use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn verify_loop_execution_proofs(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<CVerifiedLoopRule>, ClickError> {
    let has_structural_proofs = function_block
        .structural_clauses()
        .iter()
        .any(|clause| matches!(clause.region(), CodeRegion::Loop(_)));
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
    let source_layout = SourceExecutionLayout::new(parsed_function.body());
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
        source_layout: &source_layout,
        frontier_loop_certificates: None,
        frontier_loop_source: None,
    };
    let mut verified_loop_rules = Vec::new();
    let mut next_statement_index = 0;
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
        &mut next_statement_index,
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

pub(super) fn kernel_loop_by_index<'a>(
    statement: &'a CStatement,
    target: usize,
    next_loop_index: &mut usize,
) -> Option<&'a CStatement> {
    match statement {
        CStatement::While { body, .. } => {
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            if loop_index == target {
                Some(statement)
            } else {
                kernel_loop_by_index(body, target, next_loop_index)
            }
        }
        CStatement::Seq(first, second) => kernel_loop_by_index(first, target, next_loop_index)
            .or_else(|| kernel_loop_by_index(second, target, next_loop_index)),
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => kernel_loop_by_index(then_branch, target, next_loop_index)
            .or_else(|| kernel_loop_by_index(else_branch, target, next_loop_index)),
        CStatement::Skip
        | CStatement::Declare { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Assert { .. } => None,
    }
}

pub(super) struct ExecutionProofEnvironment<'a> {
    pub(super) initial_state: &'a CState,
    pub(super) function_block: &'a FunctionBlock,
    pub(super) parsed_function: &'a syntax::C0Function,
    pub(super) function_environment: &'a CExecutionEnvironment,
    pub(super) predicate_environment: &'a PredicateEnvironment,
    pub(super) click_function_environment: &'a ClickFunctionEnvironment,
    pub(super) resource_environment: &'a ResourceEnvironment,
    pub(super) theorem_environment: &'a TheoremEnvironment,
    pub(super) function: &'a CFunction,
    pub(super) arguments: &'a [CExpression],
    pub(super) surface_propositions: &'a SurfacePropositionMap,
    pub(super) source_layout: &'a SourceExecutionLayout,
    pub(super) frontier_loop_certificates: Option<&'a std::cell::RefCell<LoopProofCertificates>>,
    pub(super) frontier_loop_source: Option<&'a FrontierLoopProofSource>,
}

#[derive(Clone, Default)]
pub(super) struct LoopProofCertificates {
    pub(super) initialize: Option<TacticCertificate>,
    pub(super) preserve: Option<TacticCertificate>,
    pub(super) effects: BTreeMap<usize, TacticCertificate>,
}

#[derive(Clone)]
pub(super) struct FrontierLoopProofSource {
    pub(super) proof_site: Option<ProofSite>,
    pub(super) claim_label: String,
    pub(super) loop_source_index: usize,
    pub(super) initialize_source_index: Option<usize>,
    pub(super) preserve_source_index: Option<usize>,
    pub(super) effect_source_indices: BTreeMap<usize, usize>,
}

impl FrontierLoopProofSource {
    pub(super) fn new(
        clause: &StructuralClause,
        proof_site: Option<ProofSite>,
        claim_label: &str,
        loop_source_index: usize,
    ) -> Self {
        let mut next_source_index = loop_source_index + 1;
        let initialize_source_index = clause.initialize_proof().and_then(|proof| {
            let width = proof_source_tactic_count(proof);
            let start = (width != 0).then_some(next_source_index);
            next_source_index += width;
            start
        });
        let preserve_source_index = clause.preserve_proof().and_then(|proof| {
            let width = proof_source_tactic_count(proof);
            let start = (width != 0).then_some(next_source_index);
            next_source_index += width;
            start
        });
        let mut effect_source_indices = BTreeMap::new();
        for (item_index, item) in clause.items().iter().enumerate() {
            if !item.is_effect_kind() {
                continue;
            }
            let width = proof_source_tactic_count(item.proof());
            if width != 0 {
                effect_source_indices.insert(item_index, next_source_index);
            }
            next_source_index += width;
        }
        Self {
            proof_site,
            claim_label: claim_label.to_string(),
            loop_source_index,
            initialize_source_index,
            preserve_source_index,
            effect_source_indices,
        }
    }
}

#[derive(Clone)]
pub(super) struct ExecutionProofContext {
    pub(super) state: CState,
    pub(super) pure_facts: Vec<Proposition>,
    pub(super) surface_propositions: SurfacePropositionMap,
    pub(super) program_point_states: ProgramPointStates,
    pub(super) case_path: Vec<ProofCaseChoice>,
    pub(super) next_opaque_call: u64,
    pub(super) next_verification_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ProofCaseChoice {
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
}

#[derive(Clone)]
pub(super) struct PathCertificate {
    pub(super) case_path: Vec<ProofCaseChoice>,
    pub(super) certificate: TacticCertificate,
}

pub(super) fn merge_path_aligned_certificates(
    claim_label: &str,
    paths: Vec<PathCertificate>,
) -> Result<TacticCertificate, ClickError> {
    pub(super) fn merge(
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
    pub(super) fn select(
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
pub(super) struct CertifiedConditionTransition {
    pub(super) is_true: bool,
    pub(super) pure_facts: Vec<Proposition>,
    pub(super) path_facts: Vec<Proposition>,
    pub(super) theorem: Theorem,
    pub(super) prerequisite_derivations: Vec<PropositionDerivation>,
    pub(super) planning_exact_premises: Vec<Proposition>,
}

pub(super) fn append_statement_transition_certificate(
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

pub(super) fn theorem_implication_premises(theorem: &Theorem) -> Vec<Proposition> {
    let mut proposition = theorem.proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proposition {
        premises.push(premise.as_ref().clone());
        proposition = body;
    }
    premises
}

pub(super) fn append_condition_transition_certificate(
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

pub(super) fn surface_c_condition(condition: &CExpression) -> ClickProposition {
    pub(super) fn expression(expression: &CExpression) -> ContractExpression {
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
pub(in crate::lang::click) enum StatementPrerequisitePolicy {
    Exact,
    Explicit,
    Certified,
    Contextual,
    Planning,
}

#[derive(Clone, Copy)]
pub(in crate::lang::click) enum StatementFactTransportPolicy {
    None,
    Selected,
    Automatic,
}

#[derive(Clone, Copy)]
pub(super) enum LoopStepPolicy {
    EnterBody,
    ApplyVerifiedRule,
}

#[derive(Clone, Copy)]
pub(super) enum BranchStepPolicy {
    RequireProven,
    Explore,
}

#[derive(Clone, Copy)]
pub(super) enum LoopPreservationSource {
    Automatic,
    ExecutionProof,
}

pub(super) fn certified_condition_transitions(
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
                "verification time limit exceeded inside {}",
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
        || statement_consults_conditions(state, statement)
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
        statement_contains_call(statement),
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
pub(super) fn ambient_condition_facts(available: &[Proposition]) -> Vec<Proposition> {
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
fn statement_consults_conditions(state: &CState, statement: &CStatement) -> bool {
    pub(super) fn expression_consults(expression: &CExpression) -> bool {
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

pub(super) fn is_internal_snapshot_frame_witness(fact: &Proposition) -> bool {
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
                "verification time limit exceeded inside {}",
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

pub(super) fn verify_execution_proofs_forward(
    statement: &CStatement,
    contexts: Vec<ExecutionProofContext>,
    next_statement_index: &mut usize,
    next_loop_index: &mut usize,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    match statement {
        CStatement::Seq(first, second) => {
            let contexts = verify_execution_proofs_forward(
                first,
                contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            verify_execution_proofs_forward(
                second,
                contexts,
                next_statement_index,
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
            let statement_index = *next_statement_index;
            let source_region = environment
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
                    ))
                })?;
            let SourceStatementKind::If {
                then_statement_index,
                else_statement_index,
            } = source_region.kind
            else {
                return Err(ClickError::new(format!(
                    "execution proof traversal expected source statement({statement_index}) to be an `if`"
                )));
            };
            let (then_contexts, else_contexts) =
                split_execution_proof_branch_contexts(condition, contexts)?;
            *next_statement_index = then_statement_index;
            let mut joined = verify_execution_proofs_forward(
                then_branch,
                then_contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?;
            *next_statement_index = else_statement_index;
            joined.extend(verify_execution_proofs_forward(
                else_branch,
                else_contexts,
                next_statement_index,
                next_loop_index,
                environment,
                verified_loop_rules,
            )?);
            *next_statement_index = source_region.continuation_node;
            Ok(joined)
        }
        CStatement::While {
            condition,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            let statement_index = *next_statement_index;
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            let source_region = environment
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
                    ))
                })?;
            if !matches!(source_region.kind, SourceStatementKind::Loop { loop_index: found } if found == loop_index)
            {
                return Err(ClickError::new(format!(
                    "execution proof traversal source statement({statement_index}) does not match loop({loop_index})"
                )));
            }
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
                        let (preservation_tactics, first_generated_tactic_index) =
                            if let Some(tactics) = explicit_tactics {
                                (tactics.to_vec(), tactics.len())
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
                                    .filter(|tactic| {
                                        matches!(tactic, ProofTactic::UnfoldPredicate(_))
                                    })
                                    .cloned()
                                    .collect::<Vec<_>>();
                                let first_generated_tactic_index = tactics.len();
                                tactics.extend(body_certificate.tactics().iter().cloned());
                                tactics.push(ProofTactic::Simp);
                                (tactics, first_generated_tactic_index)
                            };
                        let result = verify_one_loop_preservation_proof(
                            loop_index,
                            &preservation_tactics,
                            first_generated_tactic_index,
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
                let legacy_site = ProofSite::LoopPhase {
                    function_name: environment.function_block.signature().name().to_string(),
                    loop_index,
                    phase: "initialize",
                };
                let (claim_label, site, selected_source_index) = environment
                    .frontier_loop_source
                    .map(|source| {
                        (
                            source.claim_label.clone(),
                            source
                                .proof_site
                                .clone()
                                .unwrap_or_else(|| legacy_site.clone()),
                            source.initialize_source_index,
                        )
                    })
                    .unwrap_or_else(|| (legacy_site.description(), legacy_site.clone(), Some(0)));
                let initialization_certificate = merge_path_aligned_certificates(
                    &claim_label,
                    initialization_path_certificates,
                )?;
                if let Some(certificates) = environment.frontier_loop_certificates {
                    certificates.borrow_mut().initialize = Some(initialization_certificate.clone());
                }
                if environment.frontier_loop_source.is_some() {
                    if let Some(phase_start) = selected_source_index
                        && let Some(selected) = selected_tactic_index_for_site(&site)
                        && let Some(local_index) = selected.checked_sub(phase_start)
                        // The parser keeps a single smart tactic as `Tactic`
                        // rather than wrapping it in a one-item `Script`.
                        && initialization_proof.is_some_and(|(_, proof)| match proof {
                            Proof::Tactic(SmartTactic::Simp) => local_index == 0,
                            Proof::Script(source_tactics) => {
                                selected == phase_start
                                    || matches!(
                                        source_tactics.get(local_index),
                                        Some(ProofTactic::Simp)
                                    )
                            }
                            _ => false,
                        })
                    {
                        record_proof_site_tactic_expansion(
                            &site,
                            selected,
                            initialization_certificate.tactics(),
                        );
                    }
                } else {
                    if let Some(source_index) = selected_tactic_index_for_site(&site)
                        && let Some((_, Proof::Script(source_tactics))) = initialization_proof
                        && matches!(source_tactics.get(source_index), Some(ProofTactic::Simp))
                        && !source_tactics.iter().any(|tactic| {
                            matches!(
                                tactic,
                                ProofTactic::ApplyTheorem(_)
                                    | ProofTactic::ApplyTheoremUsing { .. }
                            )
                        })
                    {
                        record_proof_site_tactic_expansion(
                            &site,
                            source_index,
                            initialization_certificate.tactics(),
                        );
                    }
                    finish_proof_site_expansion_capture(&site, &initialization_certificate)?;
                }
            }
            if !preservation_path_certificates.is_empty() {
                let claim_label = environment.frontier_loop_source.map_or_else(
                    || {
                        format!(
                            "{}.loop({loop_index}).preserve",
                            environment.function_block.signature().name()
                        )
                    },
                    |source| source.claim_label.clone(),
                );
                let preservation_certificate =
                    merge_path_aligned_certificates(&claim_label, preservation_path_certificates)?;
                if let Some(certificates) = environment.frontier_loop_certificates {
                    certificates.borrow_mut().preserve = Some(preservation_certificate.clone());
                }
                if environment.frontier_loop_source.is_none() {
                    finish_proof_site_expansion_capture(
                        &ProofSite::LoopPhase {
                            function_name: environment
                                .function_block
                                .signature()
                                .name()
                                .to_string(),
                            loop_index,
                            phase: "preserve",
                        },
                        &preservation_certificate,
                    )?;
                }
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
                if let Some(certificates) = environment.frontier_loop_certificates {
                    certificates
                        .borrow_mut()
                        .effects
                        .insert(item_index, certificate.clone());
                }
                finish_proof_site_expansion_capture(&site, &certificate)?;
            }

            *next_statement_index = source_region.continuation_node;

            advance_execution_proof_statement(
                statement,
                contexts,
                statement_index,
                Some(loop_index),
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
        CStatement::Return(_) => {
            let statement_index = *next_statement_index;
            *next_statement_index = environment
                .source_layout
                .statement(statement_index)
                .map(|region| region.continuation_node)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
                    ))
                })?;
            Ok(Vec::new())
        }
        _ => {
            let statement_index = *next_statement_index;
            *next_statement_index = environment
                .source_layout
                .statement(statement_index)
                .map(|region| region.continuation_node)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "execution proof traversal could not resolve source statement({statement_index})"
                    ))
                })?;
            advance_execution_proof_statement(
                statement,
                contexts,
                statement_index,
                None,
                environment,
                verified_loop_rules,
                LoopPreservationSource::Automatic,
                false,
            )
        }
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
    let lowered_applied_theorem_script = matches!(proof, Proof::Script(tactics)
    if tactics.iter().any(|tactic| matches!(
        tactic,
        ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. }
    ))
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        }));
    let proof = if let Proof::Script(tactics) = proof
        && tactics.iter().any(|tactic| {
            matches!(
                tactic,
                ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. }
            )
        })
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        }) {
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
        if lowered_applied_theorem_script
            && let Some(source_index) = selected_tactic_index_for_site(proof_site)
            && let Some(tactic) = certificate.tactics().get(source_index)
        {
            record_proof_site_tactic_expansion(
                proof_site,
                source_index,
                std::slice::from_ref(tactic),
            );
        }
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

fn advance_execution_proof_statement(
    statement: &CStatement,
    contexts: Vec<ExecutionProofContext>,
    statement_index: usize,
    loop_index: Option<usize>,
    environment: &ExecutionProofEnvironment<'_>,
    verified_loop_rules: &mut Vec<CVerifiedLoopRule>,
    loop_preservation_source: LoopPreservationSource,
    initialization_proven: bool,
) -> Result<Vec<ExecutionProofContext>, ClickError> {
    let mut advanced = Vec::new();
    for mut context in contexts {
        record_code_region_program_point_state(
            &mut context.program_point_states,
            environment.function_block,
            CodeRegion::Statement(statement_index),
            ProgramPointKind::Entry,
            context.state.clone(),
        );
        let label = format!("execution proof traversal at statement({statement_index})");
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
            let loop_index = loop_index.ok_or_else(|| {
                ClickError::new(format!(
                    "execution proof traversal source statement({statement_index}) is a loop without a loop index"
                ))
            })?;
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
                    "`{}` loop({loop_index}) did not produce an obligation-free verified loop rule{}",
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
            if let CStatementOutcome::Normal(exit_state)
            | CStatementOutcome::Return {
                state: exit_state, ..
            } = &transition.outcome
            {
                record_code_region_program_point_state(
                    &mut program_point_states,
                    environment.function_block,
                    CodeRegion::Statement(statement_index),
                    ProgramPointKind::Exit,
                    exit_state.clone(),
                );
            }
            if matches!(statement, CStatement::While { .. }) {
                let loop_index = loop_index.expect("a while statement has a checked loop index");
                let loop_labels = environment
                    .function_block
                    .structural_clauses()
                    .iter()
                    .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
                    .filter_map(StructuralClause::label)
                    .map(str::to_string)
                    .collect::<Vec<_>>();
                let entry_point = ProgramPointRef {
                    region: CodeRegionRef::Loop(loop_index),
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
                        region: CodeRegionRef::Loop(loop_index),
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
                        .find(|clause| clause.region() == &CodeRegion::Loop(loop_index))
                    {
                        let mut invariant_targets = transition.pure_facts.iter().filter(|fact| {
                            !context.pure_facts.contains(fact)
                                && !matches!(
                                    fact,
                                    Proposition::CMemoryEffectSummary { .. }
                                        | Proposition::CMemoryMutatesOnly { .. }
                                        | Proposition::CHeapLifetimeRetired { .. }
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
                                    "execution proof traversal loop({loop_index}) omitted an exported fact for an invariant"
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
                                "could not lower loop({loop_index}) exit condition provenance: {message}"
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
                CStatementOutcome::VerificationDiverges => {}
                CStatementOutcome::UndefinedBehavior(kind) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({statement_index}) produced undefined behavior: {kind:?}",
                        environment.function_block.signature().name()
                    )));
                }
                CStatementOutcome::RuntimeError(error) => {
                    return Err(ClickError::new(format!(
                        "execution proof traversal for {} statement({statement_index}) produced runtime error: {error:?}\navailable resources: {:?}",
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
    let legacy_site = ProofSite::LoopPhase {
        function_name: environment.function_block.signature().name().to_string(),
        loop_index,
        phase: "initialize",
    };
    let (claim_label, initialize_source_index, initialize_site) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source.claim_label.clone(),
                source
                    .initialize_source_index
                    .unwrap_or(source.loop_source_index),
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
            )
        })
        .unwrap_or_else(|| (legacy_site.description(), 0, legacy_site));
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
    // Generated initialization steps belong to the explicit phase tactic when
    // one exists, or to the enclosing `loop` keyword for an omitted phase.
    // Computing the source statement is only worth it when timings are read.
    let timings_enabled = crate::instrumentation::enabled();
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
    // Expansion lowers a shared initialize proof to optional predicate
    // unfolds followed by one explicit `have` per invariant.  Recognize that
    // surface-certificate shape on the next verification pass and replay it
    // directly.  Sending it back through the per-invariant planner would
    // treat the whole certificate as the proof of every individual `have`,
    // recursively duplicate it, and can make a valid first expansion fail.
    let source_certificate = proof.tactics().and_then(|tactics| {
        let invariant_start = tactics.len().checked_sub(invariant_items.len())?;
        let prefix_is_explicit = tactics[..invariant_start]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::UnfoldPredicate(_)));
        let invariants_match =
            tactics[invariant_start..]
                .iter()
                .zip(&invariant_items)
                .all(|(tactic, item)| {
                    matches!(
                        tactic,
                        ProofTactic::Have(have)
                            if item.proposition() == Some(&have.proposition)
                    )
                });
        (prefix_is_explicit && invariants_match)
            .then(|| TacticCertificate::from_proof_tactics(tactics).ok())
            .flatten()
    });
    let (certificate, available) = pure_goal_certificate_gateway(
        &claim_label,
        || {
            if let Some(certificate) = source_certificate {
                return Ok(certificate);
            }
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
                let plan = || {
                    plan_point_pure_goal_certificate(
                        &initialize_site,
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
                    )
                };
                let direct_plan = if environment.frontier_loop_source.is_some() {
                    // Nested frontier-loop phase tactics use absolute source
                    // indices in the enclosing proof. The per-invariant pure
                    // planner sees only the local phase script, so let the
                    // phase merger below retain the expansion at the absolute
                    // source site instead of allowing a local planner to
                    // misinterpret that index.
                    SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(|suppressed| {
                        let previous = suppressed.replace(true);
                        let result = plan();
                        suppressed.set(previous);
                        result
                    })
                } else {
                    plan()
                }?;
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
    let claim_label = environment.frontier_loop_source.map_or_else(
        || {
            format!(
                "{}.loop({loop_index}).preserve",
                environment.function_block.signature().name()
            )
        },
        |source| source.claim_label.clone(),
    );
    let sentinel = CStatement::Return(CExpression::Value(int32(0)));
    let remaining = c_seq(body.clone(), sentinel.clone());
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        proof_site: environment
            .frontier_loop_source
            .and_then(|source| source.proof_site.clone()),
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
            let (source_statement, _) =
                split_next_source_operation(remaining).map_err(ClickError::new)?;
            let CStatement::If { condition, .. } = source_statement else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` source branch does not match the lowered statement"
                )));
            };
            vec![ProofTactic::If(ProofIf {
                condition: surface_c_condition(&condition),
                then_tactics: vec![ProofTactic::SmartStep],
                else_tactics: vec![ProofTactic::SmartStep],
            })]
        } else {
            vec![ProofTactic::SmartStep]
        };
        let mut advanced = Vec::new();
        let mut errors = Vec::new();
        for tactic in candidates {
            let program = if let Some(source) = environment.frontier_loop_source {
                build_generated_certificate_proof(
                    std::slice::from_ref(&tactic),
                    &claim_label,
                    source.loop_source_index,
                )?
            } else {
                build_internal_proof(std::slice::from_ref(&tactic), &claim_label)?
            };
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
    let legacy_site = ProofSite::StructuralItem {
        function_name: environment.function_block.signature().name().to_string(),
        region: CodeRegion::Loop(loop_index),
        item_index,
        kind: item.kind(),
    };
    let (site, claim_label, effect_source_index) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
                source.claim_label.clone(),
                source
                    .effect_source_indices
                    .get(&item_index)
                    .copied()
                    .unwrap_or(source.loop_source_index),
            )
        })
        .unwrap_or_else(|| (legacy_site.clone(), legacy_site.description(), 0));
    let certificate = match item.proof() {
        Proof::Default | Proof::Tactic(SmartTactic::Auto) | Proof::Tactic(SmartTactic::Frame) => {
            TacticCertificate::from_proof_tactics(&[ProofTactic::FrameUsing {
                region: None,
                premises: Vec::new(),
            }])
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
    if environment.frontier_loop_source.is_some()
        && selected_tactic_index_for_site(&site) == Some(effect_source_index)
    {
        record_proof_site_tactic_expansion(&site, effect_source_index, certificate.tactics());
    }
    let program =
        build_internal_proof_from_source_index(certificate.tactics(), effect_source_index)?;
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
            "`{claim_label}` structural-effect certificate did not close every replay path:\n{}\n  replay paths: {}\n  closed paths: {}",
            format_tactic_certificate(&certificate),
            replayed.len(),
            replayed
                .iter()
                .filter(|context| context
                    .replay
                    .loop_effect_goal
                    .as_ref()
                    .is_some_and(|goal| goal.closed))
                .count(),
        )));
    }
    Ok(certificate)
}

pub(super) struct LoopPreservationProofResult {
    pub(super) certificate: TacticCertificate,
    pub(super) effect_certificates: Vec<(usize, TacticCertificate)>,
}

#[allow(clippy::too_many_arguments)]
fn verify_one_loop_preservation_proof(
    loop_index: usize,
    tactics: &[ProofTactic],
    first_generated_tactic_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<LoopPreservationProofResult, ClickError> {
    let legacy_site = ProofSite::LoopPhase {
        function_name: environment.function_block.signature().name().to_string(),
        loop_index,
        phase: "preserve",
    };
    let (claim_label, preserve_source_index, preserve_site) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source.claim_label.clone(),
                source
                    .preserve_source_index
                    .unwrap_or(source.loop_source_index),
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
            )
        })
        .unwrap_or_else(|| (legacy_site.description(), 0, legacy_site));

    let proof_claims = [];
    // Positive closer results from the planner half, keyed by the certificate
    // path that produced them. Replay starts from the same loop-entry context
    // and checks every deterministic leaf tactic, so reaching the same case
    // path reproduces the closer inputs without an expensive deep comparison
    // of snapshot-rich states and proposition sets.
    let mut verified_closer_paths: Vec<Vec<ProofCaseChoice>> = Vec::new();
    let mut program = if environment
        .frontier_loop_source
        .is_some_and(|source| source.preserve_source_index.is_none())
    {
        build_generated_certificate_proof(tactics, &claim_label, preserve_source_index)?
    } else {
        build_internal_proof_from_source_index(tactics, preserve_source_index)?
    };
    if first_generated_tactic_index < tactics.len() {
        // Automatic preservation appends planned body steps and a closer
        // after the source-spelled unfold prefix. They are owned by the loop
        // tactic, not additional source occurrences after `preserve`.
        // Detach them so a later nested clause (notably `immutable by frame`)
        // cannot be mistaken for one of these generated tactics by expand.
        detach_generated_suffix_from_source_indices(&mut program, first_generated_tactic_index);
    }
    let sentinel = CStatement::Return(CExpression::Value(int32(0)));
    let remaining = c_seq(body.clone(), sentinel.clone());
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let mut replay = TacticReplayState {
        proof_site: Some(preserve_site),
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
        let case_path = context
            .replay
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
            })
            .collect::<Vec<_>>();
        let (closer_index, closer_source, closer_name, closer_class) =
            if let Some((tactic_index, source_index)) = context.replay.region_simp {
                (tactic_index, source_index, "simp", "smart")
            } else {
                (tactics.len(), tactics.len(), "assumption", "simple")
            };
        let _timing = crate::instrumentation::enabled().then(|| {
            if crate::instrumentation::starts_enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(
                        crate::instrumentation::TacticEvent {
                            claim: claim_label.clone(),
                            tactic_index: closer_index,
                            tactic_name: closer_name.to_string(),
                            class: closer_class.to_string(),
                            statement_index: context.replay.frontier.next_statement_index,
                            source_index: closer_source,
                        },
                    ),
                );
            }
            let timing_context = TimingTacticContext {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class.to_string(),
                statement_index: context.replay.frontier.next_statement_index,
            };
            push_timing_tactic(timing_context.clone());
            TacticTiming {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class,
                statement_index: context.replay.frontier.next_statement_index,
                start: std::time::Instant::now(),
                context: timing_context,
            }
        });
        let closer_tactics = if invariant_checks.is_empty()
            || context.replay.region_invariants_closed
        {
            Vec::new()
        } else {
            let mut closer_facts = context.pure_facts.clone();
            closer_facts.extend(
                context
                    .replay
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            closer_facts.extend(crate::kernel::certified_store_equations(
                &context.replay.effect_facts,
            ));
            if let Err(message) = c_loop_invariants_hold_at_back_edge_using(
                &context.state,
                preservation.loop_entry_state(),
                invariant_checks,
                &assumptions_from_propositions(&closer_facts),
            ) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} invariant bundle preservation) could not certify every guarded invariant-lowering path: {message}"
                )));
            }
            verified_closer_paths.push(case_path.clone());
            vec![ProofTactic::CloseInvariants]
        };
        let omitted_frontier_preservation = environment
            .frontier_loop_source
            .is_some_and(|source| source.preserve_source_index.is_none());
        if !omitted_frontier_preservation
            && context.replay.region_simp.is_some_and(|(_, source_index)| {
                tactic_expansion_capture_matches(context.replay.proof_site.as_ref(), source_index)
            })
        {
            let capture = SurfaceReplay {
                tactics: closer_tactics.clone(),
                ..SurfaceReplay::default()
            };
            return Err(finish_tactic_expansion_capture(&capture, false));
        }
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
    // This is a detached, deterministic replay of the certificate just
    // produced above. Its local tactic indices start at zero and are not
    // source occurrences in the enclosing proof. Letting the expansion probe
    // observe them can make (for example) certificate tactic 1 overwrite the
    // expansion selected for enclosing source tactic 1.
    let replayed = SUPPRESS_TACTIC_EXPANSION_CAPTURE
        .with(|suppressed| {
            let previous = suppressed.replace(true);
            let result = execute_internal_proof(
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
            );
            suppressed.set(previous);
            result
        })
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
        if context.replay.region_invariants_closed == invariant_checks.is_empty() {
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
            let case_path = context
                .replay
                .case_assumptions
                .iter()
                .map(|choice| ProofCaseChoice {
                    condition: choice.condition.clone(),
                    value: choice.value,
                })
                .collect::<Vec<_>>();
            let planner_already_verified = std::env::var_os("CLICK_DISABLE_CLOSER_REUSE").is_none()
                && verified_closer_paths.contains(&case_path);
            if !planner_already_verified {
                let mut closer_facts = context.pure_facts.clone();
                closer_facts.extend(
                    context
                        .replay
                        .effect_facts
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                closer_facts.extend(crate::kernel::certified_store_equations(
                    &context.replay.effect_facts,
                ));
                c_loop_invariants_hold_at_back_edge_using(
                    &context.state,
                    preservation.loop_entry_state(),
                    invariant_checks,
                    &assumptions_from_propositions(&closer_facts),
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
