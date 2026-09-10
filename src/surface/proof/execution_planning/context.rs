use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn verify_loop_execution_proofs(
    expansion_capture: Option<&mut ExpansionCapture>,
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
        expansion_capture,
        function.body(),
        vec![PlanningExecutionContext {
            state: entry_state,
            pure_facts: requirement_facts,
            surface_propositions: surface_propositions.clone(),
            recorded_snapshots: RecordedSnapshots::new(),
            case_path: Vec::new(),
            next_opaque_call: 0,
            next_kernel_variable: 0,
        }],
        &mut next_statement_index,
        &mut next_loop_index,
        &environment,
        &mut verified_loop_rules,
    )?;
    Ok(verified_loop_rules)
}

pub(in crate::surface::proof) fn explicit_loop_preservation_tactics(
    clause: &StructuralClause,
) -> Option<&[ProofTactic]> {
    let SourceProof::Script(tactics) = clause.preserve_proof()? else {
        return None;
    };
    (!tactics
        .iter()
        .all(|tactic| matches!(tactic, ProofTactic::UnfoldPredicate(_))))
    .then_some(tactics)
}

pub(in crate::surface::proof) fn kernel_loop_by_index<'a>(
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
        CStatement::Switch { cases, .. } => cases
            .iter()
            .find_map(|case| kernel_loop_by_index(&case.body, target, next_loop_index)),
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Return(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Update { .. }
        | CStatement::Assert { .. } => None,
        CStatement::ContinueWithStep { .. } => None,
    }
}

pub(in crate::surface::proof) struct ExecutionProofEnvironment<'a> {
    pub(in crate::surface::proof) initial_state: &'a CState,
    pub(in crate::surface::proof) function_block: &'a FunctionBlock,
    pub(in crate::surface::proof) parsed_function: &'a syntax::C0Function,
    pub(in crate::surface::proof) function_environment: &'a CExecutionEnvironment,
    pub(in crate::surface::proof) predicate_environment: &'a PredicateEnvironment,
    pub(in crate::surface::proof) click_function_environment: &'a ClickFunctionEnvironment,
    pub(in crate::surface::proof) resource_environment: &'a ResourceEnvironment,
    pub(in crate::surface::proof) theorem_environment: &'a TheoremEnvironment,
    pub(in crate::surface::proof) function: &'a CFunction,
    pub(in crate::surface::proof) arguments: &'a [CExpression],
    pub(in crate::surface::proof) surface_propositions: &'a SurfacePropositionMap,
    pub(in crate::surface::proof) source_layout: &'a SourceExecutionLayout,
    pub(in crate::surface::proof) frontier_loop_certificates:
        Option<&'a std::cell::RefCell<LoopProofCertificates>>,
    pub(in crate::surface::proof) frontier_loop_source: Option<&'a FrontierLoopProofSource>,
}

#[derive(Clone, Default)]
pub(in crate::surface::proof) struct LoopProofCertificates {
    pub(in crate::surface::proof) initialize: Option<ProofCertificate>,
    pub(in crate::surface::proof) preserve: Option<ProofCertificate>,
}

#[derive(Clone)]
pub(in crate::surface::proof) struct FrontierLoopProofSource {
    pub(in crate::surface::proof) proof_site: Option<ProofSite>,
    pub(in crate::surface::proof) claim_label: String,
    pub(in crate::surface::proof) loop_source_index: usize,
    pub(in crate::surface::proof) initialize_source_index: Option<usize>,
    pub(in crate::surface::proof) preserve_source_index: Option<usize>,
}

impl FrontierLoopProofSource {
    pub(in crate::surface::proof) fn new(
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
        Self {
            proof_site,
            claim_label: claim_label.to_string(),
            loop_source_index,
            initialize_source_index,
            preserve_source_index,
        }
    }
}

#[derive(Clone)]
pub(in crate::surface::proof) struct PlanningExecutionContext {
    pub(in crate::surface::proof) state: CState,
    pub(in crate::surface::proof) pure_facts: Vec<Proposition>,
    pub(in crate::surface::proof) surface_propositions: SurfacePropositionMap,
    pub(in crate::surface::proof) recorded_snapshots: RecordedSnapshots,
    pub(in crate::surface::proof) case_path: Vec<ProofCaseChoice>,
    pub(in crate::surface::proof) next_opaque_call: u64,
    pub(in crate::surface::proof) next_kernel_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) struct ProofCaseChoice {
    pub(in crate::surface::proof) condition: ClickProposition,
    pub(in crate::surface::proof) value: bool,
}

#[derive(Clone)]
pub(in crate::surface::proof) struct PathCertificate {
    pub(in crate::surface::proof) case_path: Vec<ProofCaseChoice>,
    /// For each case of `case_path`, the tactic offset in `certificate` at
    /// which the leaf took it, when leaf selection recorded every case. The
    /// merge then keeps each case at that position: the tactics before it are
    /// shared by both arms and stay before the `if`, and the tactics after it
    /// stay inside the arms. Without recorded positions a case wraps the whole
    /// certificate, which is only valid when nothing precedes it.
    pub(in crate::surface::proof) case_offsets: Option<Vec<usize>>,
    pub(in crate::surface::proof) certificate: ProofCertificate,
}

pub(in crate::surface::proof) fn merge_path_aligned_certificates(
    claim_label: &str,
    paths: Vec<PathCertificate>,
) -> Result<ProofCertificate, ClickError> {
    pub(in crate::surface::proof) fn merge(
        claim_label: &str,
        mut paths: Vec<PathCertificate>,
    ) -> Result<ProofCertificate, ClickError> {
        let first = paths.first().ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` path-aligned certificate has no paths"
            ))
        })?;
        // Equal certificates fold only when they took the same cases: a bare
        // `step()` at a C `if` reads the same on both sides of a case split
        // and is valid only inside its case, so distinct cases keep their
        // `if` even when their steps coincide.
        if paths
            .iter()
            .all(|path| path.certificate == first.certificate && path.case_path == first.case_path)
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
                if let Some(offsets) = &mut path.case_offsets
                    && !offsets.is_empty()
                {
                    offsets.remove(0);
                }
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
        // The case keeps its execution position when every path recorded it
        // at the same offset: the tactics before it are one shared prefix.
        let offset = paths
            .iter()
            .map(|path| {
                path.case_offsets
                    .as_ref()
                    .and_then(|offsets| offsets.first().copied())
            })
            .collect::<Option<Vec<usize>>>()
            .filter(|offsets| offsets.windows(2).all(|pair| pair[0] == pair[1]))
            .and_then(|offsets| offsets.first().copied());
        let mut prefix = Vec::new();
        if let Some(offset) = offset {
            let shared = paths[0]
                .certificate
                .to_proof_tactics()
                .get(..offset)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` path-aligned certificate case offset exceeds its tactics"
                    ))
                })?
                .to_vec();
            if paths.iter().any(|path| {
                path.certificate.to_proof_tactics().get(..offset) != Some(shared.as_slice())
            }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path-aligned certificates disagree before their next case `{}`",
                    describe_click_proposition(&condition)
                )));
            }
            for path in &mut paths {
                let remaining = path.certificate.to_proof_tactics()[offset..].to_vec();
                path.certificate =
                    ProofCertificate::from_proof_tactics(&remaining).map_err(|error| {
                        ClickError::new(format!(
                            "`{claim_label}` split an invalid path-aligned certificate: {error:?}"
                        ))
                    })?;
                if let Some(offsets) = &mut path.case_offsets {
                    for recorded in offsets.iter_mut() {
                        *recorded -= offset;
                    }
                }
            }
            prefix = shared;
        }
        let mut then_paths = Vec::new();
        let mut else_paths = Vec::new();
        for mut path in paths {
            let choice = path.case_path.remove(0);
            if let Some(offsets) = &mut path.case_offsets
                && !offsets.is_empty()
            {
                offsets.remove(0);
            }
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
        prefix.push(ProofTactic::If(ProofIf {
            condition,
            then_tactics: then_certificate.to_proof_tactics().to_vec(),
            else_tactics: else_certificate.to_proof_tactics().to_vec(),
        }));
        ProofCertificate::from_proof_tactics(&prefix).map_err(|error| {
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

/// The certificate offsets at which a path took its proof-level cases, as the
/// split recorded them on the checked derivation, when every case has one.
pub(in crate::surface::proof) fn recorded_case_offsets(
    presentation: &ExecutionProofPresentation,
    cases: usize,
) -> Option<Vec<usize>> {
    let choices = &presentation.surface_record.path_choices;
    (choices.len() == cases).then(|| choices.iter().map(|choice| choice.tactic_offset).collect())
}

/// Selects the leaf's own arm of every proof `if` along `case_path`, splicing
/// the arm's tactics in place. Also returns the offset of each case in the
/// selected tactics, when every case corresponds to a proof `if` (cases taken
/// at C branches without a proof `if` leave no position to record).
pub(in crate::surface::proof) fn certificate_leaf_for_case_path(
    claim_label: &str,
    tactics: &[ProofTactic],
    case_path: &[ProofCaseChoice],
) -> Result<(ProofCertificate, Option<Vec<usize>>), ClickError> {
    pub(in crate::surface::proof) fn select(
        claim_label: &str,
        tactics: &[ProofTactic],
        case_path: &[ProofCaseChoice],
        next_case: &mut usize,
        selected: &mut Vec<ProofTactic>,
        offsets: &mut Vec<usize>,
    ) -> Result<(), ClickError> {
        for tactic in tactics {
            let ProofTactic::If(proof_if) = tactic else {
                selected.push(tactic.clone());
                continue;
            };
            offsets.push(selected.len());
            let choice = case_path.get(*next_case).ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` surface certificate has more branches than its validation path"
                ))
            })?;
            if choice.condition != proof_if.condition {
                return Err(ClickError::new(format!(
                    "`{claim_label}` surface certificate branch condition does not match its validation path"
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
                offsets,
            )?;
        }
        Ok(())
    }

    let mut next_case = 0;
    let mut selected = Vec::new();
    let mut offsets = Vec::new();
    select(
        claim_label,
        tactics,
        case_path,
        &mut next_case,
        &mut selected,
        &mut offsets,
    )?;
    let certificate = ProofCertificate::from_proof_tactics(&selected).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` selected a non-surface certificate leaf: {error:?}"
        ))
    })?;
    let offsets = (offsets.len() == case_path.len()).then_some(offsets);
    Ok((certificate, offsets))
}

#[derive(Clone)]
pub(in crate::surface::proof) struct CertifiedConditionTransition {
    pub(in crate::surface::proof) is_true: bool,
    /// The kernel fact context the theorem was proved under.
    pub(in crate::surface::proof) context: PureFactContext,
    pub(in crate::surface::proof) pure_facts: Vec<Proposition>,
    pub(in crate::surface::proof) path_facts: Vec<Proposition>,
    pub(in crate::surface::proof) theorem: Theorem,
}

/// Records the planning evidence for a certified statement transition and
/// immediately constructs its surface step against the current planning state.
///
/// Fact transports that must become standalone surface steps are returned to
/// the caller instead of being constructed here: their surface form is
/// resolved against the post-statement state, which does not exist yet at this
/// call frontier.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn append_statement_transition_certificate(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    transition: &CertifiedStatementTransition,
    loop_step_policy: LoopStepPolicy,
    state: &CState,
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut construction: Option<Construction<'_>>,
) -> Vec<ConstructionEvidence> {
    let planned_transition = execution.presentation.planned_statement_transitions.len();
    let statement_operation = match loop_step_policy {
        LoopStepPolicy::EnterBody => ConstructionEvidence::CertifiedStatementStep {
            planned_transition: Some(planned_transition),
        },
        LoopStepPolicy::ApplyVerifiedRule => {
            let mut exact_premises = transition.planning_premises.clone();
            for transport in &transition.fact_transports {
                if !transport.statement_local && !exact_premises.contains(&transport.source) {
                    exact_premises.push(transport.source.clone());
                }
                for premise in &transport.frame_premises {
                    if !exact_premises.contains(premise) {
                        exact_premises.push(premise.clone());
                    }
                }
            }
            for obligation in &transition.obligations {
                if !exact_premises.contains(obligation.proposition()) {
                    exact_premises.push(obligation.proposition().clone());
                }
            }
            for fact in &transition.path_facts {
                if execution
                    .presentation
                    .surface_record
                    .certificate_facts
                    .contains(fact)
                    && !exact_premises.contains(fact)
                {
                    exact_premises.push(fact.clone());
                }
            }
            ConstructionEvidence::CertifiedLoopSummaryStep {
                prerequisite_derivations: transition.prerequisite_derivations.clone(),
                exact_premises,
                planned_transition: Some(planned_transition),
            }
        }
    };
    execution
        .presentation
        .planned_statement_transitions
        .push(PlannedStatementTransition {
            transition: transition.clone(),
            next_opaque_call: execution.core.next_opaque_call,
            next_kernel_variable: execution.core.next_kernel_variable,
        });
    if let Some(construction) = construction.as_mut() {
        let environments = construction.environments;
        construct_proof_step_for_planned_operation(
            execution,
            proof_context,
            construction.sink,
            state,
            function_block,
            parameters,
            arguments,
            environments,
            &statement_operation,
        );
        // Certificate validation carries the pre-statement facts across this
        // step, adds the transition's path facts, and rewrites
        // statement-local transports; automatic planning transports stay out
        // of the certificate-visible set.
        let certificate_facts = &mut execution.presentation.surface_record.certificate_facts;
        for fact in &transition.path_facts {
            certificate_facts.insert(fact.clone());
        }
        let local_sources = transition
            .fact_transports
            .iter()
            .filter(|transport| transport.statement_local)
            .map(|transport| &transport.source)
            .collect::<Vec<_>>();
        certificate_facts.retain(|fact| !local_sources.contains(&fact));
        for transport in transition
            .fact_transports
            .iter()
            .filter(|transport| transport.statement_local)
        {
            certificate_facts.insert(transport.target.clone());
        }
    }
    // Definedness guards are certified with the statement, so its execution
    // already carries them to their certified targets.
    // Other transported facts can still require an explicit surface bridge.
    let is_evaluator_guard = |fact: &Proposition| {
        matches!(
            fact,
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedAddOverflows(_, _)
                    | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
                    | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
                    | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
                    | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _),
                _
            )
        )
    };
    let external_transports = transition
        .fact_transports
        .iter()
        .filter(|transport| {
            !transport.statement_local
                && !is_evaluator_guard(&transport.source)
                && transport.source.clone() != transport.target.clone()
        })
        .collect::<Vec<_>>();
    let mut deferred_operations = external_transports
        .iter()
        .map(|transport| ConstructionEvidence::CertifiedFactTransport {
            source: transport.source.clone(),
            target: transport.target.clone(),
            theorem: transport.theorem.clone(),
        })
        .collect::<Vec<_>>();
    if !external_transports.is_empty() {
        deferred_operations.push(ConstructionEvidence::FinishCertifiedFactTransports(
            external_transports
                .iter()
                .map(|transport| transport.source.clone())
                .collect(),
        ));
    }
    deferred_operations
}

pub(in crate::surface::proof) fn theorem_implication_premises(
    theorem: &Theorem,
) -> Vec<Proposition> {
    let mut proposition = theorem.proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proposition {
        premises.push(premise.as_ref().clone());
        proposition = body;
    }
    premises
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn append_condition_transition_certificate(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    transition: &CertifiedConditionTransition,
    state: &CState,
    available: &[Proposition],
    function_block: &FunctionBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut construction: Option<Construction<'_>>,
) {
    let Some(construction) = construction.as_mut() else {
        return;
    };
    let environments = construction.environments;
    construct_proof_step_for_planned_operation(
        execution,
        proof_context,
        construction.sink,
        state,
        function_block,
        parameters,
        arguments,
        environments,
        &ConstructionEvidence::CertifiedStatementStep {
            planned_transition: None,
        },
    );
    // A condition step introduces evaluation guards and path facts without
    // touching memory; extend the certificate-visible set with exactly what this
    // transition adds over the planning context.
    let certificate_facts = &mut execution.presentation.surface_record.certificate_facts;
    for fact in &transition.pure_facts {
        if !available.contains(fact) {
            certificate_facts.insert(fact.clone());
        }
    }
}

pub(in crate::surface::proof) fn surface_c_condition(condition: &CExpression) -> ClickProposition {
    pub(in crate::surface::proof) fn expression(expression: &CExpression) -> ContractExpression {
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
pub(in crate::surface) enum StatementPrerequisitePolicy {
    Exact,
    Explicit,
    Contextual,
    Planning,
}

#[derive(Clone, Copy)]
pub(in crate::surface) enum StatementFactTransportPolicy {
    None,
    Automatic,
}

#[derive(Clone, Copy)]
pub(in crate::surface::proof) enum LoopStepPolicy {
    EnterBody,
    ApplyVerifiedRule,
}

#[derive(Clone, Copy)]
pub(in crate::surface::proof) enum BranchStepPolicy {
    RequireProven,
    Explore,
}

#[derive(Clone, Copy)]
pub(in crate::surface::proof) enum LoopPreservationSource {
    Automatic,
    ExecutionProof,
}
