use super::proof_object::ProofCheckpoint;
use super::*;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use std::sync::Arc;

/// The parent proof operation, before registration or termination planning.
/// Omitted proofs have already run through the same ordinary child scopes.
pub(in crate::surface) fn finish_contract_body_root(
    function: &FunctionBlock,
    theorems: &[VerifiedProgramTheorem],
) -> Result<Arc<crate::kernel::ContractBodyProof>, ClickError> {
    let entry = theorems
        .iter()
        .find_map(|theorem| theorem.entry_context.as_ref())
        .ok_or_else(|| {
            ClickError::new(format!(
                "function proof for `{}` did not retain its contract root",
                function.signature().name()
            ))
        })?;
    let root = entry.completion.as_ref().ok_or_else(|| {
        ClickError::new(format!(
            "ordinary function proof for `{}` lost its contract root",
            function.signature().name()
        ))
    })?;
    root.finish().map_err(|goal| {
        let missing = match goal {
            crate::kernel::ContractCompletionGoal::Boundary { case } => {
                format!("closing obligations for entry case {case}")
            }
            crate::kernel::ContractCompletionGoal::RecursiveDescent { case } => {
                format!("recursive descent for entry case {case}")
            }
            crate::kernel::ContractCompletionGoal::Claim { case, key } => format!(
                "{} in entry case {case}",
                crate::surface::diagnostics::describe_unverified_contract_claims(function, &[key])
            ),
        };
        ClickError::new(format!(
            "contract proof for `{}` still owes {missing}",
            function.signature().name()
        ))
        .at_declaration(function.signature().name())
    })
}

/// Input retained across ordinary closing steps. Return rewrites are resolved
/// once before the first step, and the same path identity reaches registration.
struct ContractClosingInput {
    path: crate::kernel::SymbolicExecutionPath,
    specification: Arc<crate::kernel::PublishedFunctionOutcome>,
}

// Entry runs before the proof starts. Preserve typed refusals from the
// producers above it and report an unexplained setup failure as a Click defect.
fn classify_contract_entry_error(error: ClickError) -> ClickError {
    if error.kind() == ClickErrorKind::Proof && error.proof_refusal().is_none() {
        error.with_kind(ClickErrorKind::Internal)
    } else {
        error
    }
}

fn contract_closing_input(
    root: Option<&Proof<'_>>,
    execution: &CheckedFunctionExecution,
    path_index: usize,
    has_return_resource_rewrite: bool,
    post_return_facts: &[(usize, PureFactStore)],
) -> Result<ContractClosingInput, ClickError> {
    let returned = if has_return_resource_rewrite {
        let root = root.ok_or_else(|| {
            ClickError::new("return instance fold lost its outcome proof")
                .with_kind(ClickErrorKind::Internal)
        })?;
        let core = &root
            .execution()
            .ok_or_else(|| {
                ClickError::new("return instance fold lost its checked execution")
                    .with_kind(ClickErrorKind::Internal)
            })?
            .core;
        Some(core.checked_return_path(path_index).map_err(|refusal| {
            let message = format!("could not certify return instance fold: {}", refusal.reason);
            match refusal.unjustified_fact {
                Some(fact) => unjustified_return_fact_error(
                    root,
                    post_return_facts,
                    &fact,
                    &message,
                    path_index,
                ),
                None => ClickError::new(message),
            }
        })?)
    } else {
        None
    };
    let path = match &returned {
        Some(returned) => returned.path(),
        None => execution.paths().get(path_index).ok_or_else(|| {
            ClickError::new("return instance fold changed execution path coverage")
                .with_kind(ClickErrorKind::Internal)
        })?,
    }
    .clone();
    let specification = returned.as_ref().map_or_else(
        || execution.published_outcome(path_index).clone(),
        |returned| returned.publication().clone(),
    );
    Ok(ContractClosingInput {
        path,
        specification,
    })
}

#[derive(Clone, Copy)]
enum ClosingProofMode {
    Explicit,
    Implicit,
}

fn prove_next_contract_closing_goal<'a>(
    outcome_proof: &mut Option<Proof<'a>>,
    input: &mut Option<ContractClosingInput>,
    execution: &CheckedFunctionExecution,
    path_index: usize,
    has_return_resource_rewrite: bool,
    post_return_facts: &[(usize, PureFactStore)],
    mode: ClosingProofMode,
) -> Result<bool, ClickError> {
    let Some(root) = outcome_proof.as_ref() else {
        return Ok(false);
    };
    let Some(crate::kernel::proof::OutcomeGoal::Closing(kind)) = root.first_open_outcome_goal()?
    else {
        return Ok(false);
    };
    let _origin = matches!(mode, ClosingProofMode::Implicit)
        .then(|| crate::surface::proof_trace::TraceOrigin::enter_implicit("contract closing"));
    if input.is_none() {
        *input = Some(contract_closing_input(
            Some(root),
            execution,
            path_index,
            has_return_resource_rewrite,
            post_return_facts,
        )?);
    }
    let input = input.as_ref().expect("prepared closing input");
    let proved = root.prove_contract_closing_goal(kind, execution, &input.path, &input.specification)
        .map_err(|error| match mode {
            _ if error.kind() == ClickErrorKind::Internal
                || error.proof_refusal() == Some(crate::surface::ProofRefusal::IncompleteProof) => error,
            ClosingProofMode::Explicit => error.with_context(format!("this tactic could not prove the {} obligation while closing the contract", kind.description())),
            ClosingProofMode::Implicit => error.with_context(format!("the implicit solver could not prove the {} obligation while closing the contract; write an explicit proof or establish the required facts and resources before closing", kind.description())),
        })?;
    check_verification_deadline()?;
    *outcome_proof = Some(proved);
    Ok(true)
}

#[cfg(test)]
thread_local! {
    static FLAT_PROOF_UNITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(in crate::surface) fn count_flat_proof_units<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let before = FLAT_PROOF_UNITS.with(std::cell::Cell::get);
    let result = operation();
    let after = FLAT_PROOF_UNITS.with(std::cell::Cell::get);
    (result, after - before)
}

pub(in crate::surface) struct ClaimProofResult {
    pub(in crate::surface) theorems: Vec<VerifiedProgramTheorem>,
}

/// A deferred tactic still to visit, or the end of a selected proof arm.
enum PendingPostExecutionTactic<'a> {
    Tactic(
        &'a DeferredPostExecutionTactic,
        usize,
        Option<PersistentBinderMap<ContractExpression>>,
    ),
    EndIfArm {
        choice: usize,
        obtains_before_arm: usize,
    },
}

/// The end of the written block containing each obtain, using the same
/// source positions as the deferred program. Nested proposition proofs
/// are checked separately and use their own locals.
fn obtain_scope_ends(tactics: &[ProofTactic]) -> BTreeMap<usize, usize> {
    fn visit(
        tactics: &[ProofTactic],
        position: &mut usize,
        ends: &mut BTreeMap<usize, usize>,
        outermost: bool,
    ) {
        let mut obtains = Vec::new();
        for tactic in tactics {
            if matches!(tactic, ProofTactic::Synthetic(_)) {
                continue;
            }
            if matches!(tactic, ProofTactic::LetSatisfy(_)) {
                obtains.push(*position);
            }
            *position += 1;
            if matches!(
                tactic,
                ProofTactic::Open(_)
                    | ProofTactic::If(_)
                    | ProofTactic::Cases(_)
                    | ProofTactic::Branch(_)
                    | ProofTactic::CallOutcomes(_)
                    | ProofTactic::Match(_)
                    | ProofTactic::Loop(_)
            ) {
                for child in tactic.children() {
                    match child {
                        TacticChild::Continuing(ChildProof::Script(body)) => {
                            visit(body, position, ends, false);
                        }
                        TacticChild::Continuing(ChildProof::Source(SourceProof::Script(body))) => {
                            visit(body, position, ends, false);
                        }
                        TacticChild::Continuing(ChildProof::Source(SourceProof::Tactic(_))) => {
                            *position += 1;
                        }
                        _ => {}
                    }
                }
            }
        }
        let end = if outermost { usize::MAX } else { *position };
        ends.extend(obtains.into_iter().map(|start| (start, end)));
    }

    let mut ends = BTreeMap::new();
    visit(tactics, &mut 0, &mut ends, true);
    ends
}

/// Source scopes contain the lexical snapshots recorded during execution.
/// An ambient obtain adds checked bindings during finalization, so those
/// outputs also have to survive until their source block ends.
#[derive(Default)]
struct DeferredOutcomeLocals {
    source: Option<PersistentBinderMap<ContractExpression>>,
    obtained: PersistentBinderMap<ContractExpression>,
    ends: BTreeMap<usize, Vec<String>>,
    checked_obtains: usize,
}

impl DeferredOutcomeLocals {
    fn enter<'a>(
        &mut self,
        proof: &mut Option<Proof<'a>>,
        source_index: usize,
        scope: Option<&PersistentBinderMap<ContractExpression>>,
    ) {
        let Some(root) = proof.as_ref() else { return };
        let mut expired = Vec::new();
        if source_index < SYNTHETIC_SOURCE_INDEX_BASE {
            while self
                .ends
                .first_key_value()
                .is_some_and(|(end, _)| *end <= source_index)
            {
                let (_, names) = self.ends.pop_first().expect("scope end was just inspected");
                for name in &names {
                    self.obtained.remove(name);
                }
                expired.extend(names);
            }
        }
        if self.ends.is_empty() && expired.is_empty() {
            if let Some(scope) = scope {
                *proof = Some(root.with_surface_local_scope(scope));
            }
        } else {
            *proof = Some(root.update_deferred_outcome_locals(
                self.source.as_ref(),
                scope,
                &self.obtained,
                &expired,
            ));
        }
        if let Some(scope) = scope {
            self.source = Some(scope.clone());
        }
    }

    fn record(
        &mut self,
        before: &Proof<'_>,
        after: &Proof<'_>,
        binding: &ProofLetSatisfy,
        end: usize,
    ) {
        if self.source.is_none() {
            self.source = Some(before.surface_local_scope());
        }
        let names = self.ends.entry(end).or_default();
        for (name, _) in &binding.bindings {
            if let Some(value) = after.local_binding(name) {
                self.obtained.insert(name.clone(), value.clone());
            }
            names.push(name.clone());
        }
    }
}

/// Visit one leaf at a time so each control node sees the checked facts left
/// by all preceding leaves. `call_depth` follows nested `outcomes` arms only;
/// sibling controls in the continuation keep their enclosing depth.
fn next_checked_post_execution_tactic<'a>(
    proof: &mut Option<Proof<'_>>,
    pending: &mut Vec<PendingPostExecutionTactic<'a>>,
    locals: &mut DeferredOutcomeLocals,
    choices: &mut Vec<SurfacePathChoice>,
    surface_tactics: &mut Vec<ProofTactic>,
    path_index: usize,
) -> Result<Option<&'a DeferredPostExecutionTactic>, ClickError> {
    while let Some(pending_tactic) = pending.pop() {
        let (deferred, call_depth, arm_scope) = match pending_tactic {
            PendingPostExecutionTactic::Tactic(deferred, call_depth, arm_scope) => {
                (deferred, call_depth, arm_scope)
            }
            PendingPostExecutionTactic::EndIfArm {
                choice,
                obtains_before_arm,
            } => {
                let arm_end = SurfaceIfArmEnd {
                    step_offset: surface_tactics.len(),
                    nested_choices: choices.len() - choice - 1,
                    binds_obtain: locals.checked_obtains != obtains_before_arm,
                };
                choices[choice].if_arm_end = Some(arm_end);
                continue;
            }
        };
        // A deferred `match` takes the arm this path's constructor case
        // selected, under that arm's field bindings.
        if let PostExecutionTactic::Match { source, arms } = &deferred.tactic {
            let proof = proof.as_ref().ok_or_else(|| {
                ClickError::new("post-execution `match` has no focused outcome Proof")
            })?;
            let (arm, bindings) = proof
                .clone()
                .at_source_tactic(deferred.source_index)
                .checked_outcome_match_arm(deferred.source_index)
                .map_err(|error| error.with_context(format!("post-execution path {path_index}")))?;
            choices.push(SurfacePathChoice {
                occurrence: deferred.source_index,
                selector: SurfacePathSelector::MatchArm(Arc::clone(source), arm),
                value: true,
                tactic_offset: surface_tactics.len(),
                if_arm_end: None,
            });
            let tactics = arms.get(arm).ok_or_else(|| {
                ClickError::new("a post-execution `match` path names an arm it does not have")
            })?;
            pending.extend(tactics.iter().rev().map(|tactic| {
                PendingPostExecutionTactic::Tactic(tactic, call_depth, Some(bindings.clone()))
            }));
            continue;
        }
        let mut scope = deferred
            .lexical_bindings
            .clone()
            .or_else(|| arm_scope.clone());
        let (selector, value, arm, child_depth) = match &deferred.tactic {
            PostExecutionTactic::If {
                condition,
                disjunction,
                execution_route,
                then_tactics,
                else_tactics,
            } => {
                let has_obtains = !locals.ends.is_empty();
                if has_obtains {
                    locals.enter(proof, deferred.source_index, scope.as_ref());
                }
                let mut scoped = proof
                    .as_ref()
                    .ok_or_else(|| {
                        ClickError::new("post-execution `if` has no focused outcome Proof")
                    })?
                    .clone()
                    .at_source_tactic(deferred.source_index);
                if !has_obtains && let Some(bindings) = &scope {
                    scoped = scoped.with_surface_local_scope(bindings);
                }
                if *disjunction
                    && let Some(have) = scoped
                        .focused_outcome_data()
                        .and_then(|data| data.case_obligations.get(&deferred.source_index))
                {
                    // Already proved before partitioning, with neither arm
                    // assumed. Retain its source without checking it again.
                    surface_tactics.extend(have.to_proof_tactics());
                }
                let value = if *disjunction {
                    scoped.checked_outcome_cases_value(condition, *execution_route)
                } else if deferred.reads_deferred_obtain {
                    scoped.decide_outcome_if_from_facts(condition)
                } else {
                    scoped.checked_outcome_if_value(condition, *execution_route)
                }
                .map_err(|error| error.with_context(format!("post-execution path {path_index}")))?;
                (
                    if *disjunction {
                        SurfacePathSelector::Disjunction(condition.clone())
                    } else {
                        SurfacePathSelector::Proposition(condition.clone())
                    },
                    value,
                    if value { then_tactics } else { else_tactics },
                    call_depth,
                )
            }
            PostExecutionTactic::CallOutcomes {
                payload_bindings,
                returned_tactics,
                threw_tactics,
            } => {
                let proof = proof.as_ref().ok_or_else(|| {
                    ClickError::new("post-execution `outcomes` has no focused outcome Proof")
                })?;
                let focused = proof.clone().at_source_tactic(deferred.source_index);
                let edge = focused.checked_call_outcome(call_depth)?;
                let returned = edge.returned;
                if let Some(name) = &payload_bindings[usize::from(!returned)] {
                    let payload = edge.payload.clone().ok_or_else(|| {
                        focused.step_error(format!(
                            "`outcomes` cannot bind `{name}`: this call edge has no bindable payload"
                        ))
                    })?;
                    scope = Some(focused.scope_call_payload(
                        scope.as_ref().or({
                            if locals.ends.is_empty() {
                                None
                            } else {
                                locals.source.as_ref()
                            }
                        }),
                        name,
                        payload,
                    ));
                }
                (
                    SurfacePathSelector::CallOutcome(payload_bindings.clone()),
                    returned,
                    if returned {
                        returned_tactics
                    } else {
                        threw_tactics
                    },
                    call_depth + 1,
                )
            }
            _ => {
                locals.enter(proof, deferred.source_index, scope.as_ref());
                return Ok(Some(deferred));
            }
        };
        if matches!(selector, SurfacePathSelector::Proposition(_)) {
            pending.push(PendingPostExecutionTactic::EndIfArm {
                choice: choices.len(),
                obtains_before_arm: locals.checked_obtains,
            });
        }
        choices.push(SurfacePathChoice {
            occurrence: deferred.source_index,
            selector,
            value,
            tactic_offset: surface_tactics.len(),
            if_arm_end: None,
        });
        pending.extend(
            arm.iter().rev().map(|tactic| {
                PendingPostExecutionTactic::Tactic(tactic, child_depth, scope.clone())
            }),
        );
    }
    Ok(None)
}

/// Serialize deferred proof cases at their checked operation offsets. Their
/// outcome paths need not have branches in the earlier C execution prefix.
fn synthesize_post_execution_paths(
    tactics: &[Vec<ProofTactic>],
    closers: &[Vec<ProofTactic>],
    choices: &[Vec<SurfacePathChoice>],
    boolean_returns: &[Option<bool>],
) -> Result<Vec<ProofStep>, String> {
    let paths = tactics
        .iter()
        .zip(closers)
        .zip(choices)
        .map(|((tactics, closers), choices)| {
            let mut steps = ProofCertificate::from_proof_tactics(tactics)
                .map_err(|error| format!("post-execution path is not simple: {error}"))?
                .into_steps();
            steps.extend(
                ProofCertificate::from_proof_tactics(closers)
                    .map_err(|error| format!("post-execution closer is not simple: {error}"))?
                    .into_steps(),
            );
            Ok(ProofCertificateBuilder {
                steps,
                path_choices: choices.clone(),
                ..ProofCertificateBuilder::default()
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    synthesize_surface_alternatives_with_returns(paths, boolean_returns)
}

fn checked_boolean_return(outcome: &FunctionOutcome) -> Option<bool> {
    let FunctionOutcome::Return { value, .. } = outcome else {
        return None;
    };
    match &**value {
        crate::kernel::ExecutionValue::Native(ProgramValue::Bool(word)) => {
            word.bool_constant_value()
        }
        crate::kernel::ExecutionValue::Shared(term) => match term.node() {
            crate::kernel::KernelTermNode::BoolLiteral(result) => Some(*result),
            _ => None,
        },
        _ => None,
    }
}

/// Serialize deferred proof cases separately inside each leaf of the retained
/// C-execution surface. A proof-level case split applies after execution, so
/// two outcomes that take one proof arm from different C branches may need
/// different closers; the C branch already separates them, and no proof-level
/// condition exists to split them again. Each leaf receives the proof cases
/// synthesized from exactly the outcomes that reach it.
fn append_post_execution_paths_by_surface_leaf(
    steps: &mut Vec<ProofStep>,
    tactics: &[Vec<ProofTactic>],
    closers: &[Vec<ProofTactic>],
    choices: &[Vec<SurfacePathChoice>],
    mut branch_path: impl FnMut(usize) -> Option<Vec<bool>>,
    boolean_return: impl Fn(usize) -> Option<bool>,
) -> Result<(), String> {
    let mut groups = std::collections::BTreeMap::<Vec<bool>, Vec<usize>>::new();
    for index in 0..tactics.len() {
        let branch_path = branch_path(index)
            .ok_or_else(|| "an outcome has no retained surface branch path".to_string())?;
        groups.entry(branch_path).or_default().push(index);
    }
    fn select<T: Clone>(source: &[T], members: &[usize]) -> Vec<T> {
        members.iter().map(|index| source[*index].clone()).collect()
    }
    for (branch_path, members) in groups {
        let returns = members
            .iter()
            .map(|&index| boolean_return(index))
            .collect::<Vec<_>>();
        let choices = select(choices, &members);
        let keep_scopes = outcome_paths_bind_obtain(&choices);
        let suffix = synthesize_post_execution_paths(
            &select(tactics, &members),
            &select(closers, &members),
            &choices,
            &returns,
        )?;
        append_surface_steps_at_step_branch_path(steps, &branch_path, suffix, keep_scopes)?;
    }
    Ok(())
}

fn outcome_paths_bind_obtain(choices: &[Vec<SurfacePathChoice>]) -> bool {
    choices
        .iter()
        .flatten()
        .any(|choice| choice.if_arm_end.is_some_and(|end| end.binds_obtain))
}

fn diagnostic_claim_label(function_block: &FunctionBlock, claim: &FunctionClaimRef<'_>) -> String {
    let label = function_claim_label(function_block, claim);
    format!("{label}: {}", diagnostic_claim_statement(claim))
}

fn diagnostic_claim_statement(claim: &FunctionClaimRef<'_>) -> String {
    match claim.clause().ensure() {
        Ensure::Resource(resource) => {
            crate::surface::validation::describe_resource_clause(resource)
        }
        Ensure::Proposition(proposition) => {
            crate::surface::diagnostics::describe_click_proposition(proposition)
        }
    }
}

/// The terminal diagnostic when all checked drivers declined.
fn checked_driver_refusal(
    proof_label: &str,
    claim_labels: &[String],
    decline: Decline,
) -> ClickError {
    if decline == Decline::RegionDepth {
        return ClickError::new(format!(
            "`{proof_label}`: checked execution-region recursion exceeds the supported depth of {MAX_CHECKED_PROOF_REGION_RECURSION}. This bound counts active recursive regions, not written proof nesting; completed early-return cases run iteratively. Move an inner `match`, `branch`, or proof `if` into a contracted helper, or prove part of it in a `have`."
        )).with_kind(ClickErrorKind::Unsupported);
    }
    if decline == Decline::ShortOfExit {
        // The written shape is supported; what stopped the drivers is a path
        // the proof left open. Say which, rather than calling the shape
        // unimplemented, since the fix is in the proof script.
        return ClickError::new(format!(
            "`{proof_label}`: a `branch` or proof `if` split the path, one arm returned, and the tactics after the split ran out before the continuing arm reached the function exit, so that path is still open. The proof after the split runs inside the continuing arm; finish it there (for example with `step_until(function.exit);`), or check the continuation's last tactics."
        )).with_proof_refusal(crate::surface::ProofRefusal::IncompleteProof);
    }
    let claim_description = if claim_labels.len() == 1 {
        format!("the contract claim `{}`", claim_labels[0])
    } else {
        let labels = claim_labels
            .iter()
            .map(|label| format!("`{label}`"))
            .collect::<Vec<_>>()
            .join(", ");
        format!("these {} contract claims: {labels}", claim_labels.len())
    };
    ClickError::new(format!(
        "`{proof_label}`: no checked proof driver accepts this proof script's shape for {claim_description}, and none reported a tactic it refused. Click could not identify why verification stopped."
    )).with_kind(ClickErrorKind::Internal)
}

pub(in crate::surface) fn prove_claim_by_tactics(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<ClaimProofResult, ClickError> {
    if tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty explicit proof script"
        )));
    }
    if crate::surface::sorry_outside_have_bodies(tactics) {
        return Err(ClickError::new(format!(
            "`{claim_label}` uses `sorry` outside a `have` body; `sorry` is only allowed as a complete contract proof body or a complete `have` body"
        )));
    }
    prove_claims_by_checked_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        std::slice::from_ref(claim),
        claim_label,
        false,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        tactics,
        tactic_source,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn prove_claims_by_grouped_tactics(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<ClaimProofResult, ClickError> {
    let proof_label = function_block.contract_claim_label();
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
    if crate::surface::sorry_outside_have_bodies(tactics) {
        return Err(ClickError::new(format!(
            "`{proof_label}` uses `sorry` outside a `have` body; `sorry` is only allowed as a complete contract proof body or a complete `have` body"
        )));
    }
    prove_claims_by_checked_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claims,
        &proof_label,
        true,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        tactics,
        tactic_source,
    )
}

/// The proof route shared by single-claim and grouped contract proofs: the
/// claims the script must establish, the label its diagnostics use, and
/// whether the script proves the contract as one group.
#[allow(clippy::too_many_arguments)]
fn prove_claims_by_checked_tactics(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claims: &[FunctionClaimRef<'_>],
    proof_label: &str,
    grouped: bool,
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<ClaimProofResult, ClickError> {
    let _automation_scope = super::implicit_solve_scope::ClaimScope::enter(proof_label);
    let _local_layouts =
        super::surface_synthesis::LocalStructLayoutScope::enter(parsed_function, function_block);
    let program = build_internal_proof_with_source(tactics, proof_label, tactic_source)?;
    let generated_by_source_index = match tactic_source {
        ProofTacticSource::SourceSyntax => None,
        ProofTacticSource::GeneratedBy { source_index } => Some(source_index),
    };
    let caller_source_owner =
        CallerSourceOwnerId::ordinary(source_path, function_block.signature().name());
    let InitialClaimContext {
        opened_entry: shared_entry,
        state,
        arguments,
        pure_facts,
        entry_fact_origins,
        mut surface_propositions,
        entry_separation_sources,
    } = function_source_registry
        .claim_entries()
        .get_or_build(source_path, function_block, || {
            initial_claim_context_with_caller_owner(
                function_block,
                parsed_function,
                resource_environment,
                spec_definitions,
                proof_label,
                Some(&caller_source_owner),
            )
        })
        .map_err(|error| {
            classify_contract_entry_error(error.at_declaration(function_block.signature().name()))
        })?;
    // A shared context was built for an earlier claim; name this function's
    // parameters for diagnostics as building it would have.
    crate::surface::proof_diagnostics::render::enter_ambient_naming(
        ParameterBinding::new(parsed_function.parameters(), &arguments),
        &state,
    );
    crate::surface::diagnostics::enter_ambient_object_fields(parsed_function);
    let opened_entry = shared_entry
        .get_or_open(|| {
            let function = annotated_function_with_assumptions(
                function_block,
                parsed_function,
                &state,
                &arguments,
                spec_definitions,
                resource_environment,
                Some(ResourceFrameEntry {
                    assumptions: &assumptions_from_propositions(&pure_facts),
                    checked_entry_state: None,
                }),
                None,
            )?;
            let state = canonical_claim_caller_state(
                state,
                function_block.structural_clauses().any_loop(),
                &function,
                &arguments,
                &pure_facts,
                proof_label,
            )?;
            let state = install_borrowed_contract_inputs(
                state,
                &function,
                &pure_facts,
                ParameterBinding::new(parsed_function.parameters(), &arguments),
                proof_label,
            )?;
            let entry = crate::kernel::proof::OpenedContractEntry::open(
                &state,
                &function,
                &arguments,
                &pure_facts,
                function_environment,
            )
            .map_err(|error| {
                let diagnostic = ClickError::new(format!(
                    "could not open contract entry for `{proof_label}`: {}",
                    crate::surface::diagnostics::describe_runtime_error(
                        &error,
                        ParameterBinding::new(parsed_function.parameters(), &arguments),
                    ),
                ));
                contract_entry_runtime_refusal(diagnostic, &error)
            })?;
            entry
                .open_contract_root(function_source_registry.program())
                .map_err(|message| {
                    ClickError::new(format!(
                        "could not initialize the contract proof for `{proof_label}`: {message}"
                    ))
                    .with_kind(ClickErrorKind::Internal)
                })
        })
        .map_err(classify_contract_entry_error)?;
    // Every clause uses the function produced by this generative entry.
    // Re-lowering a sibling clause can allocate different binder identities.
    let function = opened_entry.function().clone();
    let state = opened_entry.caller_state().clone();
    let function_entry_state = opened_entry.entry_state().clone();
    let entry_fact_origins = opened_entry
        .source_origins()
        .iter()
        .map(|origin| match origin {
            Some(crate::kernel::proof::OpenedEntryFactSource::SourceFact(index)) => {
                entry_fact_origins[*index].clone()
            }
            Some(crate::kernel::proof::OpenedEntryFactSource::Requirement(outer_ordinal)) => {
                EntryFactOrigin::Requirement {
                    source_id: RequirementSourceId {
                        owner: caller_source_owner.clone(),
                        outer_ordinal: *outer_ordinal,
                    },
                    role: RequirementFactRole::Principal {
                        unfolding_path: Vec::new(),
                    },
                }
            }
            None => EntryFactOrigin::Derived,
        })
        .collect::<Vec<_>>();
    let pure_facts = PureFactList::from_store(opened_entry.facts());
    let caller_requirement_index = CallerRequirementIndex::from_entry_facts_elaborated(
        caller_source_owner.clone(),
        function_block,
        parsed_function.parameters(),
        &pure_facts,
        &entry_fact_origins,
        crate::kernel::MemoryStateIdentity::of(state.memory()),
        Some(spec_definitions.predicates),
    );
    // Entry opening owns the final resource-count lineage and source facts.
    // Retain those products directly rather than their pre-opening identities.
    for (fact, origin) in pure_facts.iter().zip(&entry_fact_origins) {
        let EntryFactOrigin::Requirement {
            source_id,
            role: RequirementFactRole::Principal { unfolding_path },
        } = origin
        else {
            continue;
        };
        if !unfolding_path.is_empty() {
            continue;
        }
        let Some(Requirement::Proposition(surface)) =
            function_block.requires().get(source_id.outer_ordinal)
        else {
            continue;
        };
        surface_propositions.record_lowering(surface, fact)?;
        surface_propositions.record_lowering(
            &ClickProposition::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                proposition: Box::new(surface.clone()),
            },
            fact,
        )?;
    }
    let completion = opened_entry.contract_root().cloned();
    let root_attempt = completion.as_ref().map(|root| root.begin_attempt());
    let strategy_root = root_attempt.as_ref().map(|attempt| attempt.root().clone());
    let entry_context = Arc::new(ProofEntryContext {
        completion,
        strategy_root,
        cases: opened_entry.prepared_cases().clone(),
        state: state.clone(),
        arguments: arguments.clone(),
        pure_facts: pure_facts.clone(),
        contract_value_parameters: spec_definitions
            .predicates
            .contract_value_parameters
            .clone(),
    });
    // The proof of a function that declares an expression `decreases` measure
    // steps under that function's recursion anchor, which is what makes a
    // self-call raise the descent obligations. The opened execution core binds
    // that context before any statements run; outcome completion retains it.
    let anchored_function_environment =
        crate::kernel::program_execution_environment_with_recursion_anchor_reporting(
            function_environment.clone(),
            &function,
            &state,
            &arguments,
        )
        .map_err(|error| {
            crate::surface::verification::termination_analysis_error(
                &error,
                format!("`{proof_label}`: {error}"),
            )
        })?;
    let function_environment = &anchored_function_environment;
    let proof_site = proof_site_for_claims(function_block, claims, grouped);
    let nested_tactic_capture = expansion_capture
        .as_deref()
        .and_then(|capture| capture.nested_for_site(proof_site.as_ref()));
    let source_layout = SourceExecutionLayout::for_function(parsed_function)?;
    let _spelling = crate::surface::diagnostics::SourcePathSpellingScope::enter(&source_layout);
    // Function-wide indexes belong to claim setup. A loop reads these shared
    // results without charging its tactic for scanning other statements.
    if source_layout.loop_body_entry(0).is_some() {
        source_layout.loop_region_count(|| count_loop_regions(parsed_function));
        source_layout.local_pointer_element_types(|| local_pointer_element_types(parsed_function));
        function.prepare_loop_proofs();
    }
    let constants = ExecutionProofConstants {
        proof_site,
        source_layout,
        execution_start_facts: Arc::new(pure_facts.clone()),
        entry_fact_origins: Arc::new(entry_fact_origins),
        caller_requirement_index: Arc::new(caller_requirement_index),
        caller_source_owner: Some(caller_source_owner),
        function_entry_state: Some(function_entry_state),
        parameter_index: Some((
            parsed_function.parameters().as_ptr() as usize,
            Arc::new(crate::surface::ParameterIndex::new(
                parsed_function.parameters(),
            )),
        )),
        parameter_naming: Some((
            parsed_function.parameters().as_ptr() as usize,
            arguments.as_ptr() as usize,
            Arc::new(crate::surface::ParameterNaming::new(
                parsed_function.parameters(),
                &arguments,
            )),
        )),
        entry_context: Some(entry_context),
        function_source_registry,
        grouped_contract: grouped,
        invariant_body_context: None,
        nested_tactic_capture,
    };
    let frontier = ExecutionFrontier::default();
    let mut recorded_states =
        RecordedStates::new().with_source_layout(constants.source_layout.clone());
    if !entry_separation_sources.facts.is_empty()
        && let Some(point) = state.observation_point_id()
    {
        recorded_states.entry_separation_sources = Some((point, entry_separation_sources));
    }
    record_current_statement_entry(
        &frontier,
        &mut recorded_states,
        &state,
        function_block,
        &function,
        &arguments,
        proof_label,
        0,
        "proof entry",
    )?;
    let mut initial = ExecutionProofState::at_entry(
        state,
        frontier,
        recorded_states,
        surface_propositions,
        PersistentSequence::default(),
    );
    initial.core = opened_entry
        .into_execution_core_with_environment(function_environment)
        .map_err(ClickError::new)?;
    // The checked drivers are tried in order: the structural driver owns
    // scopes and branches, and the flat driver owns linear proofs. A decline
    // tries the next checked driver; an error is terminal.
    let structural = try_check_structural_function_proof(
        &initial,
        &pure_facts,
        &constants,
        &program,
        generated_by_source_index,
        expansion_capture.as_deref_mut(),
        function_block,
        parsed_function,
        proof_label,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    )?;
    let direct_proof = match structural {
        Ok(proof) => Ok(proof),
        Err(structural_decline) => try_check_flat_function_proof(
            &initial,
            &pure_facts,
            &constants,
            &program,
            generated_by_source_index,
            expansion_capture.as_deref_mut(),
            function_block,
            parsed_function,
            proof_label,
            function_environment,
            spec_definitions,
            resource_environment,
            theorem_environment,
            &function,
            &arguments,
        )?
        // The structural driver's reason names more than the flat driver's,
        // which only checks linear proofs: keep the more specific of the two.
        .map_err(|flat_decline| structural_decline.max(flat_decline)),
    };
    if let Ok(proof) = direct_proof {
        match finish_ordered_proof_units(
            expansion_capture,
            vec![proof],
            source_path,
            function_block,
            parsed_function,
            claims,
            grouped,
            spec_definitions,
            resource_environment,
            theorem_environment,
            function_environment,
            &function,
            &arguments,
            tactics,
        ) {
            Ok(theorems) => {
                #[cfg(test)]
                FLAT_PROOF_UNITS.with(|units| units.set(units.get() + 1));
                if let Some(attempt) = root_attempt {
                    attempt.commit();
                }
                return Ok(ClaimProofResult { theorems });
            }
            Err(error) => return Err(error),
        }
    }
    let claim_labels = claims
        .iter()
        .map(|claim| diagnostic_claim_label(function_block, claim))
        .collect::<Vec<_>>();
    let decline = direct_proof.err().unwrap_or(Decline::Shape);
    Err(checked_driver_refusal(proof_label, &claim_labels, decline)
        .at_declaration(function_block.signature().name()))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn prove_claims_by_implicit_tail(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let mut tactics = vec![ProofTactic::SmartExecute];
    if !claims.is_empty() {
        if let Some(split) = entry_type_resource_split(function_block, claims, resource_environment)
        {
            tactics = vec![split];
        }
        tactics.push(ProofTactic::ImplicitSolve);
    }

    let verified = prove_claims_by_grouped_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    Ok(verified.theorems)
}

/// The implicit tail's split at entry on a conditional resource the function
/// takes, when a claim reads the entry state: `if c { unfold(R(x)); ... }
/// else { unfold(R(x)); }`, each arm executing to the exit.
///
/// A resource whose body is `if c { owns S(..); }`, as an option of a box's
/// type resource is, holds its contents only on one side of `c`. A claim
/// that reads those contents at entry, `old(self.slot.value)`, needs them
/// related to the reads the program makes after it has stored to the place,
/// and the facts that relate them are the ones the unfolded body gives at
/// entry. Splitting there is one case analysis on the resource's own
/// condition, written out by expansion; the closer folds at the exit.
fn entry_type_resource_split(
    function_block: &FunctionBlock,
    claims: &[FunctionClaimRef<'_>],
    resource_environment: &ResourceEnvironment,
) -> Option<ProofTactic> {
    let reads_entry = claims.iter().any(|claim| match claim.clause().ensure() {
        Ensure::Proposition(proposition) => proposition_contains_old_expression(proposition),
        Ensure::Resource(_) => false,
    });
    if !reads_entry {
        return None;
    }
    function_block.requires().iter().find_map(|requirement| {
        let Requirement::Resource(
            resource @ ResourceClause::Declared {
                kind: ResourceKind::Composite,
                name,
                arguments,
                ..
            },
        ) = requirement
        else {
            return None;
        };
        let definition = resource_environment.get(name)?;
        let body = definition.composite_body()?;
        let condition = body.condition()?;
        let [inner @ ResourceClause::Declared { .. }] = body.contains() else {
            return None;
        };
        if definition.parameters().len() != arguments.len() {
            return None;
        }
        let substitutions = definition
            .parameters()
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| (parameter.name.as_str(), argument.clone()))
            .collect::<BTreeMap<&str, ContractExpression>>();
        let condition =
            crate::surface::lowering::substitute_click_proposition(condition, &substitutions)
                .ok()?;
        let inner = crate::surface::verification::substitute_resource_clause_for_summary(
            inner,
            &substitutions,
        )
        .ok()?;
        let mut outer = resource.clone();
        if let ResourceClause::Declared { access, .. } = &mut outer {
            *access = ResourceAccessMode::Own;
        }
        let mut inner = inner;
        if let ResourceClause::Declared { access, .. } = &mut inner {
            *access = ResourceAccessMode::Own;
        }
        Some(ProofTactic::If(ProofIf {
            condition,
            ensuring: None,
            then_tactics: vec![
                ProofTactic::UnfoldResource(outer.clone()),
                ProofTactic::UnfoldResource(inner),
                ProofTactic::SmartExecute,
            ],
            else_tactics: vec![
                ProofTactic::UnfoldResource(outer),
                ProofTactic::SmartExecute,
            ],
        }))
    })
}

/// A written script followed by the implicit tail every script ends with: a
/// closer at a live frontier executes the C that remains, and at function
/// exit it closes what is still open, as the implicit closer does. A script
/// that ends in `match`, `outcomes`, `both` or structural induction ends in
/// its arms, each with its own implicit closer, so nothing is appended after
/// it. After a proof `if` or `cases` the tail is appended: before execution
/// it runs the C the split left, and after execution, where the split forks
/// the returned paths, it is the closer each forked path runs. Returns
/// whether the tail was appended.
pub(super) fn with_implicit_tail(tactics: &[ProofTactic]) -> (Vec<ProofTactic>, bool) {
    let mut tactics = tactics.to_vec();
    let ends_linearly = !matches!(
        tactics.last(),
        None | Some(
            ProofTactic::ImplicitSolve
                | ProofTactic::Match(_)
                | ProofTactic::CallOutcomes(_)
                | ProofTactic::Both(_)
                | ProofTactic::All(_)
        )
    );
    if ends_linearly {
        tactics.push(ProofTactic::ImplicitSolve);
    }
    (tactics, ends_linearly)
}

/// An explicit grouped proof script. The completed proof unit is accepted
/// directly; retained evidence is serialized only for expansion.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn prove_claims_by_grouped_script(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let verified = prove_claims_by_grouped_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function_source_registry,
        tactics,
        ProofTacticSource::SourceSyntax,
    )?;
    Ok(verified.theorems)
}

/// Claim acceptance and presentation are separate. Every closed claim retains
/// a checked proposition, exact resource production, or vacuous checked path.
mod exit_claim {
    use super::*;

    #[derive(Clone, Debug)]
    pub(super) enum ClaimCertificate {
        Claim(Vec<ProofTactic>),
        GroupedTransition,
        ExactCheck,
    }

    #[derive(Clone)]
    enum ClaimEvidence<'e> {
        Proposition(crate::kernel::proof::CheckedProposition),
        Resource(CheckedResourceClaim<'e>),
        Vacuous(&'e CheckedFunctionExecution),
    }

    #[derive(Clone)]
    pub(super) struct ClosedClaim<'e> {
        key: FunctionContractClaimKey,
        path_index: usize,
        certificate: ClaimCertificate,
        evidence: ClaimEvidence<'e>,
    }

    impl ClosedClaim<'_> {
        pub(super) fn claim_tactics(&self) -> &[ProofTactic] {
            match &self.certificate {
                ClaimCertificate::Claim(tactics) => tactics,
                ClaimCertificate::GroupedTransition | ClaimCertificate::ExactCheck => &[],
            }
        }
        /// The kernel evidence this closure gives the claim's goal on the
        /// outcome Proof. A vacuous closure gives none: a path that reaches
        /// an outcome holds its vacuous claims from the start.
        pub(super) fn goal_evidence(&self) -> Option<crate::kernel::proof::ClaimGoalEvidence> {
            use crate::kernel::proof::{ClaimGoalEvidence, ClaimResourceReceipt};
            match &self.evidence {
                ClaimEvidence::Proposition(checked) => {
                    Some(ClaimGoalEvidence::Proposition(checked.clone()))
                }
                ClaimEvidence::Resource(checked) => {
                    Some(ClaimGoalEvidence::Resource(ClaimResourceReceipt {
                        returned_resources: checked.returned_resources().clone(),
                        contributes_returned_resources: checked.contributes_returned_resources(),
                        defers_resource_transition: checked.defers_resource_transition(),
                    }))
                }
                ClaimEvidence::Vacuous(_) => None,
            }
        }
        pub(super) fn validate_for(
            &self,
            execution: &CheckedFunctionExecution,
            path_index: usize,
            key: &FunctionContractClaimKey,
        ) -> Result<(), ClickError> {
            let matches = self.path_index == path_index
                && &self.key == key
                && match &self.evidence {
                    ClaimEvidence::Proposition(_) => true,
                    ClaimEvidence::Resource(checked) => checked.matches(execution, path_index, key),
                    ClaimEvidence::Vacuous(checked) => std::ptr::eq(*checked, execution),
                };
            if matches {
                Ok(())
            } else {
                Err(ClickError::new(
                    "claim closure evidence belongs to a different claim or execution path",
                ))
            }
        }
    }

    #[derive(Clone)]
    pub(super) enum ClaimClosure<'e> {
        Open(Option<ClickError>),
        Closed(ClosedClaim<'e>),
    }
    impl Default for ClaimClosure<'_> {
        fn default() -> Self {
            Self::Open(None)
        }
    }
    impl<'e> ClaimClosure<'e> {
        pub(super) fn is_closed(&self) -> bool {
            matches!(self, Self::Closed(_))
        }
        pub(super) fn closed(&self) -> Option<&ClosedClaim<'e>> {
            match self {
                Self::Closed(closed) => Some(closed),
                _ => None,
            }
        }
        pub(super) fn require_evidence(
            &self,
            execution: &CheckedFunctionExecution,
            path_index: usize,
            key: &FunctionContractClaimKey,
        ) -> Result<&ClosedClaim<'e>, ClickError> {
            let closed = self
                .closed()
                .ok_or_else(|| ClickError::new("claim has no checked completion evidence"))?;
            closed.validate_for(execution, path_index, key)?;
            Ok(closed)
        }
        pub(super) fn last_error(&self) -> Option<&ClickError> {
            match self {
                Self::Open(error) => error.as_ref(),
                _ => None,
            }
        }
        pub(super) fn record_failure(&mut self, message: ClickError) {
            if let Self::Open(error) = self {
                *error = Some(message);
            }
        }

        /// A claim closed inside the proof that earlier deferred tactics
        /// opened. Those tactics are already in the path's surface proof, so
        /// the claim contributes only `tactics`, what followed them.
        pub(super) fn by_continued_proposition(
            key: FunctionContractClaimKey,
            path_index: usize,
            tactics: Vec<ProofTactic>,
            checked: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::proposition(key, path_index, ClaimCertificate::Claim(tactics), checked)
        }

        pub(super) fn by_checked_proposition(
            key: FunctionContractClaimKey,
            path_index: usize,
            certificate: &ProofCertificate,
            checked: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::proposition(
                key,
                path_index,
                ClaimCertificate::Claim(certificate.to_proof_tactics()),
                checked,
            )
        }
        pub(super) fn by_grouped_proposition(
            key: FunctionContractClaimKey,
            path_index: usize,
            _certificate: &ProofCertificate,
            checked: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::proposition(
                key,
                path_index,
                ClaimCertificate::GroupedTransition,
                checked,
            )
        }
        pub(super) fn by_exact_check_completing(
            key: FunctionContractClaimKey,
            path_index: usize,
            checked: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::proposition(key, path_index, ClaimCertificate::ExactCheck, checked)
        }
        fn proposition(
            key: FunctionContractClaimKey,
            path_index: usize,
            certificate: ClaimCertificate,
            checked: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::Closed(ClosedClaim {
                key,
                path_index,
                certificate,
                evidence: ClaimEvidence::Proposition(checked),
            })
        }
        pub(super) fn resource(
            certificate: ClaimCertificate,
            checked: CheckedResourceClaim<'e>,
        ) -> Self {
            Self::Closed(ClosedClaim {
                key: checked.claim_key().clone(),
                path_index: checked.path_index(),
                certificate,
                evidence: ClaimEvidence::Resource(checked),
            })
        }
        /// Vacuity is read only from the kernel-created execution theorem for
        /// this path, never from a caller's boolean or serialized closer.
        pub(super) fn vacuous(
            execution: &'e CheckedFunctionExecution,
            path_index: usize,
            key: FunctionContractClaimKey,
            certificate: ClaimCertificate,
        ) -> Result<Self, ClickError> {
            let path = execution
                .paths()
                .get(path_index)
                .ok_or_else(|| ClickError::new("vacuous claim has no checked path"))?;
            let Proposition::ProgramFunctionVerifies { outcome, .. } =
                implication_body(path.theorem().proposition())
            else {
                return Err(ClickError::new(
                    "vacuous claim has no checked function outcome",
                ));
            };
            if !matches!(
                (&key, outcome),
                (_, FunctionOutcome::VerificationDiverges)
                    | (
                        FunctionContractClaimKey::Ensure(_),
                        FunctionOutcome::Throw { .. }
                    )
                    | (
                        FunctionContractClaimKey::ExceptionalEnsure(_),
                        FunctionOutcome::Return { .. }
                    )
            ) {
                return Err(ClickError::new(
                    "checked outcome does not make this claim vacuous",
                ));
            }
            Ok(Self::Closed(ClosedClaim {
                key,
                path_index,
                certificate,
                evidence: ClaimEvidence::Vacuous(execution),
            }))
        }
    }
}

use exit_claim::{ClaimCertificate, ClaimClosure, ClosedClaim};

/// Contract closing constructs the kernel obligation for this postcondition
/// at the checked outcome. Its evaluation requirements are ordinary proof
/// obligations, and its completion retains the clause it establishes.
fn contract_closing_goal<'a>(
    function: &'a ProgramFunction,
    retained_entry: Option<&crate::kernel::RetainedClosingEntry>,
    target: Option<&FunctionContractClaimTarget>,
    pre_state: &ExecutionState,
    arguments: &[ProgramExpression],
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
    return_context: &mut Option<Option<crate::kernel::FunctionEnsureGoalContext<'a>>>,
) -> Result<Option<crate::kernel::ContractClaimGoal>, ClickError> {
    // None denotes a structural claim or a proof-local clause of a function
    // without a reusable contract, not a failed postcondition construction.
    // Registered postconditions always return a kernel goal or an error.
    let Some(target) = target else {
        return Ok(None);
    };
    let claim_label = match target {
        FunctionContractClaimTarget::EnsureProposition(index) => {
            format!("{}.ensures_{index}", function.name())
        }
        FunctionContractClaimTarget::ExceptionalEnsureProposition(index) => {
            format!("{}.exceptional_ensures_{index}", function.name())
        }
        _ => return Ok(None),
    };
    let mut goals = match target {
        FunctionContractClaimTarget::EnsureProposition(contract_index) => return_context
            .get_or_insert_with(|| {
                crate::instrumentation::measure_operation(
                    function.name(),
                    "explicit return closer",
                    "return claim state preparation",
                    || match retained_entry {
                        Some(entry) => {
                            crate::kernel::FunctionEnsureGoalContext::from_retained_entry(
                                function,
                                entry,
                                outcome,
                                assumptions,
                            )
                        }
                        None => crate::kernel::FunctionEnsureGoalContext::new(
                            function,
                            pre_state,
                            arguments,
                            outcome,
                            assumptions,
                        ),
                    },
                )
            })
            .as_ref()
            .ok_or_else(|| {
                ClickError::new(
                    "contract closing could not construct the postcondition's entry and exit views",
                )
                .with_kind(ClickErrorKind::Internal)
            })?
            .goals(*contract_index)
            .map_err(|reason| {
                closing_goal_error(
                    &format!("`{}.ensures_{contract_index}`", function.name()),
                    reason,
                )
            })?,
        FunctionContractClaimTarget::ExceptionalEnsureProposition(contract_index) => {
            match retained_entry {
                Some(entry) => crate::kernel::program_function_exceptional_ensure_goals_from_entry(
                    function,
                    *contract_index,
                    entry,
                    outcome,
                    assumptions,
                ),
                None => crate::kernel::program_function_exceptional_ensure_goals(
                    function,
                    *contract_index,
                    pre_state,
                    arguments,
                    outcome,
                    assumptions,
                ),
            }
            .map_err(|reason| closing_goal_error(&claim_label, reason))?
        }
        _ => return Ok(None),
    };
    if goals.is_empty() {
        return Err(ClickError::new(format!(
            "contract closing could not evaluate `{claim_label}` at this outcome",
        ))
        .with_proof_refusal(ProofRefusal::IncompleteProof));
    }
    if goals.len() != 1 {
        return Err(ClickError::new(format!(
            "contract closing produced {} evaluation paths for `{claim_label}`; establish the selecting condition before closing this claim",
            goals.len(),
        )).with_proof_refusal(ProofRefusal::IncompleteProof));
    }
    Ok(goals.pop())
}

fn closing_goal_error(claim: &str, reason: crate::kernel::EnsureGoalRefusal) -> ClickError {
    use crate::kernel::{EnsureGoalRefusal, ExecutionLimit};
    let diagnostic = ClickError::new(format!("contract closing for {claim}: {reason}"));
    match reason {
        EnsureGoalRefusal::MissingClause(_)
        | EnsureGoalRefusal::MissingExceptionalClause(_)
        | EnsureGoalRefusal::EntryUnavailable
        | EnsureGoalRefusal::ExpectedThrow
        | EnsureGoalRefusal::Stopped(
            ExecutionLimit::Deadline
            | ExecutionLimit::ExpressionSteps
            | ExecutionLimit::StatementSteps
            | ExecutionLimit::FunctionCalls
            | ExecutionLimit::LoopUnrolls
            | ExecutionLimit::KernelVariables { .. }
            | ExecutionLimit::MatchBinderVariables { .. }
            | ExecutionLimit::ExecutionIdentityBesideLiveState
            | ExecutionLimit::QuantifierDoesNotClose,
        ) => diagnostic.with_kind(ClickErrorKind::Internal),
        EnsureGoalRefusal::Stopped(
            ExecutionLimit::GuardedConjunctionTooLong
            | ExecutionLimit::SymbolicPointerConditional
            | ExecutionLimit::UnsupportedPureFunctionResult(_),
        ) => diagnostic.with_kind(ClickErrorKind::Unsupported),
        EnsureGoalRefusal::Stopped(
            ExecutionLimit::BoolArithmetic
            | ExecutionLimit::BoolComparedWithInteger
            | ExecutionLimit::BoolOrdered
            | ExecutionLimit::MixedBoolArms
            | ExecutionLimit::LoopIterationsUnbound,
        ) => diagnostic.with_proof_refusal(ProofRefusal::Contract),
        EnsureGoalRefusal::Unavailable(_)
        | EnsureGoalRefusal::Stopped(
            ExecutionLimit::Paths
            | ExecutionLimit::ResourceFieldInstanceUnavailable
            | ExecutionLimit::AuthorityCountNeedsExactPointer
            | ExecutionLimit::AuthorityCountNeedsResolvedMember
            | ExecutionLimit::AuthorityCountNeedsOwnership
            | ExecutionLimit::AuthorityCountLentToWorker
            | ExecutionLimit::AuthorityCountPendingLockedWorker
            | ExecutionLimit::DisjunctionRightUndefined,
        ) => diagnostic.with_proof_refusal(ProofRefusal::IncompleteProof),
    }
}

/// The retained contract judgment for an explicit closer. Definition
/// exposure happens through local proof steps inside that judgment.
fn contract_closing_goal_forms<'a>(
    function: &'a ProgramFunction,
    retained_entry: Option<&crate::kernel::RetainedClosingEntry>,
    target: Option<&FunctionContractClaimTarget>,
    pre_state: &ExecutionState,
    arguments: &[ProgramExpression],
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
    return_context: &mut Option<Option<crate::kernel::FunctionEnsureGoalContext<'a>>>,
) -> Result<Vec<Option<crate::kernel::ContractClaimGoal>>, ClickError> {
    crate::instrumentation::measure_operation(
        function.name(),
        "explicit return closer",
        "return claim goal lowering",
        || {
            contract_closing_goal(
                function,
                retained_entry,
                target,
                pre_state,
                arguments,
                outcome,
                assumptions,
                return_context,
            )
        },
    )
    .map(|form| vec![form])
}

/// Requires the checked outcome from which contract closing opens its goals.
fn required_outcome<'p, 'a>(root: &'p Option<Proof<'a>>) -> Result<&'p Proof<'a>, ClickError> {
    root.as_ref()
        .ok_or_else(|| ClickError::new("operation requires a retained outcome Proof"))
}

fn focus_claim_goal<'a>(
    root: &Proof<'a>,
    kernel_goal: Option<crate::kernel::ContractClaimGoal>,
    source_key: &FunctionContractClaimKey,
    surface_goal: &ClickProposition,
) -> Result<Proof<'a>, ClickError> {
    match kernel_goal {
        Some(goal) => root.driver().open_contract_claim(&goal, surface_goal),
        // Structural claims and proof-local clauses have no reusable kernel
        // postcondition. A failed registered postcondition construction is an
        // Err and cannot reach this path.
        None => root.focus_source_contract_claim(source_key, surface_goal),
    }
}

/// Which claim proof a step is applied to: the proof a `rewrite` left the
/// claim on, or a goal freshly focused from the outcome Proof.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ClaimProofOrigin {
    Rewritten,
    Fresh,
}

/// A step that applied to a claim, with the certificate it adds to the claim
/// proof it continued.
struct ClaimStepApplied<'a> {
    proof: Proof<'a>,
    certificate: ProofCertificate,
}

/// A step that applied to none of a claim's goals. `error` is the last
/// refusal, if any goal was tried.
struct ClaimStepMiss {
    error: Option<ClickError>,
    origin: ClaimProofOrigin,
}

/// Applies one written step to a proposition claim. A claim a `rewrite` left
/// on its own proof is continued there and nowhere else, after that proof
/// takes up the outcome's current state from `root`. Otherwise each
/// candidate goal is focused from `root` in turn until the step applies.
/// `step` returns an outer error to abort the tactic, and an inner one to
/// refuse the goal it was given.
fn apply_claim_step<'a>(
    rewritten: Option<&(Proof<'a>, ProofCheckpoint<'a>)>,
    root: Option<&Proof<'a>>,
    source_key: &FunctionContractClaimKey,
    surface_goal: &ClickProposition,
    candidates: impl FnOnce() -> Result<Vec<Option<crate::kernel::ContractClaimGoal>>, ClickError>,
    step: impl Fn(&Proof<'a>, ClaimProofOrigin) -> Result<Result<Proof<'a>, ClickError>, ClickError>,
) -> Result<Result<ClaimStepApplied<'a>, ClaimStepMiss>, ClickError> {
    if let Some((rewritten, checkpoint)) = rewritten {
        let rewritten = match root {
            Some(root) => rewritten.refresh_outcome_from(root)?,
            None => rewritten.clone(),
        };
        return match step(&rewritten, ClaimProofOrigin::Rewritten)? {
            Ok(proof) => Ok(Ok(ClaimStepApplied {
                certificate: proof.certificate_since(checkpoint)?,
                proof,
            })),
            Err(error) => {
                check_verification_deadline()?;
                Ok(Err(ClaimStepMiss {
                    error: Some(error),
                    origin: ClaimProofOrigin::Rewritten,
                }))
            }
        };
    }
    let candidates = candidates()?;
    let Some(root) = root else {
        return Ok(Err(ClaimStepMiss {
            error: None,
            origin: ClaimProofOrigin::Fresh,
        }));
    };
    let mut last_error = None;
    for goal in candidates {
        let focused = match goal {
            Some(goal) => root.driver().open_contract_claim(&goal, surface_goal)?,
            None => root.focus_source_contract_claim(source_key, surface_goal)?,
        };
        match step(&focused, ClaimProofOrigin::Fresh)? {
            Ok(proof) => {
                return Ok(Ok(ClaimStepApplied {
                    certificate: proof.certificate(),
                    proof,
                }));
            }
            Err(error) => last_error = Some(error),
        }
    }
    check_verification_deadline()?;
    Ok(Err(ClaimStepMiss {
        error: last_error,
        origin: ClaimProofOrigin::Fresh,
    }))
}

/// Starts a result-aware proof for the same claim the ordinary closers focus.
fn begin_outcome_claim_proof<'a>(
    outcome_root: &Proof<'a>,
    function: &ProgramFunction,
    pre_state: &ExecutionState,
    arguments: &[ProgramExpression],
    outcome: &FunctionOutcome,
    claims: &[FunctionClaimRef<'_>],
    rewrite_claim_equalities: &[Vec<ClickProposition>],
    tactic: &str,
) -> Result<(usize, ClickProposition, Proof<'a>), ClickError> {
    let (claim_index, surface_goal) = focused_proposition_claim(outcome_root, claims, tactic)?;
    let claim_key = claims[claim_index].key();
    let kernel_goal = contract_closing_goal(
        function,
        outcome_root
            .execution_context()
            .and_then(|context| context.constants.entry_context.as_ref())
            .map(|entry| entry.cases.closing_entry()),
        outcome_root
            .claim_goals()
            .and_then(|goals| goals.target(&claim_key)),
        pre_state,
        arguments,
        outcome,
        outcome_root.facts().assumptions(),
        &mut None,
    )?;
    let mut proof = focus_claim_goal(outcome_root, kernel_goal, &claim_key, surface_goal)?;
    for equality in &rewrite_claim_equalities[claim_index] {
        proof = proof
            .driver()
            .apply_step(ProofStep::Rewrite(equality.clone()))?;
    }
    Ok((claim_index, surface_goal.clone(), proof))
}

/// Closes one proposition claim from the outcome Proof by the direct logical
/// closure: the implicit closer of a claim with no `by` block. Rewrites and
/// applied as an explicit claim body would apply them. A
/// goal the fixed-state lowering cannot express, or that the closure does not
/// reach, is a miss; only a deadline is an error.
/// The implicit closer of a proposition claim: the claim goal is the
/// kernel's lowering of the contract ensure at the outcome, closed by the
/// direct logical closure or, when that does not apply, by the smart `solve`
/// search whose certificate is checked like an explicit one. Either way the
/// completion retains the contract claim it proves. When neither closes the
/// claim the reason names what stood in the way: the goal's lowering, a
/// rewrite that did not apply, or the goal left unclosed with the sides it
/// evaluated to and the checked proof context. The context is reported, not a
/// guess at which step was missing.
#[allow(clippy::too_many_arguments)]
/// How far [`close_claim_directly_from_outcome`] searches for a closure.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ClaimClosureSearch<'p> {
    /// Explain why the claim is open without searching.
    None,
    /// `solve() using`: only the listed premises.
    Restricted(&'p [ClickProposition]),
    /// The direct logical closure, then `solve`.
    Solve,
}

fn close_claim_directly_from_outcome<'a>(
    outcome_root: &Proof<'a>,
    function: &ProgramFunction,
    claim: &FunctionClaimRef<'_>,
    pre_state: &ExecutionState,
    outcome: &FunctionOutcome,
    surface_goal: &ClickProposition,
    rewrite_equalities: &[ClickProposition],
    claim_label: &str,
    path_index: usize,
    entry_facts: &(impl PropositionSource + ?Sized),
    execution_paths: &[crate::kernel::FunctionExecutionCandidate],
    parameter_binding: ParameterBinding<'_>,
    spec_definitions: SpecDefinitions<'_>,
    // How far to search before explaining a failure. An explicit closer's
    // failure explanation has already searched and must not search again.
    closure_search: ClaimClosureSearch<'_>,
    failed_attempt: Option<&Proof<'a>>,
) -> Result<Result<Proof<'a>, ClickError>, ClickError> {
    let surface = describe_click_proposition(surface_goal);
    let failure = |reason: String| {
        Ok(Err(ClickError::new(format!(
            "`ensures {surface}` failed for `{claim_label}` path {path_index}: {reason}"
        ))))
    };
    if !claim.applies_to(outcome) {
        return failure(describe_function_outcome(outcome, parameter_binding));
    }
    let root = failed_attempt.unwrap_or(outcome_root).clone();
    let kernel_goal = failed_attempt
        .is_none()
        .then(|| {
            contract_closing_goal(
                function,
                root.execution_context()
                    .and_then(|context| context.constants.entry_context.as_ref())
                    .map(|entry| entry.cases.closing_entry()),
                root.claim_goals()
                    .and_then(|goals| goals.target(&claim.key())),
                pre_state,
                parameter_binding.arguments,
                outcome,
                root.facts().assumptions(),
                &mut None,
            )
        })
        .transpose()?
        .flatten();
    let listed_goal = failed_attempt
        .and_then(Proof::goal)
        .cloned()
        .or_else(|| kernel_goal.as_ref().map(|goal| goal.proposition().clone()));
    let mut proof = if let Some(failed) = failed_attempt {
        failed.clone()
    } else {
        match focus_claim_goal(&root, kernel_goal, &claim.key(), surface_goal) {
            Ok(proof) => proof,
            Err(error) => {
                check_verification_deadline()?;
                // A missed domain is an ordinary open proof obligation. Keep
                // its exact goal and checked context through the claim wrapper;
                // converting it to a summary string loses both in the report.
                let reason = if error.unresolved_requirement().is_some() {
                    format!("unclosed goal: {surface}")
                } else {
                    "could not lower the claim goal".to_string()
                };
                return Ok(Err(error
                    .with_context(format!(
                        "`ensures {surface}` failed for `{claim_label}` path {path_index}: {reason}"
                    ))
                    .with_failing_path(path_index)));
            }
        }
    };
    if failed_attempt.is_none() {
        for equality in rewrite_equalities {
            proof = match proof
                .driver()
                .apply_step(ProofStep::Rewrite(equality.clone()))
            {
                Ok(next) => next,
                Err(error) => {
                    check_verification_deadline()?;
                    return failure(format!(
                        "rewrite `{}` did not apply: {}",
                        describe_click_proposition(equality),
                        error.raw_summary()
                    ));
                }
            };
        }
    }
    let mut search = super::attempt::search_scope("claim outcome closure");
    if let ClaimClosureSearch::Restricted(premises) = closure_search {
        let selected =
            crate::kernel::search::ProofSearch::try_restricted_solve_closure(&(proof), premises);
        check_verification_deadline()?;
        if let Some(completed) = selected
            && completed.is_complete()
        {
            search.succeed();
            return Ok(Ok(completed));
        }
    } else if closure_search != ClaimClosureSearch::None {
        if let Some(completed) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))?
            && completed.is_complete()
        {
            search.succeed();
            return Ok(Ok(completed));
        }
        if let Some(completed) = crate::kernel::search::ProofSearch::try_solve_closure(&(proof))?
            && completed.is_complete()
        {
            search.succeed();
            return Ok(Ok(completed));
        }
        check_verification_deadline()?;
    }
    check_verification_deadline()?;
    // One label set for the whole report: a read of the outcome state is
    // the bare place, a read of the entry memory is `old(...)`, and any
    // other memory a value reads is a `<state A>` defined after the context.
    let mut labels =
        crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
    if let FunctionOutcome::Return { state, .. } | FunctionOutcome::Throw { state, .. } = outcome {
        labels.register_current_state(state);
    }
    if let FunctionOutcome::Return { value, .. } = outcome {
        labels.source_result(&value.native());
    }
    // A value the outcome state no longer names may be what a local held
    // at a statement boundary this path recorded, which an `ensures` cites
    // as `at(region(N).entry, x)`.
    if let Some(view) = proof.outcome_fixed_state_view() {
        super::proof_object::register_recorded_state_names(
            &mut labels,
            view.fixed_state.recorded_states,
        );
    }
    // A comparison reports what each side evaluates to at the outcome, by
    // the same kernel evaluation every proof-side expression gets. Two
    // distinct load variables over one address render identically, so that
    // case names the surface spellings and which state each reads.
    let evaluated_sides = match (surface_goal, outcome) {
        (
            ClickProposition::Comparison { left, right, .. },
            FunctionOutcome::Return { value, state },
        ) => {
            let values = parameter_values(parameter_binding).unwrap_or_default();
            let array_refs = array_refs_for_parameters(
                parameter_binding.parameters,
                &values,
                &state.program_point(),
            );
            let evaluate = |expression: &ContractExpression| {
                evaluate_fixed_state_expression_through_kernel(
                    expression,
                    root.facts().assumptions(),
                    ContractEnvironment::new(&values, &array_refs)
                        .with_parameters(parameter_binding),
                    FixedStateFrame::new(
                        pre_state,
                        state,
                        Some(&value.native()),
                        &RecordedStates::new(),
                    ),
                    spec_definitions,
                    &BTreeSet::new(),
                )
                .ok()
                // What a read of a stored cell evaluates to is the value
                // stored there (the read-over-write authority).
                .map(|value| crate::kernel::read_over_write_program_value(&value))
            };
            match (evaluate(left), evaluate(right)) {
                (Some(kernel_left), Some(kernel_right)) => {
                    let rendered_left =
                        crate::surface::proof_diagnostics::render::render_program_value_labeled(
                            &kernel_left,
                            &mut labels,
                        );
                    let rendered_right =
                        crate::surface::proof_diagnostics::render::render_program_value_labeled(
                            &kernel_right,
                            &mut labels,
                        );
                    // Whether the two sides are reads of one address, which
                    // the unqualified address spelling tells.
                    let same_address = describe_program_value(&kernel_left, parameter_binding)
                        == describe_program_value(&kernel_right, parameter_binding);
                    // Two reads of one address of different kinds are two
                    // values whatever happened in between: say that, and not
                    // which state or store set them apart.
                    if let Some(mismatch) = crate::surface::diagnostics::describe_load_kind_mismatch(
                        &kernel_left,
                        &kernel_right,
                        parameter_binding,
                        Some(root.facts().assumptions()),
                    ) {
                        format!(
                            "; left side evaluated to {rendered_left}, right side evaluated to \
                             {rendered_right}; {mismatch}"
                        )
                    } else {
                        // Which state a side reads, as the reader would name it.
                        // Both branches below need it: one to say the two sides
                        // read different states, the other to say what a value
                        // may have changed *since*.
                        let state_role = |expression: &ContractExpression| {
                            if contains_old_expression(expression) {
                                "function entry"
                            } else if contains_at_expression(expression) {
                                "a recorded state"
                            } else {
                                "the outcome state"
                            }
                        };
                        if same_address && kernel_left != kernel_right {
                            let surface_left = describe_contract_expression(left);
                            let surface_right = describe_contract_expression(right);
                            let left_role = state_role(left);
                            let right_role = state_role(right);
                            let program_point_note = if left_role == right_role {
                                format!(
                                    "`{surface_left}` and `{surface_right}` both read {left_role}"
                                )
                            } else {
                                format!(
                                    "`{surface_left}` reads {left_role}, `{surface_right}` reads {right_role}"
                                )
                            };
                            // Both sides read one address at two program points,
                            // which is the resource tracker's question: it names
                            // the step in between that broke the chain.
                            let tracked = describe_two_sided_version_mismatch(
                                &kernel_left,
                                &kernel_right,
                                left_role,
                                right_role,
                                parameter_binding,
                            )
                            .map(|mismatch| format!("; {mismatch}"))
                            .unwrap_or_default();
                            format!(
                                "; the two sides read the same address in different memory states ({program_point_note}){tracked}"
                            )
                        } else {
                            // A side still standing as a load did not survive the
                            // body. The tracker names the step its walk stopped
                            // at: the repair is a resource or a `separate`, not
                            // another tactic.
                            // A side that is a model field did not survive either,
                            // and its versions are values in two saved states
                            // rather than points on the memory history, so the
                            // tracker is asked about the two states this claim
                            // compares.
                            let model_field = |value: &ProgramValue, role: &str| {
                                describe_model_field_mismatch(
                                    value,
                                    state,
                                    pre_state,
                                    if role == "the outcome state" {
                                        "function entry"
                                    } else {
                                        role
                                    },
                                    parameter_binding,
                                )
                            };
                            let unseparated = describe_read_address_mismatch(
                                &kernel_left,
                                &kernel_right,
                                parameter_binding,
                            )
                            .map(|mismatch| format!("; {mismatch}"))
                            .or_else(|| describe_unseparated_write(&kernel_left, parameter_binding))
                            .or_else(|| {
                                describe_unseparated_write(&kernel_right, parameter_binding)
                            })
                            .or_else(|| {
                                model_field(&kernel_left, state_role(left))
                                    .or_else(|| model_field(&kernel_right, state_role(right)))
                                    .map(|mismatch| format!("; {mismatch}"))
                            })
                            .unwrap_or_default();
                            format!(
                                "; left side evaluated to {rendered_left}, right side evaluated to {rendered_right}{unseparated}"
                            )
                        }
                    }
                }
                _ => String::new(),
            }
        }
        _ => String::new(),
    };
    // Which checked step is missing is not knowable here, so the diagnostic
    // also reports the checked proof context every other failure path
    // reports, rather than guessing at the absent reasoning.
    let resource_facts: &[ResourceFact] = match outcome {
        FunctionOutcome::Return { state, .. } | FunctionOutcome::Throw { state, .. } => {
            state.resources().facts()
        }
        FunctionOutcome::VerificationDiverges
        | FunctionOutcome::UndefinedBehavior(_)
        | FunctionOutcome::RuntimeError(_) => &[],
    };
    // The pure facts listed are those bearing on the goal, so a premise the
    // closure lacked is not pushed past the item limit by unrelated ones.
    let path_facts = root.facts().propositions().cloned().collect::<Vec<_>>();
    let native_result = match outcome {
        FunctionOutcome::Return { value, .. } => Some(value.native()),
        _ => None,
    };
    let context = describe_goal_proof_context(
        listed_goal.as_ref(),
        &path_facts,
        &path_case_facts(entry_facts, execution_paths, path_index),
        resource_facts,
        native_result.as_deref(),
        &mut labels,
        &|fact| proof.round_trip_source_text(fact),
    );
    // A read of a cell a store dropped after the store search missed names
    // that store and the fact that keeps the cell.
    let store_separation_miss = listed_goal
        .as_ref()
        .and_then(|goal| proof.store_separation_miss_for_goal(goal))
        .map(|(miss, _)| {
            format!(
                "\n{}",
                crate::surface::proof::smart_closures::describe_recorded_store_separation_miss(
                    &miss
                )
            )
        })
        .unwrap_or_default();
    let error = proof.step_error(format!(
        "`ensures {surface}` failed for `{claim_label}` path {path_index}: unclosed goal: {surface}{evaluated_sides}{store_separation_miss}\n{context}"
    ));
    let refusal = match closure_search {
        ClaimClosureSearch::None => crate::surface::ProofRefusal::IncompleteProof,
        ClaimClosureSearch::Restricted(_) | ClaimClosureSearch::Solve => {
            crate::surface::ProofRefusal::UnsuccessfulSearch
        }
    };
    Ok(Err(error
        .with_proof_refusal(refusal)
        .with_search_failures(search.finish())
        .with_failing_path(path_index)))
}

/// The conditions that make one execution path the case it is: each C
/// branch condition, implicit-tail case split, and proof `if` case that sets
/// its checked path apart from another -- a condition fact of
/// `paths[path_index]` that some other path lacks. A fact the execution
/// started from -- an entry `requires`, or a `have` before the first step --
/// is never among them: every path has it.
fn path_case_facts(
    entry_facts: &(impl PropositionSource + ?Sized),
    paths: &[crate::kernel::FunctionExecutionCandidate],
    path_index: usize,
) -> Vec<Proposition> {
    use std::collections::BTreeSet;
    fn is_condition(fact: &Proposition) -> bool {
        match fact {
            Proposition::ConditionIs(..) => true,
            Proposition::Not(inner) => is_condition(inner),
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => is_condition(left) && is_condition(right),
            _ => false,
        }
    }
    let Some(path) = paths.get(path_index) else {
        return Vec::new();
    };
    // An entry conjunction is assumed conjunct by conjunct.
    let mut entry = BTreeSet::new();
    let mut pending = entry_facts.propositions().collect::<Vec<_>>();
    while let Some(fact) = pending.pop() {
        if let Proposition::And(left, right) = fact {
            pending.push(left);
            pending.push(right);
        }
        entry.insert(fact);
    }
    let others = paths
        .iter()
        .enumerate()
        .filter(|(index, _)| *index != path_index)
        .map(|(_, other)| {
            other
                .facts()
                .iter()
                .map(|fact| fact.proposition())
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let mut listed = BTreeSet::new();
    let mut cases = Vec::new();
    for fact in path.facts().iter().map(|fact| fact.proposition()) {
        if is_condition(fact)
            && !entry.contains(fact)
            && others.iter().any(|other| !other.contains(fact))
            && listed.insert(fact)
        {
            cases.push(fact.clone());
        }
    }
    cases
}

/// Serializes retained checked Proof lineage as surface steps. This is a
/// structural serialization, not a semantic search or reconstruction.
fn surface_steps_from_checked_proof(proof: &Proof<'_>) -> Result<Vec<ProofStep>, ClickError> {
    ProofCertificate::from_steps(proof.certificate().steps().to_vec())
        .map(ProofCertificate::into_steps)
}

pub(super) fn proof_case_fact_conflicts(
    fact: &Proposition,
    assumptions: &PureFactContext,
) -> Result<bool, ()> {
    let conflicts = fact_conflicts_with_assumptions(fact, assumptions);
    if conflicts && crate::kernel::pure_fact_context_is_inconsistent(assumptions) {
        return Err(());
    }
    Ok(conflicts)
}

/// One claim's own proof after execution, opened by a goal refinement and
/// continued by the tactics after it.
struct OpenedClaimProof<'a> {
    claim_index: usize,
    surface_goal: ClickProposition,
    proof: Proof<'a>,
    /// An `intro` opened a scope: a later `have` extends this proof, and a
    /// closer that does not apply to it is read against the claims instead.
    /// A proof only `choose` or `witness` opened commits to that
    /// choice, so a closer that does not apply to it is an error: reading it
    /// against the claims could close one without the witness.
    introduces_scope: bool,
}

impl<'a> OpenedClaimProof<'a> {
    fn with_proof(&self, proof: Proof<'a>) -> Self {
        Self {
            claim_index: self.claim_index,
            surface_goal: self.surface_goal.clone(),
            proof,
            introduces_scope: self.introduces_scope,
        }
    }

    /// Whether a closer that does not apply here is read against the claims.
    fn falls_back_on_miss(&self) -> bool {
        self.introduces_scope
    }
}

/// The root each claim of an outcome path is focused from: the path's
/// evolving outcome `Proof`. A path that returned always has one; a path
/// that threw, diverged or failed may have none.
fn outcome_claim_root<'a>(
    outcome_proof: &Option<Proof<'a>>,
    outcome: &FunctionOutcome,
    proof_label: &str,
    path_index: usize,
) -> Result<Option<Proof<'a>>, ClickError> {
    match (outcome_proof.as_ref(), outcome) {
        (Some(evolving), _) => Ok(Some(evolving.clone())),
        (None, FunctionOutcome::Return { .. }) => Err(ClickError::new(format!(
            "`{proof_label}` path {path_index}: missing retained outcome Proof"
        ))),
        (
            None,
            FunctionOutcome::Throw { .. }
            | FunctionOutcome::VerificationDiverges
            | FunctionOutcome::UndefinedBehavior(_)
            | FunctionOutcome::RuntimeError(_),
        ) => Ok(None),
    }
}

/// Plans the certificate a post-execution `arithmetic using` cites on a
/// fresh claim goal and applies it. The outer error refuses the step: a
/// premise that does not lower or is not exactly available. The inner
/// result is the step's own outcome.
fn apply_post_execution_arithmetic_using<'a>(
    focused: &Proof<'a>,
    surface_premises: &[ClickProposition],
) -> Result<Result<Proof<'a>, ClickError>, ClickError> {
    let kernels = surface_premises
        .iter()
        .map(|premise| {
            focused.lower_cited_surface_proposition(premise, "post-execution arithmetic premise")
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (premise_index, premise) in kernels.iter().enumerate() {
        if !focused
            .facts()
            .listed_premise_available(premise, &[], false)
        {
            return Err(focused.step_error(format!(
                "post-execution `solve() using` premise {premise_index} is not exactly available"
            )));
        }
    }
    Ok((|| -> Result<_, ClickError> {
        let goal = focused.goal().ok_or_else(|| {
            focused.step_error("post-execution arithmetic requires a proposition goal")
        })?;
        let surface_goal = focused.surface_goal().ok_or_else(|| {
            focused.step_error("post-execution arithmetic requires a source goal")
        })?;
        let pairs = kernels
            .into_iter()
            .zip(surface_premises.iter().cloned())
            .collect::<Vec<_>>();
        let kernel_premises = pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        if crate::kernel::proof::arithmetic_special::signed_definedness_query(goal).is_some() {
            return crate::kernel::search::ProofSearch::try_restricted_signed_definedness_closure(
                focused, &pairs,
            )?
            .ok_or_else(|| {
                focused
                    .step_error("post-execution signed definedness needs explicit operand bounds")
            });
        }
        use crate::surface::checking::ArithmeticPlan;
        let plan = crate::surface::checking::arithmetic_plans(goal, &kernel_premises, false)
            .next()
            .ok_or_else(|| {
                focused.step_error("post-execution arithmetic step could not be constructed")
            })?;
        match plan {
            ArithmeticPlan::Special(plan) => {
                let certificate = crate::surface::checking::special_plan_to_surface(
                    &plan,
                    surface_premises,
                    surface_goal,
                );
                let plan = &certificate;
                return crate::kernel::search::ProofSearch::apply_specialized_composition(
                    focused, plan,
                )?
                .ok_or_else(|| {
                    focused.step_error(
                        "post-execution specialized arithmetic needs explicit intermediate facts",
                    )
                });
            }
            ArithmeticPlan::IntegerAffine(plan) => {
                let retained_state = surface_program_point_selector(surface_goal);
                let integer_pairs = if let Some(selector) = retained_state {
                    pairs
                        .iter()
                        .map(|(kernel, surface)| {
                            surface_at_program_point(surface, &selector)
                                .map(|anchored| (kernel.clone(), anchored))
                        })
                        .collect::<Result<Vec<_>, _>>()
                        .map_err(|error| {
                            focused.step_error(format!(
                                "post-execution Integer premise state could not be serialized: {error}"
                            ))
                        })?
                } else {
                    pairs.clone()
                };
                if let Some(closed) = attempt::candidate_outcome(
                    crate::kernel::search::ProofSearch::apply_integer_composition(
                        focused,
                        &plan,
                        &integer_pairs,
                        surface_goal,
                        &[],
                    ),
                )?
                .flatten()
                {
                    return Ok(closed);
                }
                Err(focused
                    .step_error("post-execution Integer arithmetic needs an ordinary composition"))
            }
            ArithmeticPlan::SignedInt32(plan) => {
                let certificate = focused
                    .signed_plan_to_surface(&plan, &pairs, surface_goal)
                    .ok_or_else(|| {
                        focused.step_error(
                            "post-execution signed arithmetic step could not be transcribed",
                        )
                    })?;
                return crate::kernel::search::ProofSearch::apply_signed_interval_composition(
                    focused,
                    &certificate,
                )?
                .ok_or_else(|| {
                    focused.step_error(
                        "post-execution signed arithmetic needs explicit intermediate bounds",
                    )
                });
            }
        }
    })())
}

/// Supplies missing ordinary output tokens with the same checked step that
/// expansion will write at the return.
fn prepare_produced_tokens<'a>(
    function: &ProgramFunction,
    claims: &[FunctionClaimRef<'_>],
    closures: &[ClaimClosure<'_>],
    outcome: &mut FunctionOutcome,
    outcome_proof: &mut Option<Proof<'a>>,
    surface_closers: &mut Vec<ProofTactic>,
) -> Result<(), ClickError> {
    if function.resource_constructors().is_empty() || super::proof_object::implicit_solve_disabled()
    {
        return Ok(());
    }
    for (claim, closure) in claims.iter().zip(closures) {
        if closure.is_closed()
            || !matches!(claim.key(), FunctionContractClaimKey::Ensure(_))
            || claim.clause().borrowed()
        {
            continue;
        }
        let Ensure::Resource(
            resource @ ResourceClause::Declared {
                access: crate::surface::ResourceAccessMode::Own,
                kind: crate::surface::ResourceKind::Token,
                name,
                ..
            },
        ) = claim.clause().ensure()
        else {
            continue;
        };
        if !function
            .contract_interface()
            .is_ordinary_abstract_family(name)
        {
            continue;
        }
        let FunctionOutcome::Return { state, value } = &*outcome else {
            return Ok(());
        };
        let current = required_outcome(outcome_proof)?;
        let ProofContext::Execution(context) = current.context.as_ref() else {
            continue;
        };
        let (guard, deferred) = current.outcome_resource_guard(function, claim.key())?;
        if guard == Some(false) || deferred {
            continue;
        }
        let Ok(expected) = lower_resource_clause_at_state_with_result(
            resource,
            context.parameter_binding(),
            state,
            &value.native(),
        ) else {
            continue;
        };
        if state
            .resources()
            .satisfies_fact(&expected, current.facts().assumptions())
        {
            continue;
        }

        // The token fold checks that this exact token is authorized.
        let before = current.checkpoint();
        let step = ProofStep::FoldResource(resource.clone());
        let Ok(constructed) = current.driver().apply_step(step) else {
            check_verification_deadline()?;
            continue;
        };
        *outcome = constructed.focused_outcome_state()?;
        surface_closers.extend(constructed.certificate_since(&before)?.to_proof_tactics());
        *outcome_proof = Some(constructed);
    }
    Ok(())
}

/// Folds each open resource claim of a returned path whose fold checks on
/// the path's outcome `Proof`, recording the fold for expansion as a
/// written `fold` after execution is recorded.
#[allow(clippy::too_many_arguments)]
fn fold_produced_resources<'a>(
    claims: &[FunctionClaimRef<'_>],
    closures: &[ClaimClosure<'_>],
    outcome: &mut FunctionOutcome,
    outcome_proof: &mut Option<Proof<'a>>,
    capturing_this_tactic: bool,
    path_grouped_surface_closers: &mut Vec<ProofTactic>,
    path_deferred_capture_tactics: &mut Vec<ProofTactic>,
) -> Result<(), ClickError> {
    for (claim_index, claim) in claims.iter().enumerate() {
        if closures[claim_index].is_closed() {
            continue;
        }
        let Ensure::Resource(resource) = claim.clause().ensure() else {
            continue;
        };
        let fold = ProofTactic::FoldResource(resource.clone());
        let Some(step) = SourceContext::PostExecution.leaf_step(&fold) else {
            continue;
        };
        let current = required_outcome(outcome_proof)?;
        // Direct abstract outputs use the separate guarded preparation above.
        if let ResourceClause::Declared { name, .. } = resource
            && let ProofContext::Execution(context) = current.context.as_ref()
            && context
                .function
                .contract_interface()
                .is_ordinary_abstract_family(name)
        {
            continue;
        }
        // An already-held exact resource needs no new fold or certificate
        // node. This lookup only selects whether to attempt a new operation.
        if let (ProofContext::Execution(context), FunctionOutcome::Return { state, value }) =
            (current.context.as_ref(), &*outcome)
            && let Ok(held) = lower_resource_clause_at_state_with_result(
                resource,
                context.parameter_binding(),
                state,
                &value.native(),
            )
            && state.resources().contains_exact_representation(&held)
        {
            continue;
        }
        let before = current.checkpoint();
        let Ok(folded) = current.driver().apply_step(step) else {
            check_verification_deadline()?;
            continue;
        };
        *outcome = folded.focused_outcome_state()?;
        let added = folded.certificate_since(&before)?.to_proof_tactics();
        if capturing_this_tactic {
            path_deferred_capture_tactics.extend(added.iter().cloned());
        }
        // Folding changes the shared outcome before any claim closes. Its
        // checked steps belong to the path prefix for individual claims too.
        path_grouped_surface_closers.extend(added);
        *outcome_proof = Some(folded);
    }
    Ok(())
}

/// Closes claims after execution with written or implicit `solve`, or
/// with `solve() using`: a claim proof the
/// earlier tactics opened, a divergent path's claims, the claims of a
/// grouped proof together, and then each claim on its own. `Ok(())` means
/// the path's tactics continue after this closer; a closer that leaves a
/// claim it acts on open is refused.
#[allow(clippy::too_many_arguments)]
fn close_post_execution_claims_with_solve<'a, 'e>(
    post_tactic: &PostExecutionTactic,
    deferred: &DeferredPostExecutionTactic,
    tactic_index: &usize,
    path_index: usize,
    proof_label: &str,
    require_explicit_closers: bool,
    function_block: &std::sync::Arc<FunctionBlock>,
    parsed_function: &crate::languages::interface::ImportedFunction,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    claims: &[FunctionClaimRef<'_>],
    spec_definitions: SpecDefinitions<'_>,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    contract_pre_state: &ExecutionState,
    proof_context: &ExecutionProofContext<'_>,
    execution: &FunctionExecutionCandidates,
    completed_execution: &'e CheckedFunctionExecution,
    entry_pure_facts: &PureFactList,
    path_capture: Option<&DeferredTacticCapture>,
    path_requirements: &PureFactStore,
    rewrite_claim_equalities: &[Vec<ClickProposition>],
    rewritten_claim_proofs: &[Option<(Proof<'a>, ProofCheckpoint<'a>)>],
    outcome: &mut FunctionOutcome,
    outcome_proof: &mut Option<Proof<'a>>,
    opened_claim: &mut Option<OpenedClaimProof<'a>>,
    closures: &mut Vec<ClaimClosure<'e>>,
    resource_transition_applied: &mut bool,
    pending_resource_transition_error: &mut Option<String>,
    path_surface_post_tactics: &mut Vec<ProofTactic>,
    path_grouped_surface_closers: &mut Vec<ProofTactic>,
    path_deferred_capture_tactics: &mut Vec<ProofTactic>,
) -> Result<(), ClickError> {
    let restricted_premises = match post_tactic {
        PostExecutionTactic::SolveUsing(solve) => Some(solve.premises.as_slice()),
        _ => None,
    };
    let closer_name = if restricted_premises.is_some() {
        "solve() using"
    } else if matches!(post_tactic, PostExecutionTactic::ImplicitSolve) {
        "implicit tail"
    } else {
        "solve"
    };
    // An implicit tail schedules the same solver for each pending claim.
    let implicit_closer = matches!(post_tactic, PostExecutionTactic::ImplicitSolve);
    // The closer an omitted one stands for has
    // nothing to do on a path whose own tactics
    // already closed every claim.
    if implicit_closer && closures.iter().all(|closure| closure.is_closed()) {
        return Ok(());
    }
    // A written solve selects one goal; the implicit tail schedules all goals.
    let main_claim = main_goal_claim(outcome_proof, closures)?;
    let acts_on = |claim_index: usize| implicit_closer || Some(claim_index) == main_claim;
    let capturing_this_tactic =
        path_capture.is_some_and(|capture| capture.tactic_index == *tactic_index);
    // Written and implicit unrestricted solves prepare resource outputs.
    // A refused construction or fold leaves ownership unchanged, so the
    // claim check can report the missing resource.
    if restricted_premises.is_none()
        && !*resource_transition_applied
        && matches!(outcome, FunctionOutcome::Return { .. })
    {
        // An individual claim keeps its own closer, so retain construction
        // in the path's preceding tactics to replay it before that closer.
        let construction_tactics = if proof_context.constants.grouped_contract {
            &mut *path_grouped_surface_closers
        } else {
            path_surface_post_tactics
        };
        let before_construction = construction_tactics.len();
        prepare_produced_tokens(
            function,
            claims,
            closures,
            outcome,
            outcome_proof,
            construction_tactics,
        )?;
        if capturing_this_tactic {
            path_deferred_capture_tactics
                .extend(construction_tactics[before_construction..].iter().cloned());
        }
        fold_produced_resources(
            claims,
            closures,
            outcome,
            outcome_proof,
            capturing_this_tactic,
            path_grouped_surface_closers,
            path_deferred_capture_tactics,
        )?;
    }
    // Read the outcome's resources through the
    // contract's checked transition before closing
    // claims against it, so a produced or returned
    // resource is visible to a resource ensure with
    // no `frame`. The kernel certified this exit
    // already; a transition that does not apply yet
    // (an open composite still to fold) leaves the
    // body's own context in place.
    if !*resource_transition_applied
        && matches!(
            outcome,
            FunctionOutcome::Return { .. } | FunctionOutcome::Throw { .. }
        )
        && !crate::kernel::program_function_return_resources_definitionally_established(
            pre_state,
            function,
            arguments,
            outcome,
            &assumptions_from_propositions(path_requirements),
        )
    {
        // The body does not hold what the contract
        // returns; the resource ensures report the
        // missing fact against the body's context.
        *pending_resource_transition_error = Some(
            "the body outcome does not establish the contract's returned resources".to_string(),
        );
    } else if !*resource_transition_applied
        && matches!(
            outcome,
            FunctionOutcome::Return { .. } | FunctionOutcome::Throw { .. }
        )
    {
        match required_outcome(outcome_proof)?.apply_outcome_contract_resources(pre_state, function)
        {
            Ok(transitioned) => {
                *outcome = transitioned.focused_outcome_state()?;
                *resource_transition_applied = true;
                *outcome_proof = Some(transitioned);
            }
            Err(error) => {
                *pending_resource_transition_error = Some(error.raw_summary().to_string());
            }
        }
    }
    let opened_closure = match take_opened_claim(opened_claim, closures) {
        None => None,
        Some(opened) => {
            let claim_index = opened.claim_index;
            let proof = opened
                .proof
                .refresh_outcome_from(required_outcome(outcome_proof)?)?;
            // The tactics before this `solve` opened the
            // claim's proof; what `solve` itself adds is
            // only what follows them.
            let before_solve = proof.checkpoint();
            let selected = if let Some(premises) = restricted_premises {
                let selected = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(proof),
                    premises,
                );
                check_verification_deadline()?;
                selected
            } else if let Some(completed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))?
            {
                Some(completed)
            } else {
                crate::kernel::search::ProofSearch::try_solve_closure(&(proof))?
            };
            match selected {
                Some(completed) => Some((claim_index, before_solve, completed)),
                None if opened.falls_back_on_miss() => {
                    *opened_claim = Some(opened.with_proof(proof));
                    None
                }
                None => {
                    let claim_label = function_claim_label(function_block, &claims[claim_index]);
                    return Err(ClickError::new(format!(
                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `{closer_name}` did not complete the retained claim proof for `{claim_label}`"
                    )).with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch));
                }
            }
        }
    };
    if let Some((claim_index, before_solve, completed)) = opened_closure {
        if !completed.is_complete() {
            return Err(ClickError::new(format!(
                "`{proof_label}` path {path_index}, tactic {tactic_index}: retained claim proof remained incomplete after `solve`"
            )));
        }
        // The steps are checked inside the proof
        // the earlier tactics opened, so `solve`
        // stands for what it adds there, in the
        // claim's surface proof and in its own
        // expansion alike.
        let added = completed
            .certificate_since(&before_solve)?
            .to_proof_tactics();
        if capturing_this_tactic {
            path_deferred_capture_tactics.extend(added.iter().cloned());
        }
        // A grouped proof's expansion is written
        // from the path's closers, so what `solve`
        // added to the opened claim belongs there
        // too; otherwise the expanded proof stops
        // at the tactic that opened the claim.
        path_grouped_surface_closers.extend(added.iter().cloned());
        record_claim_closure(
            outcome_proof,
            closures,
            claims,
            completed_execution,
            path_index,
            claim_index,
            ClaimClosure::by_continued_proposition(
                claims[claim_index].key(),
                path_index,
                Vec::new(),
                completed.completed_proposition()?,
            ),
        )?;
        return Ok(());
    }
    // A divergent path has no outcome to prove
    // claims against. Its checked execution theorem
    // supplies vacuity evidence for each selected claim.
    if matches!(&outcome, FunctionOutcome::VerificationDiverges) {
        let certificate = ProofCertificate::from_proof_tactics(&[
            ProofTactic::Known,
        ])
        .map_err(|error| {
            ClickError::new(format!(
                "`{proof_label}` path {path_index}, tactic {tactic_index}: divergence produced an invalid known certificate: {error}"
            ))
        })?;
        for (claim_index, closure) in closures.iter_mut().enumerate() {
            if closure.is_closed() || !acts_on(claim_index) {
                continue;
            }
            *closure = ClaimClosure::vacuous(
                completed_execution,
                path_index,
                claims[claim_index].key(),
                ClaimCertificate::Claim(certificate.to_proof_tactics()),
            )?;
            if proof_context.constants.grouped_contract {
                path_grouped_surface_closers.extend(certificate.to_proof_tactics());
            }
            if capturing_this_tactic {
                path_deferred_capture_tactics.extend(certificate.to_proof_tactics());
            }
        }
        return Ok(());
    }
    // A trailing `solve` after execution may have
    // no contract work left (for example, a
    // resource-only release whose `frame` already
    // discharged every obligation).  Treat that as
    // the empty Proof transition instead of
    // constructing a legacy exit context solely to
    // discover an empty pending set.
    if claims
        .iter()
        .enumerate()
        .all(|(claim_index, _)| closures[claim_index].is_closed())
    {
        return Ok(());
    }
    // Plan claim scopes on the same retained outcome. A
    // bounded miss leaves that immutable ancestor intact.
    if let FunctionOutcome::Return { .. } | FunctionOutcome::Throw { .. } = &outcome {
        let mut direct_claims = Vec::new();
        // Exact resource checks return evidence separately
        // from the proposition scopes in this group.
        let mut direct_resource_claims = Vec::new();
        let mut direct_resource_evidence = BTreeMap::new();
        for (claim_index, claim) in claims.iter().enumerate() {
            if closures[claim_index].is_closed() || !acts_on(claim_index) {
                continue;
            }
            {
                let ensure_clause = claim.clause();
                {
                    match ensure_clause.ensure() {
                        Ensure::Proposition(surface_goal) => {
                            // A rewritten claim proves the
                            // original form with its
                            // recorded rewrites proof_candidate
                            // inside the checked scope.
                            direct_claims.push((
                                claim_index,
                                surface_goal.clone(),
                                rewrite_claim_equalities[claim_index].clone(),
                            ));
                        }
                        Ensure::Resource(resource) => {
                            direct_resource_claims.push((
                                claim_index,
                                resource.clone(),
                                ensure_clause.borrowed(),
                            ));
                        }
                    }
                }
            }
        }
        if !direct_resource_claims.is_empty() {
            for (claim_index, _, _) in &direct_resource_claims {
                let claim_label = function_claim_label(function_block, &claims[*claim_index]);
                let checked = required_outcome(outcome_proof)?.check_outcome_resource_claim(completed_execution, claims[*claim_index]).map_err(|error| {
                    if error.kind() == ClickErrorKind::Internal {
                        return error;
                    }
                    error.with_prefix(format!(
                        "`{proof_label}` path {path_index} left `{claim_label}` unproved; establish the facts and resources it needs before the end of the proof (claim index {claim_index})\nlast closing attempt:\n"
                    ))
                })?;
                direct_resource_evidence.insert(*claim_index, checked);
            }
        }
        if direct_claims.is_empty() && !direct_resource_claims.is_empty() {
            let tactics = direct_resource_evidence
                .values()
                .map(|_| ProofTactic::Known)
                .collect::<Vec<_>>();
            let certificate =
                ProofCertificate::from_proof_tactics(&tactics)
                    .map_err(|error| {
                        ClickError::new(format!(
                            "`{proof_label}` path {path_index}, tactic {tactic_index}: resource `solve` produced an invalid surface certificate: {error}"
                        ))
                    })?;
            if proof_context.constants.grouped_contract {
                for (claim_index, _, _) in &direct_resource_claims {
                    record_claim_closure(
                        outcome_proof,
                        closures,
                        claims,
                        completed_execution,
                        path_index,
                        *claim_index,
                        ClaimClosure::resource(
                            ClaimCertificate::GroupedTransition,
                            direct_resource_evidence
                                .remove(claim_index)
                                .ok_or_else(|| {
                                    ClickError::new(
                                        "grouped resource claim is missing its checked evidence",
                                    )
                                })?,
                        ),
                    )?;
                }
                path_grouped_surface_closers.extend(certificate.to_proof_tactics());
            } else {
                for (claim_index, _, _) in &direct_resource_claims {
                    record_claim_closure(
                        outcome_proof,
                        closures,
                        claims,
                        completed_execution,
                        path_index,
                        *claim_index,
                        ClaimClosure::resource(
                            ClaimCertificate::Claim(certificate.to_proof_tactics()),
                            direct_resource_evidence
                                .remove(claim_index)
                                .ok_or_else(|| {
                                    ClickError::new(
                                        "resource claim is missing its checked evidence",
                                    )
                                })?,
                        ),
                    )?;
                }
            }
            if capturing_this_tactic {
                path_deferred_capture_tactics.extend(certificate.to_proof_tactics());
            }
            return Ok(());
        }
        if !direct_claims.is_empty() {
            let direct_certificate = crate::kernel::with_search_attempt_rollback(|| {
                let attempt = || -> Result<
                            Option<(
                                Proof<'_>,
                                ProofCertificate,
                                Vec<crate::kernel::proof::CheckedProposition>,
                            )>,
                            ClickError,
                        > {
            // The evolving outcome proof supplies
            // the grouped obligation root when the
            // path derived a goal; its outcome proof data
            // carries the statement-entry anchor.
            let mut direct_proof = required_outcome(outcome_proof)?.clone();

            // The grouped closure exports only
            // work after this checkpoint; earlier
            // drained tactics on an evolving root
            // are recorded by their own tactics.
            let direct_base = direct_proof.checkpoint();
            let mut selected = true;
            for (claim_index, surface_goal, equalities) in &direct_claims {
                // Each proposition gets its own scope. Any local unfolding
                // belongs inside that scope, exactly where replay runs it.
                let scope_surface_goal = surface_goal.clone();
                let mut scope = match direct_proof.driver().open_have(scope_surface_goal) {
                    Ok(scope) => scope,
                    Err(error) => {
                        if let Err(stop) = check_verification_deadline() {
                            return Err(direct_proof.attach_step_diagnostic(stop)
                                .with_unlowered_goal(describe_click_proposition(surface_goal)));
                        }
                        if !require_explicit_closers {
                            selected = false;
                            break;
                        }
                        // A claim whose goal cannot be stated never
                        // closes. Its own refusal names it and the
                        // lowering error; the other claims of the group,
                        // which it would otherwise leave unclosed, are
                        // not reported.
                        let claim_label =
                            function_claim_label(function_block, &claims[*claim_index]);
                        let reason = match outcome_proof.as_ref() {
                            Some(root) => close_claim_directly_from_outcome(
                                root,
                                function,
                                &claims[*claim_index],
                                pre_state,
                                outcome,
                                surface_goal,
                                equalities,
                                &claim_label,
                                path_index,
                                &*entry_pure_facts,
                                execution.paths(),
                                parameter_binding,
                                spec_definitions,
                                ClaimClosureSearch::None,
                                None,
                            )?
                            .err(),
                            None => None,
                        };
                        return Err(reason.unwrap_or(error).with_context(format!(
                            "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `{closer_name}` did not retain a complete transition for every pending claim"
                        )));
                    }
                };
                let mut rewrites_applied = true;
                for equality in equalities {
                    match scope.driver().apply_step(ProofStep::Rewrite(
                        equality.clone(),
                    )) {
                        Ok(next) => scope = next,
                        Err(_) => {
                            check_verification_deadline()?;
                            rewrites_applied = false;
                            break;
                        }
                    }
                }
                if !rewrites_applied {
                    selected = false;
                    break;
                }
                let mut search = attempt::search_scope("checked outcome closure");
                let (selected_scope, checks) = crate::surface::proof_diagnostics::capture_check_observations(|| -> Result<_, ClickError> {
                    Ok(if let Some(premises) = restricted_premises {
                    let selected = (scope).driver().try_restricted_solve_closure(premises);
                    check_verification_deadline()?;
                    selected
                } else if let Some(scope) = (scope).driver().try_direct_logical_closure()? {
                    Some(scope)
                } else {
                    (scope).driver().try_solve_closure()?
                })
                });
                let selected_scope = match selected_scope {
                    Ok(selected) => selected,
                    Err(error) => return Err(scope.body().attach_step_diagnostic(error)
                        .with_check_observations(checks)
                        .with_search_failures(search.finish())),
                };
                let Some(scope) = selected_scope else {
                    check_verification_deadline()
                        .map_err(|error| scope.body().attach_step_diagnostic(error))?;
                    if !require_explicit_closers {
                        selected = false;
                        break;
                    }
                    let claim_index = direct_claims
                        .iter()
                        .find(|(_, candidate, _)| {
                            candidate == surface_goal
                        })
                        .map(|(claim_index, _, _)| *claim_index)
                        .expect("the scope goal came from direct_claims");
                    let claim_label = function_claim_label(function_block, &claims[claim_index],
                    );
                    // A restricted miss must stay restricted even
                    // while explaining it: do not launch an
                    // ambient proof search for diagnostic detail.
                    let detail = match (restricted_premises, outcome_proof.as_ref()) {
                        (Some(_), _) => "\nThe current goal could not be proved from only the listed premises.".to_string(),
                        (None, Some(root)) => close_claim_directly_from_outcome(
                            root,
                            function,
                            &claims[claim_index],
                            pre_state,
                            outcome,
                            surface_goal,
                            equalities,
                            &claim_label,
                            path_index,
                            &*entry_pure_facts,
                            execution.paths(),
                            parameter_binding,
                            spec_definitions,
                            ClaimClosureSearch::None,
                            Some(scope.body()),
                        )?
                        .err()
                        .map(|reason| format!("\n{}", reason.raw_summary()))
                        .unwrap_or_default(),
                        (None, None) => String::new(),
                    };
                    let transition_detail = pending_resource_transition_error
                        .as_ref()
                        .map(|error| {
                            format!(
                                "\nthe contract resource transition did not apply to this outcome: {error}"
                            )
                        })
                        .unwrap_or_default();
                    return Err(scope.body().step_error(format!(
                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `{closer_name}` search did not retain a complete proof for `{claim_label}`{detail}{transition_detail}",
                    )).with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch).with_check_observations(checks).with_search_failures(search.finish()));
                };
                search.succeed();
                let joined = scope.join()?;
                direct_proof = joined;
            }
            if !selected {
                return Ok(None);
            }
            let mut surface_goals = Vec::new();
            for (_, goal, _) in &direct_claims {
                surface_goals.push(goal.clone());
            }
            let completed = if surface_goals.is_empty() {
                (
                    direct_proof.certificate_since(&direct_base)?,
                    Vec::new(),
                )
            } else {
                let mut claim_goal_context = None;
                let claim_goals = direct_claims
                    .iter()
                    .map(|(claim_index, _, _)| {
                        contract_closing_goal_forms(
                            function,
                            proof_context.constants.entry_context.as_ref().map(|entry| entry.cases.closing_entry()),
                            outcome_proof.as_ref().and_then(Proof::claim_goals).and_then(|goals| goals.target(&claims[*claim_index].key())),
                            contract_pre_state,
                            arguments,
                            outcome,
                            &assumptions_from_propositions(
                                path_requirements,
                            ),
                            &mut claim_goal_context,
                        ).map(|forms| forms.into_iter().flatten().collect())
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                direct_proof.driver().complete_fixed_state_obligations_since(
                    &direct_base,
                    &surface_goals,
                    &claim_goals,
                    &direct_claims.iter().map(|(index, _, _)| claims[*index].key()).collect::<Vec<_>>(),
                )?
            };
            // Keep the checked authority for the original claims,
            // but close the rewritten goals in the expanded proof.
            // Prefer `known` for the residuals, keeping the legacy normalizer
            // only when a goal needs its broader rules. With
            // resource claims, keep the ordinary `known` closers: they
            // follow contract order, whose next goal may be ownership.
            if proof_context.constants.grouped_contract
                && direct_resource_claims.is_empty()
                && !direct_claims.is_empty()
                && let Some(closer) = [ProofStep::Known, ProofStep::Normalize]
                    .into_iter()
                    .find(|closer| direct_claims.iter().all(|(index, _, _)| {
                        rewritten_claim_proofs[*index]
                            .as_ref()
                            .is_some_and(|(proof, _)| {
                                proof.driver().apply_step(closer.clone()).is_ok()
                            })
                    }))
            {
                let mut tactics = direct_proof
                    .certificate_since(&direct_base)?
                    .to_proof_tactics();
                // Each written closer discharges only the next claim.
                tactics.extend(std::iter::repeat_n(closer.to_proof_tactic(), direct_claims.len()));
                let certificate = ProofCertificate::from_proof_tactics(&tactics)
                    .map_err(|error| ClickError::new(format!(
                        "checked residual closure is not simple: {error}"
                    )))?;
                return Ok(Some((direct_proof, certificate, completed.1)));
            }
            Ok(Some((direct_proof, completed.0, completed.1)))
                        };
                let outcome = attempt();
                let keep = matches!(&outcome, Ok(Some(_)));
                (outcome, keep)
            })?;
            if let Some((completed_root, certificate, checked_propositions)) = direct_certificate {
                *outcome_proof = Some(completed_root);
                if checked_propositions.len() != direct_claims.len() {
                    return Err(ClickError::new(format!(
                        "`{proof_label}` path {path_index}, tactic {tactic_index}: completed proposition authority did not match the checked claim set"
                    )));
                }
                // Each exact resource witness owns its
                // claim key. Serialize its explicit closer
                // after the checked proposition scopes.
                let certificate = if direct_resource_claims.is_empty() {
                    certificate
                } else {
                    let mut tactics = certificate.to_proof_tactics();
                    tactics.extend(
                        direct_resource_evidence
                            .values()
                            .map(|_| ProofTactic::Known),
                    );
                    ProofCertificate::from_proof_tactics(&tactics)
                        .map_err(|error| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped resource closer was invalid: {error}"
                            ))
                        })?
                };
                for ((claim_index, _, _), checked_proposition) in
                    direct_claims.into_iter().zip(checked_propositions)
                {
                    record_claim_closure(
                        outcome_proof,
                        closures,
                        claims,
                        completed_execution,
                        path_index,
                        claim_index,
                        ClaimClosure::by_grouped_proposition(
                            claims[claim_index].key(),
                            path_index,
                            &certificate,
                            checked_proposition,
                        ),
                    )?;
                }
                for (claim_index, _, _) in &direct_resource_claims {
                    record_claim_closure(
                        outcome_proof,
                        closures,
                        claims,
                        completed_execution,
                        path_index,
                        *claim_index,
                        ClaimClosure::resource(
                            ClaimCertificate::GroupedTransition,
                            direct_resource_evidence
                                .remove(claim_index)
                                .ok_or_else(|| {
                                    ClickError::new(
                                        "grouped resource claim is missing its checked evidence",
                                    )
                                })?,
                        ),
                    )?;
                }
                path_grouped_surface_closers.extend(certificate.to_proof_tactics());
                if capturing_this_tactic {
                    path_deferred_capture_tactics.extend(certificate.to_proof_tactics());
                }
                return Ok(());
            }
        }
    }
    // A claim of a per-claim proof that the scopes
    // above did not close is tried as its own
    // kernel goal, with the facts the kernel
    // lowered it under, as the implicit closer at
    // the end of the proof tries it. A restricted
    // `solve` still cites only its listed premises.
    if !require_explicit_closers {
        let search = match restricted_premises {
            Some(premises) => ClaimClosureSearch::Restricted(premises),
            None => ClaimClosureSearch::Solve,
        };
        for (claim_index, claim) in claims.iter().enumerate() {
            if closures[claim_index].is_closed() || !acts_on(claim_index) {
                continue;
            }
            let Some(root) = outcome_proof.clone() else {
                continue;
            };
            let Ensure::Proposition(surface_goal) = claim.clause().ensure() else {
                continue;
            };
            let claim_label = function_claim_label(function_block, claim);
            let completed = match close_claim_directly_from_outcome(
                &root,
                function,
                claim,
                pre_state,
                outcome,
                surface_goal,
                &rewrite_claim_equalities[claim_index],
                &claim_label,
                path_index,
                entry_pure_facts,
                execution.paths(),
                parameter_binding,
                spec_definitions,
                search,
                None,
            )? {
                Ok(completed) => completed,
                Err(reason) => {
                    closures[claim_index].record_failure(reason);
                    continue;
                }
            };
            // The closure is the exact check the end
            // of the proof makes, so it prints no
            // steps: an expanded proof closes the
            // claim the same way.
            record_claim_closure(
                outcome_proof,
                closures,
                claims,
                completed_execution,
                path_index,
                claim_index,
                ClaimClosure::by_checked_proposition(
                    claim.key(),
                    path_index,
                    &completed.certificate(),
                    completed.completed_proposition()?,
                ),
            )?;
        }
    }
    if (0..claims.len())
        .all(|claim_index| closures[claim_index].is_closed() || !acts_on(claim_index))
    {
        return Ok(());
    }
    // The implicit `solve` at the end of a
    // per-claim proof leaves a claim it does not
    // close for the path-end check, which names
    // it. A written closer that leaves a claim it
    // acts on open is refused here.
    if !require_explicit_closers && deferred.source_index == usize::MAX {
        return Ok(());
    }
    let mut reasons = Vec::new();
    let mut searched = false;
    for (claim_index, claim) in claims.iter().enumerate() {
        if closures[claim_index].is_closed() || !acts_on(claim_index) {
            continue;
        }
        let Some(root) = outcome_proof.as_ref() else {
            continue;
        };
        let ensure_clause = claim.clause();
        let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
            continue;
        };
        if let Some(reason) = closures[claim_index].last_error()
            && reason.proof_refusal() == Some(crate::surface::ProofRefusal::UnsuccessfulSearch)
        {
            searched = true;
            reasons.push(reason.clone());
            continue;
        }
        let claim_label = function_claim_label(function_block, claim);
        if let Err(reason) = close_claim_directly_from_outcome(
            root,
            function,
            claim,
            pre_state,
            outcome,
            surface_goal,
            &rewrite_claim_equalities[claim_index],
            &claim_label,
            path_index,
            entry_pure_facts,
            execution.paths(),
            ParameterBinding::new(parsed_function.parameters(), arguments),
            spec_definitions,
            ClaimClosureSearch::None,
            None,
        )? {
            reasons.push(reason);
        }
    }
    let summary = format!(
        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `{closer_name}` did not retain a complete transition for every pending claim"
    );
    // One claim's refusal keeps its checked context: the goal and the
    // premises it saw.
    if reasons.len() == 1 && pending_resource_transition_error.is_none() {
        return Err(reasons.remove(0).with_context(summary));
    }
    let mut reasons = reasons
        .iter()
        .map(|reason| reason.raw_summary().to_owned())
        .collect::<Vec<_>>();
    if let Some(error) = &pending_resource_transition_error {
        reasons.push(format!(
            "the contract resource transition did not apply to this outcome: {error}"
        ));
    }
    let detail = if reasons.is_empty() {
        String::new()
    } else {
        format!("\n{}", reasons.join("\n"))
    };
    let error = ClickError::new(format!("{summary}{detail}"));
    Err(if searched {
        error.with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch)
    } else {
        error
    })
}

/// Takes the opened claim proof to continue, dropping one whose claim a
/// closer has since closed through the claims.
fn take_opened_claim<'a>(
    opened_claim: &mut Option<OpenedClaimProof<'a>>,
    closures: &[ClaimClosure],
) -> Option<OpenedClaimProof<'a>> {
    opened_claim
        .take()
        .filter(|opened| !closures[opened.claim_index].is_closed())
}

/// Continues the claim proof that earlier deferred tactics opened with a
/// closer, rather than starting over at the claims. `Ok(Some(certificate))`
/// means the closer applied there, with the checked steps it recorded: a
/// completed proof closes its claim, an incomplete one stays open. `Ok(None)`
/// means the caller reads the closer against the claims instead, because no
/// proof was open or because the closer did not apply to one that falls back
/// on a miss.
fn continue_outcome_claim_proof<'a>(
    opened_claim: &mut Option<OpenedClaimProof<'a>>,
    closures: &mut [ClaimClosure],
    claims: &[FunctionClaimRef<'_>],
    outcome_proof: &mut Option<Proof<'a>>,
    execution: &CheckedFunctionExecution,
    path_index: usize,
    apply: impl FnOnce(&Proof<'a>) -> Result<Proof<'a>, ClickError>,
) -> Result<Option<ProofCertificate>, ClickError> {
    let Some(opened) = take_opened_claim(opened_claim, closures) else {
        return Ok(None);
    };
    let claim_index = opened.claim_index;
    let refreshed = opened
        .proof
        .refresh_outcome_from(required_outcome(outcome_proof)?)?;
    let before = refreshed.checkpoint();
    match apply(&refreshed) {
        Ok(proof) => {
            let certificate = proof.certificate_since(&before)?;
            if proof.is_complete() {
                record_claim_closure(
                    outcome_proof,
                    closures,
                    claims,
                    execution,
                    path_index,
                    claim_index,
                    ClaimClosure::by_continued_proposition(
                        claims[claim_index].key(),
                        path_index,
                        Vec::new(),
                        proof.completed_proposition()?,
                    ),
                )?;
            } else {
                *opened_claim = Some(opened.with_proof(proof));
            }
            Ok(Some(certificate))
        }
        Err(_) if opened.falls_back_on_miss() => {
            *opened_claim = Some(opened.with_proof(refreshed));
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// Whether a post-execution leaf refines one claim's goal and so runs on that
/// claim's existence proof rather than on the path's outcome proof.
/// The main goal a written closer acts on after execution: the first open
/// claim, in contract order. A resource claim (`owns`, `produces`) is a goal
/// like a proposition claim; `known` closes it when the instance is held.
///
/// The outcome `Proof` holds the claim goals of a path that has one. A
/// divergent path has none, and its closures say which claims are open.
fn main_goal_claim(
    outcome_proof: &Option<Proof<'_>>,
    closures: &[ClaimClosure],
) -> Result<Option<usize>, ClickError> {
    match outcome_proof {
        Some(proof) => Ok(match proof.first_open_outcome_goal()? {
            Some(crate::kernel::proof::OutcomeGoal::Claim { position, .. }) => Some(position),
            Some(crate::kernel::proof::OutcomeGoal::Closing(_)) | None => None,
        }),
        None => Ok(closures.iter().position(|closure| !closure.is_closed())),
    }
}

fn focused_proposition_claim<'c>(
    root: &Proof<'_>,
    claims: &[FunctionClaimRef<'c>],
    tactic: &str,
) -> Result<(usize, &'c ClickProposition), ClickError> {
    let Some(crate::kernel::proof::OutcomeGoal::Claim { position, .. }) =
        root.first_open_outcome_goal()?
    else {
        return Err(root.step_error(format!("`{tactic}` requires an open claim")));
    };
    let Ensure::Proposition(goal) = claims[position].clause().ensure() else {
        return Err(root.step_error(format!(
            "`{tactic}` requires the focused claim to be a proposition"
        )));
    };
    Ok((position, goal))
}

/// Records a claim's closure on the path. On a path with an outcome `Proof`
/// it also closes that claim's goal there, so the outcome `Proof` decides
/// which claims are still open; a closure the goal refuses is an error.
fn record_claim_closure<'e>(
    outcome_proof: &mut Option<Proof<'_>>,
    closures: &mut [ClaimClosure<'e>],
    claims: &[FunctionClaimRef<'_>],
    execution: &CheckedFunctionExecution,
    path_index: usize,
    claim_index: usize,
    closure: ClaimClosure<'e>,
) -> Result<(), ClickError> {
    if let Some(proof) = outcome_proof.as_ref() {
        let key = claims[claim_index].key();
        let evidence = closure
            .require_evidence(execution, path_index, &key)?
            .goal_evidence()
            .ok_or_else(|| {
                proof.step_error("a path that reaches an outcome does not hold a claim vacuously")
            })?;
        *outcome_proof = Some(proof.close_claim_goal(&key, evidence)?);
    }
    closures[claim_index] = closure;
    Ok(())
}

/// A closer written when every proposition claim on the path is closed.
fn no_open_goal(closer: &str) -> String {
    format!("`{closer}` has no goal to close: every claim on this path is already closed")
}

fn opens_outcome_claim_scope(tactic: &ProofTactic) -> bool {
    matches!(
        tactic,
        ProofTactic::Choose(_)
            | ProofTactic::Witness(_)
            | ProofTactic::Intro
            | ProofTactic::IntroAs(_)
            | ProofTactic::IntroBinder(_)
            | ProofTactic::IntroBlock { .. }
    )
}

// A definition step focuses a claim only when it names an occurrence in that
// claim's current goal. Opening a premise remains an ordinary fact operation.
fn unfolds_outcome_goal(
    tactic: &ProofTactic,
    claims: &[FunctionClaimRef<'_>],
    closures: &[ClaimClosure],
    predicates: &PredicateEnvironment,
) -> bool {
    let target = match tactic {
        ProofTactic::UnfoldProposition(target) => target.clone(),
        ProofTactic::UnfoldFunction(application) if predicates.get(&application.name).is_some() => {
            ClickProposition::PredicateCall {
                name: application.name.clone(),
                arguments: application.arguments.clone(),
            }
        }
        _ => return false,
    };
    let mut goals = claims.iter().zip(closures).filter_map(|(claim, closure)| {
        if closure.is_closed() {
            return None;
        }
        match claim.clause().ensure() {
            Ensure::Proposition(goal) => Some(goal),
            _ => None,
        }
    });
    let Some(goal) = goals.next() else {
        return false;
    };
    if goals.next().is_some() {
        return false;
    }
    fn contains(goal: &ClickProposition, target: &ClickProposition) -> bool {
        if goal == target {
            return true;
        }
        match goal {
            ClickProposition::And(a, b)
            | ClickProposition::Or(a, b)
            | ClickProposition::Implies(a, b) => contains(a, target) || contains(b, target),
            ClickProposition::Not(body)
            | ClickProposition::At {
                proposition: body, ..
            }
            | ClickProposition::ForAll { body, .. }
            | ClickProposition::Exists { body, .. } => contains(body, target),
            _ => false,
        }
    }
    contains(goal, &target)
}

pub(super) fn finish_ordered_proof<'a>(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof: Proof<'a>,
    source_path: &str,
    function_block: &std::sync::Arc<FunctionBlock>,
    parsed_function: &crate::languages::interface::ImportedFunction,
    claims: &[FunctionClaimRef<'_>],
    require_explicit_closers: bool,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    _theorem_environment: &TheoremEnvironment,
    function_environment: &ExecutionEnvironment,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    certificate_tactics: &std::sync::Arc<[ProofTactic]>,
    claim_surface_builders: &mut Vec<(VerifiedClaim, std::sync::Arc<ProofCertificateBuilder>)>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let parameter_binding = ParameterBinding::new(parsed_function.parameters(), arguments);
    let obtain_ends = std::cell::OnceCell::new();
    let proof_label = if require_explicit_closers {
        function_block.contract_claim_label()
    } else {
        function_claim_label(function_block, &claims[0])
    };
    // The drain re-enters the proof-object substrate exactly once: the
    // terminal execution context becomes an execution-frontier `Proof` whose
    // typed outcome goals own each returning path's result, state, fact
    // context, and any effect selection not already consumed by a checked
    // frontier frame. This lets source-ordered result/resource operations run
    // before an explicit outcome frame without moving semantic authority back
    // into the drain. A context that is not at a returning function exit
    // derives no outcome substrate and finalizes through the same checked
    // view unchanged.
    // Derivation is unconditional: every result-aware tactic kind consumes
    // goals now, and the working-set parity invariant below must hold for
    // every drain before its working vector is finalized.
    let direct_view = proof.finalization_view()?;
    let (state, frontier, proof_execution, proof_context, branch_path) = (
        direct_view.state,
        direct_view.frontier,
        direct_view.execution,
        direct_view.context,
        direct_view.branch_path,
    );
    // Frontier-loop frame authority is established from the proof's original
    // entry context.  The terminal fact vector also contains body/post
    // observations, which may legitimately discharge later obligations but
    // must never make an entry-dependent resource transition evaluable.
    let entry_pure_facts = proof_context.constants.execution_start_facts.clone();
    proof_execution
        .core
        .validate_execution_evidence_shapes()
        .map_err(|message| ClickError::new(format!("{proof_label}: {message}")))?;
    let mut retained_surface = {
        let record = &proof_execution.presentation.surface_record;
        let mut retained = ProofCertificateBuilder {
            path_choices: record.path_choices.clone(),
            blocker: record.blocker.clone(),
            ..ProofCertificateBuilder::default()
        };
        retained.steps = surface_steps_from_checked_proof(&proof)?;
        retained
    };
    // Every certified path and every claim on it carries the same retained
    // certificate, so it is admitted once and shared. Rebuilding it per
    // (path, claim) made a finished proof cost the certificate's size times
    // the number of paths times the number of claims.
    let retained_certificate = retained_surface
        .blocker
        .is_none()
        .then(|| ProofCertificate::from_steps(retained_surface.steps.clone()))
        .transpose()?;
    let pre_state = frontier.execution_start_state(state);
    let frontier_function_block = (!proof_execution
        .presentation
        .frontier_loop_clauses
        .is_empty())
    .then(|| {
        function_block.with_bound_frontier_loop_clauses(
            &proof_execution.presentation.frontier_loop_clauses.to_vec(),
        )
    });
    let frontier_function = frontier_function_block
        .as_ref()
        .map(|frontier_function_block| {
            annotated_function_with_assumptions(
                frontier_function_block,
                parsed_function,
                pre_state,
                arguments,
                spec_definitions,
                resource_environment,
                Some(ResourceFrameEntry {
                    assumptions: &assumptions_from_propositions(&*entry_pure_facts),
                    checked_entry_state: proof_context.constants.function_entry_state.as_ref(),
                }),
                None,
            )
        })
        .transpose()?;
    let frontier_function_environment = (!proof_execution.core.frontier_loop_rules.is_empty())
        .then(|| {
            function_environment
                .clone()
                .with_verified_loop_rules(proof_execution.core.frontier_loop_rules.to_vec())
        });
    let function = frontier_function.as_ref().unwrap_or(function);
    let function_environment = frontier_function_environment
        .as_ref()
        .unwrap_or(function_environment);
    let claim_targets: BTreeMap<_, _> = function
        .contract_claims()
        .iter()
        // A proof-local clause may mention execution states, which cannot
        // occur in a reusable contract. Such a function has no modular
        // proposition contract to register: prove its source clauses as local
        // obligations. Never confuse failure to open a registered goal with
        // this decision, made from the function's declared contract support.
        .filter(|claim| {
            function.opaque_contract_supported()
                || !matches!(
                    claim.target(),
                    FunctionContractClaimTarget::EnsureProposition(_)
                        | FunctionContractClaimTarget::ExceptionalEnsureProposition(_)
                )
        })
        .map(|claim| {
            crate::instrumentation::record_deterministic_work(1);
            (claim.key().clone(), claim.target().clone())
        })
        .collect();
    let result = (|| {
        let execution = frontier.execution().ok_or_else(|| {
            ClickError::new(format!(
                "`{proof_label}` execution proof must reach function exit with `step()` or `step_until(function.exit)`"
            ))
        })?;
        let call_edges = proof_execution
            .presentation
            .call_outcome_edges
            .as_ref()
            .filter(|edges| edges.len() == execution.paths().len());
        if execution.paths().is_empty() {
            return Err(ClickError::new(format!(
                "execution proof could not prove any complete execution path for `{proof_label}`"
            )));
        }
        // Checked statement steps apply verified loop rules; a loop with no
        // rule can only be stepped concretely or avoided by a checked path.
        // Keep that semantics even when no loop was reached. Calling it
        // `Verify` in that case incorrectly suggests that an unreachable
        // frame-annotated loop might have been summarized.
        let execution_semantics = ExecutionSemantics::APPLY_VERIFIED_RULES;
        let execution_mode = if proof_execution.core.concrete_loop_execution {
            FunctionContractExecutionMode::ExecuteLoops
        } else {
            FunctionContractExecutionMode::VerifyLoops
        };
        // The proof object composes the checked execution from its retained
        // traces, every step of which it checked when recorded, under the
        // contract's own entry assumptions; every path carries its case
        // facts itself. Nothing executes the body again to decide whether
        // the proof was valid.
        let completed_execution = crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &proof_label,
            "proof completion",
            || {
                proof_execution
                    .core
                    .checked_function_execution(
                        execution,
                        function,
                        entry_pure_facts.context(),
                        function_environment.clone(),
                        execution_semantics,
                        execution_mode,
                    )
                    .map_err(|reason| {
                        ClickError::new(format!(
                            "`{proof_label}`: the proof object could not complete its checked function execution: {reason}"
                        ))
                    })
            },
        )?;
        let (mut outcome_substrate, _, outcome_branches) =
            proof.split_checked_function_outcomes(&completed_execution)?;
        let resource_prefix = claims
            .iter()
            .filter_map(|claim| match claim_targets.get(&claim.key()) {
                Some(FunctionContractClaimTarget::EnsureResource(index)) => Some(index + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        // ABI-generated resource claims (for example construction-return
        // storage) have no written clause or separate source proof. Once
        // this proof reaches the last written resource clause, include the
        // complete generated boundary too. With no written resource clauses,
        // that is the ordinary body proof's obligation.
        let last_written_resource = claim_targets
            .iter()
            .filter_map(|(key, target)| {
                crate::instrumentation::record_deterministic_work(1);
                match (key, target) {
                    (
                        FunctionContractClaimKey::Ensure(source_index),
                        FunctionContractClaimTarget::EnsureResource(index),
                    ) if *source_index < function_block.ensures().len() => Some(index + 1),
                    _ => None,
                }
            })
            .max()
            .unwrap_or(0);
        let resource_prefix = if resource_prefix >= last_written_resource {
            function.resource_ensures().len()
        } else {
            resource_prefix
        };
        let closing_context = crate::kernel::ContractClosingContext::for_resource_prefix(
            &completed_execution,
            resource_prefix,
        );
        let mut contract_owner = outcome_substrate.open_contract_execution(
            completed_execution.clone(),
            proof_context
                .constants
                .entry_context
                .as_ref()
                .and_then(|entry| entry.strategy_root.as_ref()),
            outcome_branches.values().copied(),
        )?;
        let mut verified = Vec::new();
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_grouped_closers_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_choices_by_path = Vec::with_capacity(execution.paths().len());
        // Distinct terminal outcomes can share one written execution leaf:
        // a summarized loop, or a scalar result decided at return. Keep a
        // post-execution selector only when both outcomes decide it below.
        let shared_terminal_leaf = execution.paths().len() == 2
            && !matches!(
                through_single_arm_matches(&retained_surface.steps).last(),
                Some(
                    ProofStep::If { .. }
                        | ProofStep::Match { .. }
                        | ProofStep::CallOutcomes { .. }
                        | ProofStep::Open { .. }
                )
            );
        let terminal_outcome_selector = (execution.paths().len() == 2
            && (0..2).all(|index| proof_execution.loop_return_proof(index).is_none())
            && (shared_terminal_leaf
                || (0..2).any(|index| {
                    proof_execution
                        .core
                        .pending_loop_return_loop_index(index)
                        .is_some()
                })))
        .then(|| {
            claims
                .iter()
                .find_map(|claim| match claim.clause().ensure() {
                    Ensure::Proposition(ClickProposition::Or(left, _)) => {
                        Some(left.as_ref().clone())
                    }
                    _ => None,
                })
                .or_else(|| {
                    shared_terminal_leaf
                        .then(|| {
                            claims
                                .iter()
                                .find_map(|claim| match claim.clause().ensure() {
                                    Ensure::Proposition(ClickProposition::Implies(left, _)) => {
                                        Some(left.as_ref().clone())
                                    }
                                    _ => None,
                                })
                        })
                        .flatten()
                })
                .or_else(|| {
                    // Conditional scalar values can split at return without
                    // a written C branch. Their guard distinguishes the
                    // outcomes; an earlier frame equality holds on both.
                    shared_terminal_leaf
                        .then(|| {
                            claims
                                .iter()
                                .find_map(|claim| match claim.clause().ensure() {
                                    Ensure::Proposition(ClickProposition::Comparison {
                                        left,
                                        right,
                                        ..
                                    }) => [left, right].into_iter().find_map(|expression| {
                                        match expression {
                                            ContractExpression::If { condition, .. } => {
                                                Some(condition.as_ref().clone())
                                            }
                                            _ => None,
                                        }
                                    }),
                                    _ => None,
                                })
                        })
                        .flatten()
                })
                .or_else(|| {
                    // A scalar return can fork without a written C branch.
                    // Its checked postcondition can select distinct endings
                    // just as an OR arm or implication guard does. Each
                    // outcome must independently decide opposite sides below.
                    shared_terminal_leaf
                        .then(|| {
                            claims
                                .iter()
                                .find_map(|claim| match claim.clause().ensure() {
                                    Ensure::Proposition(proposition) => Some(proposition.clone()),
                                    _ => None,
                                })
                        })
                        .flatten()
                })
        })
        .flatten();
        let mut terminal_outcome_choices = Vec::new();
        let mut loop_return_closures = Vec::new();
        let mut surface_post_path_indices = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_prefixes_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_branches_by_path = Vec::with_capacity(execution.paths().len());
        // Whether the implicit exact closer of a single-claim proof would
        // have discharged every open proposition claim on the path without
        // surface tactics. Consulted only when the captured expansions
        // disagree across paths (see the stitch below).
        let mut implicit_closure_by_path = Vec::with_capacity(execution.paths().len());
        let mut batch_capture_paths =
            BTreeMap::<usize, Vec<(usize, Vec<ProofTactic>, (usize, usize))>>::new();

        let mut batch_implicit_closure = BTreeMap::new();
        let mut batch_captures = proof_execution
            .presentation
            .expansion
            .batch_deferred_captures
            .clone();

        // Every theorem below carries this one execution until the finished
        // execution replaces it for all of them at once.
        let provisional_checked_execution = std::sync::Arc::new(completed_execution.clone());
        crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &proof_label,
            "execution path finishing",
            || -> Result<(), ClickError> {
                'execution_path: for (path_index, path) in execution.paths().iter().enumerate() {
                    let loop_return = proof_execution.loop_return_proof(path_index);
                    if let Some(returned) = loop_return {
                        for (index, capture) in &returned.batch_captures {
                            batch_captures.insert(*index, capture.clone());
                        }
                    }
                    let path_batch_captures = loop_return.map_or(
                        &proof_execution
                            .presentation
                            .expansion
                            .batch_deferred_captures,
                        |p| &p.batch_captures,
                    );
                    let path_capture = loop_return.and_then(|p| p.capture.as_ref()).or_else(|| {
                        if loop_return.is_none() {
                            proof_execution
                                .presentation
                                .expansion
                                .deferred_tactic_capture
                                .as_ref()
                        } else {
                            None
                        }
                    });
                    let post_execution_tactics = loop_return
                        .map_or(&proof_execution.presentation.post_execution_tactics, |p| {
                            &p.tactics
                        });
                    // Entry resource rewrites may precede the first C step.
                    // Contract `old` still denotes the original function entry,
                    // not the rewritten representation where execution began.
                    let contract_pre_state = proof_execution
                        .core
                        .function_entry
                        .as_ref()
                        .map_or(pre_state, |entry| entry.caller_state());
                    let _path_preparation_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "execution path preparation",
                    );
                    let focused_outcome = if let Some(goal) = outcome_branches.get(&path_index) {
                        Some(outcome_substrate.focus_branch(*goal)?)
                    } else if matches!(path.outcome(), FunctionOutcome::VerificationDiverges) {
                        None
                    } else {
                        // The outcome derivation rejected this candidate under
                        // an exact contradictory path fact; it owns no goal.
                        continue 'execution_path;
                    };
                    let mut path_grouped_surface_closers = Vec::new();
                    let mut path_surface_post_tactics = Vec::new();
                    let mut path_deferred_capture_tactics = Vec::new();
                    let mut path_deferred_capture_prefix = (0, 0);
                    // Read the checked facts attached to this outcome. The
                    // joined frontier only holds facts shared by all arms.
                    let path_base_facts = if let Some(outcome) = &focused_outcome {
                        outcome.facts().clone()
                    } else {
                        proof_execution
                            .core
                            .pending_loop_return_pure_facts(path_index)
                            .cloned()
                            .unwrap_or_else(|| proof.facts().clone())
                    };
                    // What the path still owes at exit: the obligations the
                    // kernel filed on the way to its outcome, converting the
                    // returned value to the function's type among them,
                    // under a context that reasons only exactly. An exact
                    // fact of the path's base discharges one, and so does
                    // the checked derivation over that base that discharges
                    // a statement's prerequisite under the implicit tail
                    // (`certified_statement_transitions`, the retained
                    // policy): the bare prover verdict is not evidence, a
                    // derivation that checks is. A bound the facts decide
                    // against is refuted, not missing: no smaller step or
                    // listed premise supplies it, and the report names the
                    // facts that refute it.
                    let (missing_obligations, refuted_obligations) =
                        crate::instrumentation::measure_operation(
                            function_block.signature().name(),
                            &proof_label,
                            "path obligation lookup",
                            || {
                                let assumptions = path_base_facts.assumptions();
                                let mut missing = Vec::new();
                                let mut refuted = Vec::new();
                                for obligation in path.obligations() {
                                    let proposition = obligation.proposition();
                                    if exact_fact_is_available(proposition, &path_base_facts) {
                                        continue;
                                    }
                                    if let Proposition::ConditionIs(condition, value) = proposition
                                        && assumptions.decide(condition.native_compat())
                                            == Some(!*value)
                                    {
                                        refuted.push(obligation.clone());
                                        continue;
                                    }
                                    if crate::kernel::search::ProofSearch::derive_proposition(
                                        assumptions,
                                        proposition,
                                    )
                                    .is_some_and(|derivation| derivation.check(assumptions))
                                    {
                                        continue;
                                    }
                                    missing.push(obligation.clone());
                                }
                                (missing, refuted)
                            },
                        );
                    if let Some(refuted) = refuted_obligations.first() {
                        let message = describe_refuted_proof_obligation(
                            refuted,
                            &path_base_facts.to_vec(),
                            parameter_binding,
                        );
                        return Err(proof.execution_obligation_error(
                            &proof_label,
                            path_index,
                            refuted,
                            path_base_facts,
                            message,
                        ));
                    }
                    if let Some(missing) = missing_obligations.first() {
                        let message = describe_missing_proof_obligations(
                            &missing_obligations,
                            &path_base_facts.to_vec(),
                            pre_state.resources().facts(),
                            parameter_binding,
                            path.facts(),
                        );
                        return Err(proof.execution_obligation_error(
                            &proof_label,
                            path_index,
                            missing,
                            path_base_facts,
                            message,
                        ));
                    }
                    let mut outcome = path.outcome().clone();
                    let mut outcome_proof = match focused_outcome {
                        Some(outcome) => outcome
                            .prepare_outcome_cases(&mut outcome_substrate, &mut contract_owner)?,
                        None => None,
                    };
                    if outcome_proof.is_none()
                        && !matches!(outcome, FunctionOutcome::VerificationDiverges)
                    {
                        continue 'execution_path;
                    }
                    // `None` marks a path-independent capture: an abstracted post-join
                    // path cannot decide the pre-join surface branches, and the tactic
                    // it carries belongs on every leaf.
                    let deferred_capture_branch_path = if let Some(deferred) = path_capture {
                        // Expansion follows the decisions retained at each split.
                        // A joined path has no single pre-join route; its suffix
                        // belongs on every leaf, as represented by None.
                        direct_view.surface_branch_path(path_index, &deferred.branch_skeleton)
                    } else {
                        Some(Vec::new())
                    };

                    if let Some(root) = outcome_proof.take() {
                        outcome_proof = Some(root.project_outcome_resources()?);
                    }
                    if let Some(root) = outcome_proof.take() {
                        let root = root.with_contract_return_counts(&completed_execution)?;
                        outcome = root.focused_outcome_state()?;
                        let contract_claims = claims.iter().map(|claim| {
                            let key = claim.key();
                            crate::instrumentation::record_deterministic_work(1);
                            let target = claim_targets.get(&key).cloned();
                            (key, target)
                        });
                        outcome_proof = Some(
                            root.open_contract_claim_goals(&closing_context, contract_claims)?,
                        );
                    }

                    let mut closures = claims
                        .iter()
                        .map(|claim| {
                            if claim.is_vacuous_for(&outcome) {
                                ClaimClosure::vacuous(
                                    &completed_execution,
                                    path_index,
                                    claim.key(),
                                    ClaimCertificate::ExactCheck,
                                )
                            } else {
                                Ok(ClaimClosure::default())
                            }
                        })
                        .collect::<Result<Vec<_>, ClickError>>()?;
                    let mut outcome_surface_propositions =
                        proof_execution.presentation.surface_propositions.clone();
                    // The ordered surface equalities each claim's goal was
                    // rewritten through, parallel to `rewritten_claim_proofs`.
                    // The direct Solve path checks them inside its checked
                    // `have` scope, preserving the original claim's
                    // checked completion through each rewrite.
                    let mut rewrite_claim_equalities: Vec<Vec<ClickProposition>> =
                        vec![Vec::new(); claims.len()];
                    // A claim goal rewritten on the retained outcome proof
                    // stays that proof, with the position after the rewrite:
                    // the closers after it continue the same derivation, so
                    // the completion they record is the claim goal the proof
                    // was rooted at, not the rewritten form.
                    let mut rewritten_claim_proofs: Vec<Option<(Proof<'_>, ProofCheckpoint<'_>)>> =
                        (0..claims.len()).map(|_| None).collect();
                    let path_requirements = outcome_proof
                        .as_ref()
                        .map_or_else(|| proof.facts().clone(), |root| root.facts().clone());
                    // An ungrouped top-level `choose`/`witness` refines one
                    // result-aware claim. Retain that typed judgment between
                    // source operations; syntax is recorded only for surface
                    // attribution, never reapplied as a candidate certificate.
                    let mut opened_claim: Option<OpenedClaimProof<'_>> = None;
                    let mut has_return_resource_rewrite = false;
                    let mut closing_input = None;
                    // Frame closure also applies the contract's returned
                    // resource transition. Track that ownership transition
                    // separately from the return-count interpretation above:
                    // closing an open body must retain its owned resources
                    // until its invariant has been proved.
                    let mut resource_transition_applied = false;
                    // Why the contract's resource transition did not apply at
                    // the closing `solve`, reported when a claim then stays open.
                    let mut pending_resource_transition_error: Option<String> = None;
                    drop(_path_preparation_timing);
                    let _post_execution_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "post-execution claim tactics",
                    );
                    let terminal_outcome_choice =
                        terminal_outcome_selector.as_ref().and_then(|condition| {
                            outcome_proof
                                .as_ref()?
                                .checked_outcome_if_value(condition, None)
                                .ok()
                        });
                    // The implicit closer follows the script's last tactic,
                    // and diagnostics number it so.
                    let implicit_closer_index = post_execution_tactics
                        .iter()
                        .map(|deferred| deferred.tactic_index + 1)
                        .max()
                        .unwrap_or(0);
                    let implicit_closer = DeferredPostExecutionTactic {
                        lexical_bindings: None,
                        reads_deferred_obtain: false,
                        tactic_index: implicit_closer_index,
                        source_index: usize::MAX,
                        tactic: PostExecutionTactic::ImplicitSolve,
                    };
                    // Only an ordered drain that has no closing `solve` and no
                    // further resource operation of its own needs the
                    // transition up front. A control node defers the transition
                    // to the reached closer, since earlier tactics can decide
                    // which arm will run. An expanded proof closes its
                    // resource ensures with `known()` and never re-folds.
                    if !post_execution_tactics.iter().any(|deferred| {
                        matches!(
                            deferred.tactic,
                            PostExecutionTactic::If { .. }
                                | PostExecutionTactic::CallOutcomes { .. }
                                | PostExecutionTactic::Match { .. }
                                | PostExecutionTactic::Solve
                                | PostExecutionTactic::ImplicitSolve
                                | PostExecutionTactic::SolveUsing(_)
                                | PostExecutionTactic::Leaf(
                                    ProofTactic::FoldResource(_)
                                        | ProofTactic::UnfoldResource(_)
                                        | ProofTactic::UserTactic(_)
                                )
                                | PostExecutionTactic::ResourceStepProved(_)
                                | PostExecutionTactic::CloseOpen { .. }
                        )
                    }) {
                        // Read the outcome's resources through the contract's
                        // checked transition as soon as the body returns what the
                        // contract returns. Ownership, not a framing tactic, is what
                        // hands a produced or returned resource to a resource
                        // ensure, so every ordered closer sees the same transitioned
                        // context. A body that still has to fold an open composite
                        // does not satisfy the guard here; the closing `solve` runs
                        // the same transition once that fold has happened.
                        if matches!(outcome, FunctionOutcome::Return { .. } | FunctionOutcome::Throw { .. })
                            && crate::kernel::program_function_return_resources_definitionally_established(
                                pre_state,
                                function,
                                arguments,
                                &outcome,
                                &assumptions_from_propositions(&path_requirements),
                            )
                            && let Ok(transitioned) = required_outcome(&outcome_proof)?
                                .apply_outcome_contract_resources(pre_state, function)
                        {
                            outcome = transitioned.focused_outcome_state()?;
                            resource_transition_applied = true;
                            outcome_proof = Some(transitioned);
                        }
                    }
                    // A whole-contract script that ends without closing every
                    // claim ends with `solve`, as an omitted proof does: the
                    // path's last step is the `solve` closer, which does
                    // nothing when the script's own tactics closed every
                    // claim. Its checked steps join the path's closers, so an
                    // expanded proof writes them out.
                    // An explicitly expanded fold in a returning arm uses
                    // the template captured by its enclosing open.
                    let mut named_open_templates = BTreeMap::new();
                    for deferred in post_execution_tactics.iter() {
                        if let PostExecutionTactic::CloseOpen {
                            resource: ResourceClause::Named { binding, .. },
                            restoration: OpenResourceRestoration::Named(instance),
                            ..
                        } = &deferred.tactic
                        {
                            named_open_templates.insert(binding.instance()?, instance);
                        }
                    }
                    let mut pending_post_execution_tactics = Vec::new();
                    if require_explicit_closers {
                        pending_post_execution_tactics.push(PendingPostExecutionTactic::Tactic(
                            &implicit_closer,
                            0,
                            None,
                        ));
                    }
                    pending_post_execution_tactics.extend(
                        post_execution_tactics
                            .iter()
                            .rev()
                            .map(|tactic| PendingPostExecutionTactic::Tactic(tactic, 0, None)),
                    );
                    // A capture belongs only to paths that actually reach its
                    // source occurrence, including through newly decided arms.
                    let mut visits_selected_capture = false;
                    let mut surface_post_choices = Vec::new();
                    let mut batch_previous_capture = None;
                    // Consecutive `known` closers only discharge claims;
                    // they do not change the outcome or its ambient facts.
                    // A failed whole-contract transition must not be retried
                    // once per returned member in an expanded solve proof.
                    let mut known_transition_attempted = false;
                    // Exact closers discharge claims without changing the ambient
                    // outcome or facts. Share their lazily prepared return views,
                    // including a failed preparation, until another tactic runs.
                    let mut return_claim_context = None;
                    // The facts before each post-return tactic, by source
                    // tactic: a refused return fold names the tactic that
                    // introduced the fact it could not justify. Each entry
                    // shares the persistent fact store.
                    let mut post_return_facts = Vec::new();
                    let mut post_execution_count = 0;
                    let mut deferred_locals = DeferredOutcomeLocals::default();
                    while let Some(deferred) = {
                        // A checked closer belongs at its source occurrence,
                        // before the next post-return tactic. Include it in
                        // the prefix used to place any subsequent proof cases.
                        path_surface_post_tactics.append(&mut path_grouped_surface_closers);
                        next_checked_post_execution_tactic(
                            &mut outcome_proof,
                            &mut pending_post_execution_tactics,
                            &mut deferred_locals,
                            &mut surface_post_choices,
                            &mut path_surface_post_tactics,
                            path_index,
                        )?
                    } {
                        let post_execution_index = post_execution_count;
                        post_execution_count += 1;
                        visits_selected_capture |= path_capture.is_some_and(|capture| {
                            deferred.tactic_index == capture.tactic_index
                                && deferred.source_index == capture.source_index
                        });
                        if let Some(previous) = batch_previous_capture.take() {
                            batch_capture_paths.entry(previous).or_default().push((
                                path_index,
                                std::mem::take(&mut path_deferred_capture_tactics),
                                path_deferred_capture_prefix,
                            ));
                        }
                        let batch_capture = path_batch_captures.get(&deferred.source_index);
                        let path_capture = batch_capture.or(path_capture);
                        if batch_capture.is_some() {
                            batch_previous_capture = Some(deferred.source_index);
                        }
                        let path_requirements = outcome_proof
                            .as_ref()
                            .map_or_else(|| proof.facts().clone(), |root| root.facts().clone());
                        if !matches!(
                            deferred.tactic,
                            PostExecutionTactic::Leaf(ProofTactic::Known)
                        ) {
                            known_transition_attempted = false;
                        }
                        if !matches!(
                            deferred.tactic,
                            PostExecutionTactic::Leaf(
                                ProofTactic::Known
                                    | ProofTactic::Enumerate
                                    | ProofTactic::Normalize
                                    | ProofTactic::NormalizeUsing(_)
                                    | ProofTactic::ArithmeticUsing(_)
                                    | ProofTactic::Preserve(_)
                            ) | PostExecutionTactic::Both(_)
                        ) {
                            return_claim_context = None;
                        }
                        let tactic_index = &deferred.tactic_index;
                        let source_index = &deferred.source_index;
                        let post_tactic = &deferred.tactic;
                        if matches!(
                            post_tactic,
                            PostExecutionTactic::Leaf(ProofTactic::LetSatisfy(_))
                        ) {
                            deferred_locals.checked_obtains += 1;
                        }
                        post_return_facts.push((*source_index, path_requirements.clone()));
                        if path_capture.is_some_and(|capture| {
                            capture.tactic_index == *tactic_index
                                && capture.source_index == *source_index
                        }) {
                            path_deferred_capture_prefix = (
                                path_surface_post_tactics.len(),
                                path_grouped_surface_closers.len(),
                            );
                        }
                        outcome_proof =
                            outcome_proof.map(|proof| proof.at_source_tactic(*source_index));
                        let _origin = {
                            let (tactic_name, tactic_class) =
                                post_execution_tactic_timing(post_tactic);
                            use crate::surface::proof_trace::TraceOrigin;
                            if matches!(post_tactic, PostExecutionTactic::ImplicitSolve) {
                                TraceOrigin::enter_implicit(tactic_name)
                            } else {
                                TraceOrigin::enter((tactic_class == "smart").then_some(tactic_name))
                            }
                        };
                        // Match TacticTiming's normal constructor: the implicit
                        // contract closer has no selectable written source site.
                        let _timing = (*source_index != usize::MAX
                            && crate::instrumentation::enabled())
                        .then(|| {
                            let (tactic_name, tactic_class) =
                                post_execution_tactic_timing(post_tactic);
                            if crate::instrumentation::starts_enabled() {
                                crate::instrumentation::emit(
                                    crate::instrumentation::VerificationEvent::TacticStarted(
                                        crate::instrumentation::TacticEvent {
                                            source_tactic_path: None,
                                            claim: proof_label.clone(),
                                            tactic_index: *tactic_index,
                                            tactic_name: tactic_name.to_string(),
                                            class: tactic_class.to_string(),
                                            statement_index: frontier.next_statement_index,
                                            source_index: *source_index,
                                        },
                                    ),
                                );
                            }
                            let timing_context = TimingTacticContext {
                                source_tactic_path: None,
                                claim_label: proof_label.clone(),
                                tactic_index: *tactic_index,
                                source_index: *source_index,
                                tactic_name: tactic_name.to_string(),
                                tactic_class: tactic_class.to_string(),
                                statement_index: frontier.next_statement_index,
                            };
                            push_timing_tactic(timing_context.clone());
                            TacticTiming {
                                source_tactic_path: None,
                                claim_label: proof_label.clone(),
                                tactic_index: *tactic_index,
                                source_index: *source_index,
                                tactic_name: tactic_name.to_string(),
                                tactic_class,
                                statement_index: frontier.next_statement_index,
                                start: std::time::Instant::now(),
                                context: timing_context,
                            }
                        });
                        if matches!(
                            post_tactic,
                            PostExecutionTactic::ResourceStepProved(_)
                                | PostExecutionTactic::CloseOpen { .. }
                                | PostExecutionTactic::Leaf(
                                    ProofTactic::FoldResource(_)
                                        | ProofTactic::UnfoldResource(_)
                                        | ProofTactic::UserTactic(_)
                                )
                        ) {
                            closing_input = None;
                        }
                        let proposition_closer = match post_tactic {
                            PostExecutionTactic::SolveUsing(_) => Some("solve() using"),
                            PostExecutionTactic::Leaf(
                                tactic @ (ProofTactic::Normalize
                                | ProofTactic::NormalizeUsing(_)
                                | ProofTactic::ArithmeticUsing(_)
                                | ProofTactic::Preserve(_)),
                            ) => Some(tactic_name(tactic)),
                            PostExecutionTactic::Both(_) => Some("all"),
                            _ => None,
                        };
                        if let Some(closer) = proposition_closer
                            && let Some(root) = outcome_proof.as_ref()
                            && let Some(crate::kernel::proof::OutcomeGoal::Closing(kind)) =
                                root.first_open_outcome_goal()?
                        {
                            return Err(root.step_error(format!("`{closer}` requires a proposition goal; the current contract-closing goal is {}; use `known()` for this closing operation", kind.description())));
                        }
                        // Written `known` and `solve` select the same closing goal.
                        // The implicit solver schedules that primitive for every omitted proof.
                        if matches!(
                            post_tactic,
                            PostExecutionTactic::Leaf(ProofTactic::Known)
                                | PostExecutionTactic::Solve
                                | PostExecutionTactic::ImplicitSolve
                        ) && !matches!(post_tactic, PostExecutionTactic::ImplicitSolve)
                            && prove_next_contract_closing_goal(
                                &mut outcome_proof,
                                &mut closing_input,
                                &completed_execution,
                                path_index,
                                has_return_resource_rewrite,
                                &post_return_facts,
                                ClosingProofMode::Explicit,
                            )?
                        {
                            record_post_execution_surface_tactic(
                                &mut path_grouped_surface_closers,
                                &mut path_deferred_capture_tactics,
                                path_capture,
                                post_execution_index,
                                *tactic_index,
                                ProofTactic::Known,
                            );
                            continue;
                        }
                        match post_tactic {
                            PostExecutionTactic::ResourceStepProved(ProofTactic::StepProved {
                                step,
                                proof,
                            }) => {
                                let Some(evolving) = outcome_proof.take() else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: typed outcome resource operation has no Proof goal"
                                    )));
                                };
                                let before = evolving.checkpoint();
                                let folded = super::checked_drivers::apply_source_step_proofs(
                                    &evolving,
                                    step,
                                    proof,
                                    *tactic_index,
                                )?;
                                has_return_resource_rewrite |=
                                    folded.execution().is_some_and(|execution| {
                                        execution
                                            .core
                                            .has_checked_return_resource_rewrite(path_index)
                                    });
                                outcome = folded.focused_outcome_state()?;
                                let surface_tactics =
                                    folded.certificate_since(&before)?.to_proof_tactics();
                                outcome_proof = Some(folded);
                                for tactic in surface_tactics {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::ResourceStepProved(_) => {
                                unreachable!("a proved resource step wraps its `StepProved` tactic")
                            }
                            PostExecutionTactic::Leaf(tactic)
                                if opens_outcome_claim_scope(tactic)
                                    || opened_claim.is_some()
                                        && matches!(
                                            tactic,
                                            ProofTactic::UnfoldProposition(_)
                                                | ProofTactic::UnfoldFunction(_)
                                                | ProofTactic::Rewrite(_)
                                                | ProofTactic::LetSatisfy(_)
                                        )
                                    || unfolds_outcome_goal(
                                        tactic,
                                        claims,
                                        &closures,
                                        spec_definitions.predicates,
                                    ) =>
                            {
                                // Goal refinements open the claim's own proof.
                                // An obtain in that proof can use its local facts.
                                let opened = match opened_claim.take() {
                                    Some(active) => active,
                                    None => {
                                        let (claim_index, surface_goal, proof) = begin_outcome_claim_proof(
                                            outcome_proof.as_ref().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for `{}` is unavailable",
                                                    tactic_name(tactic)
                                                ))
                                            })?,
                                            function,
                                            pre_state,
                                            arguments,
                                            &outcome,
                                            claims,
                                            &rewrite_claim_equalities,
                                            tactic_name(tactic),
                                        )?;
                                        OpenedClaimProof {
                                            claim_index,
                                            surface_goal,
                                            proof,
                                            introduces_scope: false,
                                        }
                                    }
                                };
                                let refreshed = opened
                                    .proof
                                    .refresh_outcome_from(required_outcome(&outcome_proof)?)?;
                                let before = refreshed.checkpoint();
                                let proof = if let ProofTactic::IntroBlock { binder, body } = tactic
                                {
                                    refreshed.driver().apply_scoped_intro(
                                        binder.as_ref(),
                                        body,
                                        !implicit_solve_disabled(),
                                    )?
                                } else {
                                    let step =
                                        SourceContext::PostExecution.leaf_step(tactic).expect(
                                            "a post-execution leaf converts to its checked step",
                                        );
                                    refreshed.driver().apply_step(step)?
                                };
                                let certificate = proof.certificate_since(&before)?;
                                if matches!(tactic, ProofTactic::IntroBlock { .. }) {
                                    let claim_index = opened.claim_index;
                                    record_claim_closure(
                                        &mut outcome_proof,
                                        &mut closures,
                                        claims,
                                        &completed_execution,
                                        path_index,
                                        claim_index,
                                        ClaimClosure::by_continued_proposition(
                                            claims[claim_index].key(),
                                            path_index,
                                            Vec::new(),
                                            proof.completed_proposition()?,
                                        ),
                                    )?;
                                } else {
                                    let introduces_scope = opened.introduces_scope
                                        || matches!(
                                            tactic,
                                            ProofTactic::Intro
                                                | ProofTactic::IntroAs(_)
                                                | ProofTactic::IntroBinder(_)
                                        );
                                    opened_claim = Some(OpenedClaimProof {
                                        introduces_scope,
                                        ..opened.with_proof(proof)
                                    });
                                }
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::CloseOpen {
                                resource,
                                restoration,
                                retain_deferred_body,
                            } => {
                                if let ResourceClause::Named { binding, .. } = resource {
                                    named_open_templates.remove(&binding.instance()?);
                                }
                                let evolving = outcome_proof.take().ok_or_else(|| ClickError::new(
                                    format!("`{proof_label}` path {path_index}: resource scope has no outcome Proof")
                                ))?;
                                let named =
                                    matches!(restoration, OpenResourceRestoration::Named(_));
                                let already_restored =
                                    if let OpenResourceRestoration::Named(instance) = restoration {
                                        evolving.holds_open_instance(instance)?
                                    } else {
                                        false
                                    };
                                let (closed, tail) = if already_restored {
                                    (evolving, None)
                                } else {
                                    evolving.driver().close_scope_with_body_fact_proof(
                                        resource,
                                        restoration,
                                        &|proof| {
                                            proof.close_outcome_resource_scope(
                                                resource,
                                                restoration,
                                                resource_transition_applied,
                                            )
                                        },
                                    )?
                                };
                                has_return_resource_rewrite |= named
                                    && closed.execution().is_some_and(|execution| {
                                        execution
                                            .core
                                            .has_checked_return_resource_rewrite(path_index)
                                    });
                                outcome = closed.focused_outcome_state()?;
                                outcome_proof = Some(closed);
                                if tail.is_some() || named || *retain_deferred_body {
                                    let deferred = ProofOpen::deferred_block_tail(
                                        resource.clone(),
                                        tail.map_or_else(Vec::new, |proof| {
                                            proof.to_proof_tactics()
                                        }),
                                        if already_restored {
                                            DeferredOpenTail::AlreadyRestored
                                        } else {
                                            DeferredOpenTail::Restore
                                        },
                                    );
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        ProofTactic::Open(deferred),
                                    );
                                }
                            }
                            PostExecutionTactic::Apply(application) => {
                                let FunctionOutcome::Return { .. } = &outcome else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: theorem application requires a return outcome"
                                    )));
                                };

                                let certificate = if let Some(evolving) = outcome_proof.take() {
                                    // The migrated smart case: selection reads
                                    // the goal-aware view and the accepted
                                    // application advances this path's
                                    // evolving outcome proof.
                                    let before = evolving.checkpoint();
                                    // The same written `apply` the execution
                                    // frontier runs, with its refusal.
                                    let applied = super::checked_drivers::apply_written_theorem(
                                        &evolving,
                                        application,
                                    )?;
                                    let certificate = applied.certificate_since(&before)?;
                                    outcome_proof = Some(applied);
                                    certificate
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                // The retained application is prefixed to every
                                // claim certificate, so independent verification holds the
                                // same checked conclusions when the closer runs.
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Have(have) => {
                                if let Some(checked) = outcome_proof
                                    .as_ref()
                                    .and_then(|proof| proof.focused_outcome_data())
                                    .and_then(|data| data.checked_haves.get(&deferred.source_index))
                                {
                                    for tactic in checked.to_proof_tactics() {
                                        record_post_execution_surface_tactic(
                                            &mut path_surface_post_tactics,
                                            &mut path_deferred_capture_tactics,
                                            path_capture,
                                            post_execution_index,
                                            *tactic_index,
                                            tactic,
                                        );
                                    }
                                    continue;
                                }
                                // A throw outcome is proved like a return: its
                                // `exceptional ensures` names the thrown value
                                // `exception`, which smart `solve` already
                                // scopes with the same checked `have`.
                                let (FunctionOutcome::Return { .. }
                                | FunctionOutcome::Throw { .. }) = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `have` requires a return outcome"
                                    )));
                                };
                                // A deferred branch can leave the return-resource
                                // transition until an explicit closer. Prepare it
                                // before publishing a new outcome fact as well:
                                // otherwise the later transition changes a
                                // count-dependent predicate's captured ledger.
                                // An introduced proposition keeps its own scope.
                                if !opened_claim
                                    .as_ref()
                                    .is_some_and(|opened| opened.introduces_scope)
                                    && !resource_transition_applied
                                    && matches!(
                                        outcome,
                                        FunctionOutcome::Return { .. }
                                            | FunctionOutcome::Throw { .. }
                                    )
                                    && claims.iter().enumerate().any(|(index, claim)| {
                                        !closures[index].is_closed()
                                            && matches!(
                                                claim.clause().ensure(),
                                                Ensure::Resource(_)
                                            )
                                    })
                                    && let Ok(transitioned) = required_outcome(&outcome_proof)?
                                        .apply_outcome_contract_resources(pre_state, function)
                                {
                                    outcome = transitioned.focused_outcome_state()?;
                                    return_claim_context = None;
                                    resource_transition_applied = true;
                                    outcome_proof = Some(transitioned);
                                }
                                // A `have` after `intro` belongs to the active
                                // claim proof, which owns the introduced binder.
                                // Earlier `have` steps extend the outcome proof.
                                let active_claim = opened_claim.take();
                                let evolving_root = match &active_claim {
                                    Some(active) => active
                                        .proof
                                        .refresh_outcome_from(required_outcome(&outcome_proof)?)?,
                                    None => outcome_proof.take().ok_or_else(|| {
                                        ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                        ))
                                    })?,
                                };
                                let evolving_have = {
                                    let evolving = evolving_root;
                                    let attempt = (|| -> Result<
                                        Option<(Proof<'_>, Proposition, ProofCertificate)>,
                                        ClickError,
                                    > {
                                        let prepared = if active_claim.is_some() {
                                            evolving.clone()
                                        } else {
                                            evolving.with_outcome_store_consequences()?
                                        };
                                        let before = prepared.checkpoint();
                                        // The same checked `have` the execution
                                        // frontier runs, with its diagnostics.
                                        let nested = prepared.driver().open_source_have(have)?;
                                        let goal = nested.goal().cloned();
                                        let mut failed_check = None;
                                        let closed = super::checked_drivers::solve_nested_have(
                                            nested,
                                            have,
                                            &mut failed_check,
                                        )
                                        .map_err(|error| {
                                            super::checked_drivers::source_have_error(
                                                &prepared,
                                                have,
                                                *tactic_index,
                                                goal.as_ref(),
                                                Some(error),
                                                false,
                                            )
                                        })?
                                        .ok_or_else(|| {
                                            super::checked_drivers::source_have_error(
                                                &prepared,
                                                have,
                                                *tactic_index,
                                                goal.as_ref(),
                                                failed_check.take(),
                                                true,
                                            )
                                        })?;
                                        let joined = closed.join()?;
                                        let [fact] = joined.added_facts() else {
                                            return Ok(None);
                                        };
                                        let fact = fact.clone();
                                        let certificate = joined.certificate_since(&before)?;
                                        Ok(Some((joined, fact, certificate)))
                                    })();
                                    match attempt? {
                                        Some((joined, fact, certificate)) => {
                                            if let Some(active) = &active_claim {
                                                opened_claim = Some(active.with_proof(joined));
                                            } else {
                                                outcome_proof = Some(joined);
                                            }
                                            Some((fact, Some(certificate)))
                                        }
                                        None => {
                                            if let Some(active) = &active_claim {
                                                opened_claim = Some(active.with_proof(evolving));
                                            } else {
                                                outcome_proof = Some(evolving);
                                            }
                                            None
                                        }
                                    }
                                };
                                let Some((fact, Some(certificate))) = evolving_have else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `have` did not retain a complete certificate",
                                    )));
                                };
                                if active_claim.is_none() {
                                    outcome_surface_propositions
                                        .record_lowering(&have.proposition, &fact)?;
                                }
                                // Beginning the source `have` may first prove
                                // its lowering obligations. Keep those checked
                                // prerequisites along with the final `have`.
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::Transport { source, target }
                            | PostExecutionTactic::Leaf(ProofTactic::TransportUsing {
                                source,
                                target,
                                ..
                            }) => {
                                // A written `transport using` is the same
                                // checked leaf it is at an execution
                                // frontier; a bare `transport` searches.
                                let written = match post_tactic {
                                    PostExecutionTactic::Leaf(tactic) => {
                                        SourceContext::PostExecution.leaf_step(tactic)
                                    }
                                    _ => None,
                                };
                                if !matches!(outcome, FunctionOutcome::Return { .. }) {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `transport` requires a return outcome"
                                    )));
                                }
                                let (checked_facts, certificate) = if let Some(evolving) =
                                    outcome_proof.take()
                                {
                                    // Both forms advance this path's
                                    // evolving outcome proof, which records
                                    // the checked lowerings on the goal
                                    // atomically. A bare `transport` is
                                    // planned exactly as at an execution
                                    // frontier, against the outcome's state.
                                    let prepared = evolving.with_outcome_store_consequences()?;
                                    let before = prepared.checkpoint();
                                    let transported = if let Some(step) = written {
                                        prepared.driver().apply_step(step)
                                    } else {
                                        match crate::kernel::search::ProofSearch::try_execution_fact_transport_or_refusal(&(prepared),
                                            source, target,
                                        )? {
                                            Ok(transported) => Ok(transported),
                                            Err(source_refusal) => crate::kernel::search::ProofSearch::apply_planned_fact_transport(
 &prepared,
                                                    source,
                                                    target,
                                                    *tactic_index,
                                                    source_refusal.as_ref(),
                                                ),
                                        }
                                    }
                                    .inspect_err(|_| {
                                        prepared.record_certification_failure_trace(
                                            &proof_label,
                                            path_index,
                                        );
                                    })?;
                                    let checked_facts = transported.checked_facts().to_vec();
                                    let certificate = transported.certificate_since(&before)?;
                                    outcome_proof = Some(transported);
                                    (checked_facts, certificate)
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                // Ordinary `have` publication retains its target;
                                // the legacy transport transition retains both ends.
                                match checked_facts.as_slice() {
                                    [checked_source, checked_target] => {
                                        outcome_surface_propositions
                                            .record_lowering(source, checked_source)?;
                                        outcome_surface_propositions
                                            .record_lowering(target, checked_target)?;
                                    }
                                    [checked_target] => {
                                        outcome_surface_propositions
                                            .record_lowering(target, checked_target)?;
                                    }
                                    _ => {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: checked transport did not retain its target"
                                        )));
                                    }
                                }
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Leaf(
                                ProofTactic::Known
                                | ProofTactic::Enumerate
                                | ProofTactic::Normalize
                                | ProofTactic::NormalizeUsing(_)
                                | ProofTactic::ArithmeticUsing(_)
                                | ProofTactic::Preserve(_),
                            )
                            | PostExecutionTactic::Both(_) => {
                                // The written closers that apply one step to
                                // the main goal: `known`, the normalizing
                                // closers and `both`. Only `known` reads
                                // a resource claim and the outcome's recorded
                                // lowerings.
                                let is_known = matches!(
                                    post_tactic,
                                    PostExecutionTactic::Leaf(ProofTactic::Known)
                                );
                                let closer_name = match post_tactic {
                                    PostExecutionTactic::Both(_) => "all",
                                    PostExecutionTactic::Leaf(tactic) => tactic_name(tactic),
                                    _ => unreachable!("matched a closer above"),
                                };
                                // The step this closer applies is the written
                                // tactic's.
                                let closer_step = match post_tactic {
                                    PostExecutionTactic::Leaf(tactic) => {
                                        SourceContext::PostExecution.leaf_step(tactic).expect(
                                            "a post-execution leaf converts to its checked step",
                                        )
                                    }
                                    PostExecutionTactic::Both(_) => ProofStep::Normalize,
                                    _ => unreachable!("matched a closer above"),
                                };
                                if let Some(certificate) = continue_outcome_claim_proof(
                                    &mut opened_claim,
                                    &mut closures,
                                    claims,
                                    &mut outcome_proof,
                                    &completed_execution,
                                    path_index,
                                    |proof| {
                                        if let PostExecutionTactic::Both(both) = post_tactic {
                                            proof.driver().apply_all_source(both, true)
                                        } else {
                                            proof.driver().apply_step(closer_step.clone())
                                        }
                                    },
                                )
                                .map_err(|error| {
                                    error.with_context(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}"
                                    ))
                                })? {
                                    for tactic in certificate.to_proof_tactics() {
                                        record_post_execution_surface_tactic(
                                            &mut path_surface_post_tactics,
                                            &mut path_deferred_capture_tactics,
                                            path_capture,
                                            post_execution_index,
                                            *tactic_index,
                                            tactic,
                                        );
                                    }
                                    continue;
                                }
                                let mut closed_any = false;
                                // A contract resource claim is visible only
                                // through the contract's checked resource
                                // transition, which `solve` applies before
                                // closing claims against the outcome. The
                                // closure `solve` records for such a claim is
                                // spelled `known`, so the same reading of
                                // the outcome has to be available here: without
                                // it an expanded `solve` cannot reproduce the
                                // claim its own certificate reports closed.
                                if is_known
                                    && !resource_transition_applied
                                    && !known_transition_attempted
                                    && matches!(
                                        outcome,
                                        FunctionOutcome::Return { .. }
                                            | FunctionOutcome::Throw { .. }
                                    )
                                    && claims.iter().enumerate().any(|(index, claim)| {
                                        let clause = claim.clause();
                                        !closures[index].is_closed()
                                            && matches!(clause.ensure(), Ensure::Resource(_))
                                    })
                                {
                                    known_transition_attempted = true;
                                    let established = crate::kernel::program_function_return_resources_definitionally_established(
                                        pre_state,
                                        function,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                    );
                                    if established
                                        && let Ok(transitioned) = required_outcome(&outcome_proof)?
                                            .apply_outcome_contract_resources(pre_state, function)
                                    {
                                        outcome = transitioned.focused_outcome_state()?;
                                        return_claim_context = None;
                                        resource_transition_applied = true;
                                        outcome_proof = Some(transitioned);
                                    }
                                }

                                // Each claim is focused from the evolving
                                // outcome Proof and retains its completion.
                                let fixed_state_root = outcome_claim_root(
                                    &outcome_proof,
                                    &outcome,
                                    &proof_label,
                                    path_index,
                                )?;
                                let mut retained_certificate = None;
                                // An `known` that closes no goal keeps
                                // one fresh goal's checked context.
                                let mut failed_known = None;
                                // A `both` that closes no goal and was refused
                                // for exactly one goal reports that refusal,
                                // which names the arm tactic by its source
                                // path. With several candidate goals no one
                                // refusal is the reader's, so the summary
                                // below stands.
                                let mut both_errors = Vec::new();
                                let main_claim = main_goal_claim(&outcome_proof, &closures)?;
                                for claim_index in main_claim.into_iter() {
                                    let claim = &claims[claim_index];
                                    let ensure_clause = claim.clause();
                                    if matches!(outcome, FunctionOutcome::VerificationDiverges) {
                                        if matches!(post_tactic, PostExecutionTactic::Both(_)) {
                                            return Err(ClickError::new(
                                                "`both` requires a return-state conjunction",
                                            ));
                                        }
                                        // Postconditions are conditional on return.
                                        // The checked execution outcome supplies
                                        // vacuity without a return value or state.
                                        if matches!(closer_step, ProofStep::NormalizeUsing(_)) {
                                            return Err(ClickError::new(
                                                "`normalize using` requires a return-state proposition; use `known()` for a divergent path",
                                            ));
                                        }
                                        // Same rule for the explicit arithmetic
                                        // closer: its premises are cited against
                                        // a return state this path does not have.
                                        if matches!(closer_step, ProofStep::ArithmeticUsing(_)) {
                                            return Err(ClickError::new(
                                                "`arithmetic using` requires a return-state proposition; use `known()` for a divergent path",
                                            ));
                                        }
                                        record_claim_closure(
                                            &mut outcome_proof,
                                            &mut closures,
                                            claims,
                                            &completed_execution,
                                            path_index,
                                            claim_index,
                                            ClaimClosure::vacuous(
                                                &completed_execution,
                                                path_index,
                                                claim.key(),
                                                ClaimCertificate::ExactCheck,
                                            )?,
                                        )?;
                                        closed_any = true;
                                        continue;
                                    }
                                    if let Ensure::Resource(_resource) = ensure_clause.ensure() {
                                        if is_known
                                            && let Ok(checked_resource) =
                                                required_outcome(&outcome_proof)?
                                                    .check_outcome_resource_claim(
                                                        &completed_execution,
                                                        *claim,
                                                    )
                                        {
                                            record_claim_closure(
                                                &mut outcome_proof,
                                                &mut closures,
                                                claims,
                                                &completed_execution,
                                                path_index,
                                                claim_index,
                                                ClaimClosure::resource(
                                                    ClaimCertificate::ExactCheck,
                                                    checked_resource,
                                                ),
                                            )?;
                                            closed_any = true;
                                            break;
                                        }
                                        continue;
                                    }
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        unreachable!("resource ensures were handled above")
                                    };
                                    let kernel_goals = contract_closing_goal_forms(
                                        function,
                                        proof_context
                                            .constants
                                            .entry_context
                                            .as_ref()
                                            .map(|entry| entry.cases.closing_entry()),
                                        outcome_proof
                                            .as_ref()
                                            .and_then(Proof::claim_goals)
                                            .and_then(|goals| goals.target(&claim.key())),
                                        contract_pre_state,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                        &mut return_claim_context,
                                    )?;
                                    // Expansion can emit a checked `have` of
                                    // the original claim after rewriting it.
                                    // Independently prove that exact original
                                    // claim on the current root; never treat a
                                    // failed rewritten proof as a success.
                                    if is_known && rewritten_claim_proofs[claim_index].is_some() {
                                        if let Some(root) = &fixed_state_root {
                                            for original in kernel_goals.iter().flatten() {
                                                let candidate = root
                                                    .driver()
                                                    .open_contract_claim_without_lowering_facts(
                                                        original,
                                                        surface_goal,
                                                    )?
                                                    .driver()
                                                    .apply_step(ProofStep::Known);
                                                if let Ok(proof) = candidate {
                                                    retained_certificate =
                                                        Some(proof.certificate());
                                                    record_claim_closure(
                                                        &mut outcome_proof,
                                                        &mut closures,
                                                        claims,
                                                        &completed_execution,
                                                        path_index,
                                                        claim_index,
                                                        ClaimClosure::by_exact_check_completing(
                                                            claims[claim_index].key(),
                                                            path_index,
                                                            proof.completed_proposition()?,
                                                        ),
                                                    )?;
                                                    closed_any = true;
                                                    break;
                                                }
                                            }
                                        }
                                        if closed_any {
                                            break;
                                        }
                                    }
                                    let applied = apply_claim_step(
                                        rewritten_claim_proofs[claim_index].as_ref(),
                                        fixed_state_root.as_ref(),
                                        &claim.key(),
                                        surface_goal,
                                        || Ok(kernel_goals),
                                        |focused, origin| {
                                            // A rewritten claim proof applies the
                                            // written step as is; a fresh goal plans
                                            // the certificate `arithmetic using` cites.
                                            if let PostExecutionTactic::Both(both) = post_tactic {
                                                return Ok(focused
                                                    .at_source_tactic(*source_index)
                                                    .driver()
                                                    .apply_all_source(both, true));
                                            }
                                            let PostExecutionTactic::Leaf(
                                                ProofTactic::ArithmeticUsing(surface_premises),
                                            ) = post_tactic
                                            else {
                                                return Ok(focused
                                                    .driver()
                                                    .apply_step(closer_step.clone()));
                                            };
                                            if origin == ClaimProofOrigin::Rewritten {
                                                return Ok(focused
                                                    .driver()
                                                    .apply_step(closer_step.clone()));
                                            }
                                            apply_post_execution_arithmetic_using(
                                                focused,
                                                surface_premises,
                                            )
                                        },
                                    )?;
                                    match applied {
                                        Ok(ClaimStepApplied { proof, certificate }) => {
                                            retained_certificate = Some(certificate);
                                            record_claim_closure(
                                                &mut outcome_proof,
                                                &mut closures,
                                                claims,
                                                &completed_execution,
                                                path_index,
                                                claim_index,
                                                ClaimClosure::by_exact_check_completing(
                                                    claims[claim_index].key(),
                                                    path_index,
                                                    proof.completed_proposition()?,
                                                ),
                                            )?;
                                            closed_any = true;
                                            break;
                                        }
                                        // Keep one selected failed goal's checked context.
                                        // A fresh summary alone loses its opt-in trace.
                                        Err(ClaimStepMiss { error, origin }) => {
                                            if is_known {
                                                if origin == ClaimProofOrigin::Fresh
                                                    && error.is_some()
                                                {
                                                    failed_known = error;
                                                }
                                            } else if matches!(
                                                post_tactic,
                                                PostExecutionTactic::Both(_)
                                            ) && let Some(error) = error
                                            {
                                                both_errors.push(error);
                                            }
                                        }
                                    }
                                }
                                if !closed_any {
                                    if both_errors.len() == 1
                                        && let Some(error) = both_errors.pop()
                                    {
                                        return Err(error);
                                    }
                                    let reason = match main_claim {
                                        Some(index) => {
                                            let goal =
                                                crate::surface::diagnostics::describe_ensure_clause(
                                                    claims[index].clause(),
                                                );
                                            if is_known {
                                                format!(
                                                    "You must prove `{goal}` in order to use the tactic `known()`."
                                                )
                                            } else {
                                                format!(
                                                    "`{closer_name}` did not prove the current goal `{goal}`"
                                                )
                                            }
                                        }
                                        None => no_open_goal(closer_name),
                                    };
                                    let error = ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: {reason}"
                                    )).with_proof_refusal(ProofRefusal::Tactic).with_failed_tactic(closer_name);
                                    return Err(
                                        match failed_known
                                            .and_then(|failure| failure.diagnostic().cloned())
                                        {
                                            Some(mut diagnostic) => {
                                                diagnostic.reason = error.raw_summary().to_owned();
                                                error.with_diagnostic_if_missing(diagnostic)
                                            }
                                            None => error,
                                        },
                                    );
                                }
                                let tactics = retained_certificate
                                    .as_ref()
                                    .map(ProofCertificate::to_proof_tactics)
                                    .unwrap_or_else(|| vec![closer_step.to_proof_tactic()]);
                                for tactic in tactics {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::Leaf(
                                tactic @ ProofTactic::Rewrite(surface_equality),
                            ) => {
                                let rewrite_step = SourceContext::PostExecution
                                    .leaf_step(tactic)
                                    .expect("a post-execution leaf converts to its checked step");
                                let FunctionOutcome::Return { .. } = &outcome else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` requires a return outcome"
                                    )));
                                };
                                let root = required_outcome(&outcome_proof)?;
                                let (claim_index, surface_goal) =
                                    focused_proposition_claim(root, claims, "rewrite")?;
                                let claim = &claims[claim_index];
                                let applied = apply_claim_step(
                                    rewritten_claim_proofs[claim_index].as_ref(),
                                    Some(root),
                                    &claim.key(),
                                    surface_goal,
                                    || {
                                        contract_closing_goal_forms(
                                            function,
                                            proof_context
                                                .constants
                                                .entry_context
                                                .as_ref()
                                                .map(|entry| entry.cases.closing_entry()),
                                            root.claim_goals()
                                                .and_then(|goals| goals.target(&claim.key())),
                                            contract_pre_state,
                                            arguments,
                                            &outcome,
                                            &assumptions_from_propositions(&path_requirements),
                                            &mut None,
                                        )
                                    },
                                    |proof, _| Ok(proof.driver().apply_step(rewrite_step.clone())),
                                )?;
                                let ClaimStepApplied { proof: chained, certificate } =
                                    applied.map_err(|miss| {
                                        miss.error.unwrap_or_else(|| root.step_error(
                                            "`rewrite` could not focus the current proposition claim",
                                        ))
                                    })?;
                                let checkpoint = chained.checkpoint();
                                rewritten_claim_proofs[claim_index] = Some((chained, checkpoint));
                                rewrite_claim_equalities[claim_index]
                                    .push(surface_equality.clone());
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::If { .. }
                            | PostExecutionTactic::CallOutcomes { .. }
                            | PostExecutionTactic::Match { .. } => unreachable!(
                                "post-execution branch selection must flatten control nodes before checking leaf tactics"
                            ),
                            PostExecutionTactic::Solve
                            | PostExecutionTactic::ImplicitSolve
                            | PostExecutionTactic::SolveUsing(_) => {
                                close_post_execution_claims_with_solve(
                                    post_tactic,
                                    deferred,
                                    tactic_index,
                                    path_index,
                                    &proof_label,
                                    require_explicit_closers,
                                    function_block,
                                    parsed_function,
                                    function,
                                    arguments,
                                    claims,
                                    spec_definitions,
                                    parameter_binding,
                                    pre_state,
                                    contract_pre_state,
                                    proof_context,
                                    execution,
                                    &completed_execution,
                                    &entry_pure_facts,
                                    path_capture,
                                    &path_requirements,
                                    &rewrite_claim_equalities,
                                    &rewritten_claim_proofs,
                                    &mut outcome,
                                    &mut outcome_proof,
                                    &mut opened_claim,
                                    &mut closures,
                                    &mut resource_transition_applied,
                                    &mut pending_resource_transition_error,
                                    &mut path_surface_post_tactics,
                                    &mut path_grouped_surface_closers,
                                    &mut path_deferred_capture_tactics,
                                )
                                .map_err(|mut error| {
                                    if error.verification_stopped()
                                        && error.proof_claim_label().is_none()
                                        && let Some(root) = &outcome_proof
                                    {
                                        if let Ok(Some(index)) =
                                            main_goal_claim(&outcome_proof, &closures)
                                        {
                                            error = error.with_unlowered_goal(
                                                diagnostic_claim_statement(&claims[index]),
                                            );
                                        }
                                        error = root.attach_step_diagnostic(error);
                                    }
                                    error
                                })?;
                                if matches!(post_tactic, PostExecutionTactic::ImplicitSolve)
                                    && !super::proof_object::implicit_solve_disabled()
                                {
                                    while prove_next_contract_closing_goal(
                                        &mut outcome_proof,
                                        &mut closing_input,
                                        &completed_execution,
                                        path_index,
                                        has_return_resource_rewrite,
                                        &post_return_facts,
                                        ClosingProofMode::Implicit,
                                    )? {
                                        record_post_execution_surface_tactic(
                                            &mut path_grouped_surface_closers,
                                            &mut path_deferred_capture_tactics,
                                            path_capture,
                                            post_execution_index,
                                            *tactic_index,
                                            ProofTactic::Known,
                                        );
                                    }
                                }
                                continue;
                            }
                            // Every other leaf advances the path's outcome
                            // proof; the leaves that refine or close a claim
                            // have their own arms above.
                            PostExecutionTactic::Leaf(tactic) => {
                                // A predicate unfold and a theorem application
                                // read the returned value.
                                let return_operation = match tactic {
                                    ProofTactic::UnfoldProposition(_) => {
                                        Some("predicate unfolding")
                                    }
                                    ProofTactic::ApplyTheoremUsing { .. } => {
                                        Some("theorem application")
                                    }
                                    _ => None,
                                };
                                if let Some(operation) = return_operation
                                    && !matches!(outcome, FunctionOutcome::Return { .. })
                                {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: {operation} requires a return outcome"
                                    )));
                                }
                                let step = SourceContext::PostExecution
                                    .leaf_step(tactic)
                                    .expect("a post-execution leaf converts to its checked step");
                                let evolving = outcome_proof.take().ok_or_else(|| ClickError::new(
                                    format!("`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable")
                                ))?;
                                let before = evolving.checkpoint();
                                let applied = if let ProofTactic::FoldResource(
                                    resource @ ResourceClause::Named { binding, .. },
                                ) = tactic
                                    && binding.fold_fields.is_none()
                                    && binding.child_bindings.is_none()
                                    && let Some(instance) =
                                        named_open_templates.get(&binding.instance()?)
                                {
                                    evolving
                                        .apply_explicit_open_instance_fold(resource, instance)?
                                } else {
                                    evolving.driver().apply_step(step)?
                                };
                                if matches!(
                                    tactic,
                                    ProofTactic::FoldResource(_)
                                        | ProofTactic::UnfoldResource(_)
                                        | ProofTactic::UserTactic(_)
                                ) {
                                    has_return_resource_rewrite |=
                                        applied.execution().is_some_and(|execution| {
                                            execution
                                                .core
                                                .has_checked_return_resource_rewrite(path_index)
                                        });
                                }
                                // A resource operation changes the outcome's
                                // resources; the other leaves only add facts.
                                if matches!(
                                    tactic,
                                    ProofTactic::FoldResource(_)
                                        | ProofTactic::UnfoldResource(_)
                                        | ProofTactic::UserTactic(_)
                                ) {
                                    outcome = applied.focused_outcome_state()?;
                                }

                                // `apply using` keeps its written spelling in
                                // the expansion; every other leaf records its
                                // checked certificate.
                                let surface_tactics =
                                    if matches!(tactic, ProofTactic::ApplyTheoremUsing { .. }) {
                                        vec![tactic.clone()]
                                    } else {
                                        applied.certificate_since(&before)?.to_proof_tactics()
                                    };
                                if let ProofTactic::LetSatisfy(binding) = tactic {
                                    let end = obtain_ends
                                        .get_or_init(|| obtain_scope_ends(certificate_tactics))
                                        .get(source_index)
                                        .copied()
                                        .unwrap_or(usize::MAX);
                                    deferred_locals.record(&evolving, &applied, binding, end);
                                }
                                outcome_proof = Some(applied);
                                for tactic in surface_tactics {
                                    record_post_execution_surface_tactic(
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        path_capture,
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                        }
                        if let Err(error) = check_verification_deadline() {
                            let current = outcome_proof.as_ref().unwrap_or(&proof);
                            return Err(
                                if matches!(
                                    post_tactic,
                                    PostExecutionTactic::Leaf(ProofTactic::TransportUsing { .. })
                                ) {
                                    current.attach_transport_budget_diagnostic(error, current)
                                } else {
                                    current.attach_step_diagnostic(error)
                                },
                            );
                        }
                    }
                    drop(_post_execution_timing);
                    let _path_closing_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "path closure and theorem assembly",
                    );

                    if !require_explicit_closers
                        && let Some(opened) = take_opened_claim(&mut opened_claim, &closures)
                    {
                        let claim_index = opened.claim_index;
                        let proof = opened
                            .proof
                            .refresh_outcome_from(required_outcome(&outcome_proof)?)?;
                        match crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))? {
                            Some(completed) if completed.is_complete() => {
                                // The source's choose/witness steps are already
                                // retained in the path surface stream. The
                                // ordinary implicit closer contributes no
                                // additional syntax.
                                record_claim_closure(&mut outcome_proof, &mut closures, claims, &completed_execution, path_index, claim_index, ClaimClosure::by_exact_check_completing(claims[claim_index].key(), path_index,
                                    completed.completed_proposition()?,
                                ))?;
                            }
                            _ => closures[claim_index].record_failure(ClickError::new(
                                "the retained claim proof did not close by the implicit exact check",
                            )),
                        }
                    }

                    if !require_explicit_closers {
                        if !resource_transition_applied {
                            prepare_produced_tokens(
                                function,
                                claims,
                                &closures,
                                &mut outcome,
                                &mut outcome_proof,
                                &mut path_surface_post_tactics,
                            )?;
                        }
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            if matches!(outcome, FunctionOutcome::VerificationDiverges) {
                                record_claim_closure(
                                    &mut outcome_proof,
                                    &mut closures,
                                    claims,
                                    &completed_execution,
                                    path_index,
                                    claim_index,
                                    ClaimClosure::vacuous(
                                        &completed_execution,
                                        path_index,
                                        claim.key(),
                                        ClaimCertificate::ExactCheck,
                                    )?,
                                )?;
                                continue;
                            }
                            // The implicit closer is the direct logical closure
                            // of the claim from the outcome Proof: it records
                            // the completion claim certification matches. The
                            // exact surface checker below remains for claims
                            // that closure does not reach.
                            let claim_label = function_claim_label(function_block, claim);
                            if let Some(root) = outcome_proof.as_ref()
                                && let Ensure::Proposition(surface_goal) = claim.clause().ensure()
                            {
                                match close_claim_directly_from_outcome(
                                    root,
                                    function,
                                    claim,
                                    pre_state,
                                    &outcome,
                                    surface_goal,
                                    &rewrite_claim_equalities[claim_index],
                                    &claim_label,
                                    path_index,
                                    &*entry_pure_facts,
                                    execution.paths(),
                                    parameter_binding,
                                    spec_definitions,
                                    ClaimClosureSearch::Solve,
                                    None,
                                )? {
                                    Ok(completed) => {
                                        record_claim_closure(
                                            &mut outcome_proof,
                                            &mut closures,
                                            claims,
                                            &completed_execution,
                                            path_index,
                                            claim_index,
                                            ClaimClosure::by_checked_proposition(
                                                claims[claim_index].key(),
                                                path_index,
                                                &completed.certificate(),
                                                completed.completed_proposition()?,
                                            ),
                                        )?;
                                    }
                                    Err(reason) => closures[claim_index].record_failure(reason),
                                }
                                continue;
                            }
                            // A resource ensure or an effect claim is an exact
                            // check against the path's outcome, not a proof.
                            let ensure_clause = claim.clause();
                            let exact = match ensure_clause.ensure() {
                                Ensure::Resource(_resource) => Some(
                                    required_outcome(&outcome_proof)?
                                        .check_outcome_resource_claim(&completed_execution, *claim),
                                ),
                                Ensure::Proposition(_) => None,
                            };
                            match exact {
                                Some(Ok(checked)) => record_claim_closure(
                                    &mut outcome_proof,
                                    &mut closures,
                                    claims,
                                    &completed_execution,
                                    path_index,
                                    claim_index,
                                    ClaimClosure::resource(ClaimCertificate::ExactCheck, checked),
                                )?,
                                Some(Err(error)) => closures[claim_index].record_failure(error),
                                None if !matches!(outcome, FunctionOutcome::Return { .. }) => {
                                    closures[claim_index].record_failure(ClickError::new(format!(
                                        "`{claim_label}` failed on path {path_index}: {}",
                                        describe_function_outcome(
                                            &outcome,
                                            ParameterBinding::new(
                                                parsed_function.parameters(),
                                                arguments
                                            )
                                        )
                                    )))
                                }
                                None => {
                                    closures[claim_index].record_failure(ClickError::new(format!(
                                        "`{claim_label}` has no outcome Proof to close it from"
                                    )))
                                }
                            }
                        }
                    }

                    if !require_explicit_closers && !super::proof_object::implicit_solve_disabled()
                    {
                        while prove_next_contract_closing_goal(
                            &mut outcome_proof,
                            &mut closing_input,
                            &completed_execution,
                            path_index,
                            has_return_resource_rewrite,
                            &post_return_facts,
                            ClosingProofMode::Implicit,
                        )? {
                            path_grouped_surface_closers.push(ProofTactic::Known);
                        }
                    }

                    if let Some((claim_index, claim)) = main_goal_claim(&outcome_proof, &closures)?
                        .map(|claim_index| (claim_index, &claims[claim_index]))
                    {
                        let claim_label = function_claim_label(function_block, claim);
                        let summary = format!(
                            "`{proof_label}` path {path_index} left `{claim_label}` unproved: the implicit closer could not close it at the end of the proof; establish the facts and resources it needs before then (claim index {claim_index})"
                        );
                        if let Some(error) = closures[claim_index].last_error() {
                            return Err(error.clone().with_context(summary));
                        }
                        return Err(ClickError::new(summary)
                            .with_proof_refusal(crate::surface::ProofRefusal::IncompleteProof));
                    }

                    if let Some(root) = &outcome_proof
                        && let Some(crate::kernel::proof::OutcomeGoal::Closing(kind)) =
                            root.first_open_outcome_goal()?
                    {
                        return Err(root
                            .step_error(format!(
                                "outcome still owes contract closing: {}",
                                kind.description()
                            ))
                            .with_proof_refusal(crate::surface::ProofRefusal::IncompleteProof));
                    }

                    // The checked execution producer owns the specification.
                    // Return-resource rewrites advance that same publication;
                    // ordinary claim goals publish through their retained binding.
                    let input = match closing_input {
                        Some(input) => input,
                        None => contract_closing_input(
                            outcome_proof.as_ref(),
                            &completed_execution,
                            path_index,
                            has_return_resource_rewrite,
                            &post_return_facts,
                        )?,
                    };
                    let checked_specification = input.specification;
                    let specification = checked_specification.specification();
                    let theorem = checked_specification.theorem();
                    // Every theorem of this path shares one copy of the loop
                    // clauses and rules its proof reached.
                    let frontier_loop_clauses: std::sync::Arc<[StructuralClause]> = proof_execution
                        .presentation
                        .frontier_loop_clauses
                        .to_vec()
                        .into();
                    let frontier_loop_rules: std::sync::Arc<[VerifiedLoopRule]> =
                        proof_execution.core.frontier_loop_rules.to_vec().into();
                    for claim in claims {
                        // A path with an outcome holds each claim's evidence on its
                        // goal there. A divergent path holds its claims vacuously.
                        let checked_proposition = outcome_proof
                            .as_ref()
                            .and_then(|root| root.published_contract_claim(&claim.key()));
                        verified.push(VerifiedProgramTheorem {
                            source_path: source_path.to_string(),
                            import_identity: None,
                            artifact_identity: None,
                            target: crate::languages::c::target::CTarget::SUPPORTED,
                            selection: None,
                            // Every theorem of this proof shares one copy of
                            // the function block and of the proof text, so
                            // issuing a theorem per path and claim does not
                            // multiply the proof's size by their number.
                            function_block: std::sync::Arc::clone(function_block),
                            claim: claim.verified_claim(),
                            proof_kind: ProofKind::TacticScript,
                            proof_tactics: Some(std::sync::Arc::clone(certificate_tactics)),
                            expanded_proof: retained_certificate.clone(),
                            expansion_blocker: retained_surface.blocker.clone(),
                            specification: specification.clone(),
                            theorem: theorem.clone(),
                            concrete_loop_execution: proof_execution.core.concrete_loop_execution,
                            frontier_loop_clauses: std::sync::Arc::clone(&frontier_loop_clauses),
                            frontier_loop_rules: std::sync::Arc::clone(&frontier_loop_rules),
                            checked_execution: std::sync::Arc::clone(
                                &provisional_checked_execution,
                            ),
                            checked_proposition,
                            entry_context: proof_context.constants.entry_context.clone(),
                            source_layout: TheoremSourceLayout(Some(
                                proof_context.constants.source_layout.clone(),
                            )),
                        });
                    }
                    if let Some(return_proof) = loop_return {
                        let per_claim = closures
                            .iter()
                            .map(|closure| {
                                closure
                                    .closed()
                                    .map(ClosedClaim::claim_tactics)
                                    .unwrap_or_default()
                                    .to_vec()
                            })
                            .collect::<Vec<_>>();
                        loop_return_closures.push((
                            return_proof.clone(),
                            path_surface_post_tactics,
                            path_grouped_surface_closers,
                            per_claim,
                        ));
                    } else {
                        // Expansion prints what verification holds: the tactics come out
                        // of the closure that accepted the claim, not from a parallel
                        // record that could disagree with it.
                        for (claim_index, closure) in closures.iter().enumerate() {
                            let mut tactics = closure
                                .closed()
                                .map(ClosedClaim::claim_tactics)
                                .unwrap_or_default()
                                .to_vec();
                            if !proof_context.constants.grouped_contract {
                                tactics.extend(path_grouped_surface_closers.iter().cloned());
                            }
                            surface_closers_by_claim[claim_index].push(tactics);
                        }
                        surface_grouped_closers_by_path.push(path_grouped_surface_closers);
                        surface_post_choices_by_path.push(surface_post_choices);
                        if terminal_outcome_selector.is_some() {
                            terminal_outcome_choices.push(terminal_outcome_choice);
                        }
                        surface_post_path_indices.push(path_index);
                        surface_post_tactics_by_path.push(path_surface_post_tactics);
                    }
                    if let Some(previous) = batch_previous_capture.take() {
                        batch_capture_paths.entry(previous).or_default().push((
                            path_index,
                            std::mem::take(&mut path_deferred_capture_tactics),
                            path_deferred_capture_prefix,
                        ));
                    }
                    let implicitly_closable = path_deferred_capture_tactics.is_empty()
                        || (!require_explicit_closers
                            && claims.iter().enumerate().all(|(claim_index, claim)| {
                                !matches!(claim.clause().ensure(), Ensure::Proposition(_))
                                    || closures[claim_index].is_closed()
                            }));
                    batch_implicit_closure.insert(
                        path_index,
                        !require_explicit_closers
                            && claims.iter().enumerate().all(|(index, claim)| {
                                !matches!(claim.clause().ensure(), Ensure::Proposition(_))
                                    || closures[index].is_closed()
                            }),
                    );
                    if visits_selected_capture {
                        deferred_capture_prefixes_by_path.push(path_deferred_capture_prefix);
                        implicit_closure_by_path.push(implicitly_closable);
                        deferred_capture_tactics_by_path.push(path_deferred_capture_tactics);
                        deferred_capture_branches_by_path.push((
                            deferred_capture_branch_path,
                            checked_boolean_return(path.outcome()),
                        ));
                    }
                    outcome_proof
                        .as_ref()
                        .unwrap_or(&proof)
                        .record_accepted_trace(&proof_label, path_index);
                    if let Some(root) = outcome_proof.take() {
                        // Retire only this checked outcome. Sibling paths are
                        // completed by their own retained proofs.
                        outcome_substrate =
                            root.complete_outcome_in(&outcome_substrate, &mut contract_owner)?;
                    }
                    drop(_path_closing_timing);
                }
                Ok(())
            },
        )?;
        if !outcome_substrate.is_complete() {
            return Err(ClickError::new(format!(
                "`{proof_label}` still owns unfinished outcome cases"
            )));
        }
        // This is surface routing, never additional proof authority. If
        // either outcome cannot decide the guard, retain the existing refusal.
        let distinct_terminal_suffixes = surface_post_tactics_by_path
            .windows(2)
            .any(|pair| pair[0] != pair[1])
            || surface_grouped_closers_by_path
                .windows(2)
                .any(|pair| pair[0] != pair[1])
            || surface_closers_by_claim
                .iter()
                .any(|paths| paths.windows(2).any(|pair| pair[0] != pair[1]));
        if terminal_outcome_choices.len() == 2
            && distinct_terminal_suffixes
            && surface_post_choices_by_path.iter().all(Vec::is_empty)
            && let (Some(first), Some(second), Some(condition)) = (
                terminal_outcome_choices[0],
                terminal_outcome_choices[1],
                terminal_outcome_selector,
            )
            && first != second
        {
            for (choices, value) in surface_post_choices_by_path.iter_mut().zip([first, second]) {
                choices.insert(
                    0,
                    SurfacePathChoice {
                        // Generated cases precede written post-execution sites.
                        occurrence: usize::MAX,
                        selector: SurfacePathSelector::Proposition(condition.clone()),
                        value,
                        tactic_offset: 0,
                        if_arm_end: None,
                    },
                );
            }
        }
        // A shared suffix needs no case selector. In particular, loading
        // different cells can produce internal pointer-offset cases whose
        // common proof is already expressible. Preserve an existing terminal
        // selector too; raw statement cases must not replace its checked route.
        if distinct_terminal_suffixes && surface_post_choices_by_path.iter().all(Vec::is_empty) {
            for (choices, path_index) in surface_post_choices_by_path
                .iter_mut()
                .zip(&surface_post_path_indices)
            {
                match direct_view.terminal_statement_choices(*path_index) {
                    Ok(terminal_choices) => *choices = terminal_choices,
                    Err(message) => retained_surface.block(message),
                }
            }
        }
        let completed_strategy = outcome_substrate.finish_contract_execution(contract_owner)?;
        let completed_execution = std::sync::Arc::clone(completed_strategy.execution());
        for theorem in &mut verified {
            theorem.checked_execution = std::sync::Arc::clone(&completed_execution);
        }
        // A context that recorded a proof-branch choice appends its
        // post-execution tactics as a flat suffix after the choice point,
        // where cross-context synthesis will place the surface `if`.
        // Appending them by execution-branch leaf would graft one case's
        // closers onto execution paths the case excluded.
        let append_surface_tactics = |steps: &mut Vec<ProofStep>,
                                      path_tactics: &[Vec<ProofTactic>]|
         -> Result<(), String> {
            if retained_surface.path_choices.is_empty() {
                append_surface_tactics_by_leaf(steps, path_tactics, call_edges.map(Vec::as_slice))
            } else {
                append_surface_tactics_flat(steps, path_tactics)
            }
        };
        // The post-execution tactics, then the closers, each placed at the
        // surface leaf of the paths that produced them.
        let append_post_and_closers = |steps: &mut Vec<ProofStep>,
                                       post: &[Vec<ProofTactic>],
                                       closers: &[Vec<ProofTactic>]|
         -> Result<(), String> {
            if post.iter().any(|tactics| !tactics.is_empty()) {
                append_surface_tactics(steps, post)?;
            }
            if closers.iter().any(|tactics| !tactics.is_empty()) {
                append_surface_tactics(steps, closers)?;
            }
            Ok(())
        };
        let keep_post_execution_scopes = outcome_paths_bind_obtain(&surface_post_choices_by_path);
        let append_paths_by_leaf = |steps: &mut Vec<ProofStep>, closers: &[Vec<ProofTactic>]| {
            append_post_execution_paths_by_surface_leaf(
                steps,
                &surface_post_tactics_by_path,
                closers,
                &surface_post_choices_by_path,
                |index| {
                    direct_view.surface_step_branch_path(
                        surface_post_path_indices[index],
                        &retained_surface.steps,
                    )
                },
                |index| {
                    checked_boolean_return(
                        execution.paths()[surface_post_path_indices[index]].outcome(),
                    )
                },
            )
        };
        let append_scoped_suffix = |steps: &mut Vec<ProofStep>, closers: &[Vec<ProofTactic>]| {
            match synthesize_post_execution_paths(
                &surface_post_tactics_by_path,
                closers,
                &surface_post_choices_by_path,
                &[],
            ) {
                Ok(suffix) => {
                    append_surface_steps_in_order(steps, suffix);
                    Ok(())
                }
                // A common suffix belongs after the execution branches.
                // For distinct suffixes, use the retained branch routes.
                Err(_) => append_paths_by_leaf(steps, closers),
            }
        };
        if proof_context.constants.grouped_contract {
            let mut expanded = retained_surface.clone();
            append_loop_return_closers(&mut expanded.steps, &loop_return_closures, None)?;
            complete_loop_return_expansion(
                expansion_capture.as_deref_mut(),
                &expanded.steps,
                &loop_return_closures,
            )?;
            if keep_post_execution_scopes {
                if let Err(message) =
                    append_scoped_suffix(&mut expanded.steps, &surface_grouped_closers_by_path)
                {
                    expanded.block(message);
                }
            } else if surface_post_choices_by_path
                .iter()
                .any(|choices| !choices.is_empty())
            {
                match synthesize_post_execution_paths(
                    &surface_post_tactics_by_path,
                    &surface_grouped_closers_by_path,
                    &surface_post_choices_by_path,
                    &[],
                ) {
                    Ok(suffix) => {
                        for step in suffix {
                            append_surface_step_to_leaves(&mut expanded.steps, step);
                        }
                    }
                    // Outcomes that share a proof arm but not a C branch
                    // cannot share one suffix after the C `if`; place the
                    // proof cases inside each C leaf instead.
                    Err(message) => {
                        let mut by_leaf = expanded.steps.clone();
                        match append_paths_by_leaf(&mut by_leaf, &surface_grouped_closers_by_path) {
                            Ok(()) => expanded.steps = by_leaf,
                            Err(_) => expanded.block(message),
                        }
                    }
                }
            } else if let Err(message) = append_post_and_closers(
                &mut expanded.steps,
                &surface_post_tactics_by_path,
                &surface_grouped_closers_by_path,
            ) {
                expanded.block(message);
            }
            // One admitted certificate, shared by every theorem this context
            // produced. Admitting it per theorem charged each of them the
            // whole certificate again, and left equal certificates as
            // separate objects for every later comparison to walk.
            let expanded_certificate = expanded
                .blocker
                .is_none()
                .then(|| ProofCertificate::from_steps(expanded.steps.clone()))
                .transpose()?;
            for theorem in &mut verified {
                theorem.expanded_proof = expanded_certificate.clone();
                theorem.expansion_blocker = expanded.blocker.clone();
            }
            // Surface synthesis follows proof contexts, not the number of
            // semantic execution paths they contribute. A proof branch can
            // be vacuous after outcome filtering while its checked
            // surface arm is still required to check the surrounding `if`.
            // Record exactly one builder per declared claim for this context;
            // tying builders to produced theorems silently dropped such arms
            // (and duplicated builders when a context certified many paths).
            let expanded = std::sync::Arc::new(expanded);
            for claim in claims {
                claim_surface_builders.push((claim.verified_claim(), expanded.clone()));
            }
        } else {
            for (claim_index, claim) in claims.iter().enumerate() {
                let mut expanded = retained_surface.clone();
                append_loop_return_closers(
                    &mut expanded.steps,
                    &loop_return_closures,
                    Some(claim_index),
                )?;
                complete_loop_return_expansion(
                    expansion_capture.as_deref_mut(),
                    &expanded.steps,
                    &loop_return_closures,
                )?;
                // A proof case split written after execution is rebuilt from
                // the outcomes' recorded choices, as for a grouped proof.
                // Without it the arms' tactics are emitted with no `if`
                // around them, and lose the case fact each arm relies on.
                let appended = if keep_post_execution_scopes {
                    append_scoped_suffix(
                        &mut expanded.steps,
                        &surface_closers_by_claim[claim_index],
                    )
                } else if surface_post_choices_by_path
                    .iter()
                    .any(|choices| !choices.is_empty())
                {
                    synthesize_post_execution_paths(
                        &surface_post_tactics_by_path,
                        &surface_closers_by_claim[claim_index],
                        &surface_post_choices_by_path,
                        &[],
                    )
                    .map(|suffix| {
                        for step in suffix {
                            append_surface_step_to_leaves(&mut expanded.steps, step);
                        }
                    })
                } else {
                    append_post_and_closers(
                        &mut expanded.steps,
                        &surface_post_tactics_by_path,
                        &surface_closers_by_claim[claim_index],
                    )
                };
                if let Err(message) = appended {
                    expanded.block(message);
                }
                let verified_claim = claim.verified_claim();
                // One admitted certificate per claim, shared by every path
                // that certified it, for the reason above.
                let expanded_certificate = expanded
                    .blocker
                    .is_none()
                    .then(|| ProofCertificate::from_steps(expanded.steps.clone()))
                    .transpose()?;
                for theorem in &mut verified {
                    if theorem.claim == verified_claim {
                        theorem.expanded_proof = expanded_certificate.clone();
                        theorem.expansion_blocker = expanded.blocker.clone();
                    }
                }
                claim_surface_builders.push((verified_claim, std::sync::Arc::new(expanded)));
            }
        }
        if tactic_expansion_capture_is_active(expansion_capture.as_deref())
            && expansion_capture
                .as_ref()
                .is_none_or(|capture| capture.batch.is_none())
        {
            let Some(deferred) = proof_execution
                .presentation
                .expansion
                .deferred_tactic_capture
                .as_ref()
                .or_else(|| {
                    loop_return_closures
                        .iter()
                        .find_map(|(proof, _, _, _)| proof.capture.as_ref())
                })
            else {
                // Structured proofs produce one check context per logical
                // case.  A selected deferred tactic activates the expansion
                // capture while those contexts are being built, but contexts
                // from sibling branches legitimately have no capture.  Let
                // them finish; the matching context records the expansion,
                // or the expansion entry reports that no result was seen.
                if !verified.is_empty() {
                    let preferred = verified
                        .iter()
                        .any(|theorem| !theorem.frontier_loop_rules.is_empty());
                    completed_strategy
                        .with_loop_rules(proof_execution.core.frontier_loop_rules.to_vec().into())
                        .publish(preferred);
                }
                return Ok(verified);
            };
            finish_deferred_expansion(
                expansion_capture.as_deref_mut(),
                deferred,
                &retained_surface,
                &deferred_capture_tactics_by_path,
                &deferred_capture_branches_by_path,
                &implicit_closure_by_path,
                &deferred_capture_prefixes_by_path,
                &surface_post_path_indices,
                &surface_post_tactics_by_path,
                &surface_grouped_closers_by_path,
                call_edges,
            );
        }
        if let Some(capture) = expansion_capture.as_deref_mut()
            && capture.batch.is_some()
        {
            for (index, paths) in batch_capture_paths {
                let Some(deferred) = batch_captures.get(&index) else {
                    continue;
                };
                if let Some(batch) = &mut capture.batch {
                    batch.active_source = Some(deferred.source_index);
                }
                let branches = paths
                    .iter()
                    .map(|(path, _, _)| {
                        (
                            direct_view.surface_branch_path(*path, &deferred.branch_skeleton),
                            checked_boolean_return(execution.paths()[*path].outcome()),
                        )
                    })
                    .collect::<Vec<_>>();
                let prefixes = paths
                    .iter()
                    .map(|(_, _, prefix)| *prefix)
                    .collect::<Vec<_>>();
                let implicit = paths
                    .iter()
                    .map(|(path, tactics, _)| {
                        tactics.is_empty()
                            || batch_implicit_closure.get(path).copied().unwrap_or(false)
                    })
                    .collect::<Vec<_>>();
                let deltas = paths
                    .into_iter()
                    .map(|(_, tactics, _)| tactics)
                    .collect::<Vec<_>>();
                finish_deferred_expansion(
                    Some(capture),
                    deferred,
                    &retained_surface,
                    &deltas,
                    &branches,
                    &implicit,
                    &prefixes,
                    &surface_post_path_indices,
                    &surface_post_tactics_by_path,
                    &surface_grouped_closers_by_path,
                    call_edges,
                );
                if let Some(target) = capture.target_mut(deferred.source_index) {
                    target.replaces_from =
                        crate::surface::expansion::take_expansion_replaces_from();
                }
            }
        }
        if !verified.is_empty() {
            let preferred = verified
                .iter()
                .any(|theorem| !theorem.frontier_loop_rules.is_empty());
            completed_strategy
                .with_loop_rules(proof_execution.core.frontier_loop_rules.to_vec().into())
                .publish(preferred);
        }
        Ok(verified)
    })();
    result.map_err(|error| add_proof_branch_path(error, branch_path))
}

#[allow(clippy::too_many_arguments)]
fn finish_deferred_expansion(
    expansion_capture: Option<&mut ExpansionCapture>,
    deferred: &DeferredTacticCapture,
    retained_surface: &ProofCertificateBuilder,
    deferred_capture_tactics_by_path: &[Vec<ProofTactic>],
    deferred_capture_branches_by_path: &[(Option<Vec<bool>>, Option<bool>)],
    implicit_closure_by_path: &[bool],
    deferred_capture_prefixes_by_path: &[(usize, usize)],
    surface_post_path_indices: &[usize],
    surface_post_tactics_by_path: &[Vec<ProofTactic>],
    surface_grouped_closers_by_path: &[Vec<ProofTactic>],
    call_edges: Option<&Vec<bool>>,
) {
    // A tactic whose claims all closed by exact checks or grouped
    // transitions contributes no surface tactics of its own (see
    // `ClosedClaim::claim_tactics`): its exact expansion is empty and
    // the tactic is simply removed. Grafting the enclosing branch
    // skeleton around empty leaves would instead re-split every
    // already-merged execution path at path end, losing the
    // execution-path/branch-trace pairing certificate validation keeps —
    // proof-level `if` conditions lower at each path's own outcome, so
    // an alien path meets another path's branch conditions as
    // contradictory facts it cannot use.
    let mut capture = ProofCertificateBuilder::default();
    let path_independent_capture = !deferred_capture_tactics_by_path.is_empty()
        && deferred_capture_tactics_by_path
            .windows(2)
            .all(|pair| pair[0] == pair[1]);
    // Paths that disagree — a certificate found on one, the implicit
    // exact closer on the others — cannot be stitched without the
    // branch skeleton. When every path is closable by that exact
    // closer the tactic contributes nothing on any of them and is
    // removed, exactly as when no path produced a certificate; the
    // certificate one path happened to find is not evidence the
    // others needed one.
    let contributes_no_tactics = deferred_capture_tactics_by_path
        .iter()
        .all(|tactics| tactics.is_empty())
        || (!path_independent_capture
            && deferred_capture_branches_by_path
                .iter()
                .all(|(branch, _)| branch.is_none())
            && implicit_closure_by_path.iter().all(|closable| *closable));
    if !contributes_no_tactics && path_independent_capture {
        // Every path produced the same checked expansion. It stands
        // at the selected source site, including inside an existing
        // proof branch. Repeating that branch here could evaluate a
        // caller local after return, when it is no longer in scope.
        match ProofCertificate::from_proof_tactics(&deferred_capture_tactics_by_path[0]) {
            Ok(proof) => capture.steps = proof.steps().to_vec(),
            Err(error) => capture.block(format!(
                "deferred expansion produced a non-simple proof: {error}"
            )),
        }
    } else if !contributes_no_tactics
        && deferred.can_expand_execution_prefix
        && surface_has_repeated_branch_conditions(&retained_surface.steps)
        && deferred.post_execution_index != DeferredTacticCapture::NESTED
        && retained_surface.path_choices.is_empty()
        && deferred_capture_tactics_by_path.len() == surface_post_path_indices.len()
    {
        // Reuse the execution prefix at its original branch points.
        // Repeating only its guards at function exit can reread a
        // mutable local or a loop statement's overwritten state.
        // The selected closer therefore expands the checked prefix
        // too, putting each delta in the leaf where it was checked.
        capture = retained_surface.clone();
        // Retain offsets during checking; copy syntax only now,
        // when it belongs to the requested expansion's output.
        let path_tactics = deferred_capture_prefixes_by_path
            .iter()
            .zip(deferred_capture_tactics_by_path)
            .enumerate()
            .map(|(index, ((post_end, closer_end), delta))| {
                surface_post_tactics_by_path[index][..*post_end]
                    .iter()
                    .chain(&surface_grouped_closers_by_path[index][..*closer_end])
                    .chain(delta)
                    .cloned()
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        if let Err(message) = append_surface_tactics_by_leaf(
            &mut capture.steps,
            &path_tactics,
            call_edges.map(Vec::as_slice),
        ) {
            capture.block(message);
        } else {
            crate::surface::expansion::note_expansion_replaces_from(0);
        }
    } else if !contributes_no_tactics {
        let mut capture_tactics = deferred.branch_skeleton.as_ref().clone();
        let mut split_leaves = captured_boolean_return_splits(
            deferred_capture_tactics_by_path,
            deferred_capture_branches_by_path,
        );
        for ((branch_path, _), path_tactics) in deferred_capture_branches_by_path
            .iter()
            .zip(deferred_capture_tactics_by_path)
        {
            let appended = match branch_path {
                Some(branch_path) => {
                    let split;
                    let suffix = if let Some(leaf) = split_leaves.get_mut(branch_path) {
                        split = leaf.take();
                        let Some(tactics) = &split else {
                            continue;
                        };
                        tactics
                    } else {
                        path_tactics
                    };
                    append_surface_tactics_at_branch_path(&mut capture_tactics, branch_path, suffix)
                }
                None => append_surface_tactics_at_every_leaf(&mut capture_tactics, path_tactics),
            };
            if let Err(message) = appended {
                capture.block(message);
                break;
            }
        }
        if capture.blocker.is_none() {
            match ProofCertificate::from_proof_tactics(&capture_tactics) {
                Ok(proof) => capture.steps = proof.steps().to_vec(),
                Err(error) => capture.block(format!(
                    "deferred expansion produced a non-simple proof: {error}"
                )),
            }
        }
    }
    finish_tactic_expansion_capture(expansion_capture, &capture, contributes_no_tactics);
}

fn captured_boolean_return_splits<'a>(
    tactics: &[Vec<ProofTactic>],
    branches: &'a [(Option<Vec<bool>>, Option<bool>)],
) -> BTreeMap<&'a Vec<bool>, Option<Vec<ProofTactic>>> {
    // An unknown route may share any leaf. Keep the ordinary stitch in
    // that case so no outcome is omitted from a generated result split.
    let mut leaves = BTreeMap::<_, Vec<_>>::new();
    for ((branch, boolean_return), tactics) in branches.iter().zip(tactics) {
        let Some(branch) = branch else {
            return BTreeMap::new();
        };
        leaves
            .entry(branch)
            .or_default()
            .push((*boolean_return, tactics));
    }
    leaves
        .into_iter()
        .filter_map(|(branch, paths)| {
            if paths.windows(2).all(|pair| pair[0].1 == pair[1].1) {
                return None;
            }
            let proofs = paths
                .into_iter()
                .map(|(value, tactics)| {
                    Some((value, ProofCertificate::from_proof_tactics(tactics).ok()?))
                })
                .collect::<Option<Vec<_>>>()?;
            let split =
                boolean_return_split(proofs.iter().map(|(value, proof)| (*value, proof.steps())))?
                    .ok()?;
            Some((
                branch,
                Some(ProofCertificate::from_validated_steps(vec![split]).to_proof_tactics()),
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deferred_cases_retain_prefixes_closers_and_duplicate_execution_paths() {
        let condition = ClickProposition::PredicateCall {
            name: "P".into(),
            arguments: vec![],
        };
        let choices = [true, true, false, false].map(|value| {
            vec![SurfacePathChoice {
                occurrence: 7,
                selector: SurfacePathSelector::Proposition(condition.clone()),
                value,
                tactic_offset: 1,
                if_arm_end: None,
            }]
        });
        let tactics = [true, true, false, false].map(|value| {
            vec![
                ProofTactic::Step,
                if value {
                    ProofTactic::Known
                } else {
                    ProofTactic::Normalize
                },
            ]
        });
        let closers = vec![vec![ProofTactic::Normalize]; 4];
        let steps = synthesize_post_execution_paths(&tactics, &closers, &choices, &[]).unwrap();
        let [
            ProofStep::Step,
            ProofStep::If {
                condition: actual,
                then_proof,
                else_proof,
                ..
            },
        ] = steps.as_slice()
        else {
            panic!("deferred branch lost its shared prefix");
        };
        assert_eq!(actual, &condition);
        assert_eq!(
            then_proof.steps(),
            &[ProofStep::Known, ProofStep::Normalize]
        );
        assert_eq!(
            else_proof.steps(),
            &[ProofStep::Normalize, ProofStep::Normalize]
        );
        let mut mismatched = tactics;
        mismatched[1][0] = ProofTactic::Normalize;
        assert!(synthesize_post_execution_paths(&mismatched, &closers, &choices, &[]).is_err());
    }

    #[test]
    fn unsupported_shape_diagnostic_blames_no_tactic() {
        let error =
            checked_driver_refusal("f.ensures_0", &["f.ensures_0".to_string()], Decline::Shape);

        assert!(error.message().contains("no checked proof driver accepts"));
        assert!(
            error
                .message()
                .contains("none reported a tactic it refused")
        );
        assert_eq!(error.kind(), ClickErrorKind::Internal);
        // A decline records no tactic, so none is blamed and the script is
        // not called valid.
        assert!(!error.message().contains("It reached tactic"));
        assert!(!error.message().contains("proof script is valid"));
    }

    #[test]
    fn inconsistent_context_is_not_sibling_path_evidence() {
        let left = MachineTerm::Variable(Variable(1));
        let right = MachineTerm::Variable(Variable(2));
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                },
                true,
            ))
            .assume_proposition(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(right.clone()),
                    right: Box::new(left.clone()),
                },
                true,
            ));
        let right_term = right;
        // A fact whose negation is *exactly* available still registers as a
        // conflict, and the inconsistency guard is what stops that conflict
        // from being read as sibling-path evidence.
        let exactly_refuted = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(right_term.clone()),
                right: Box::new(left.clone()),
            },
            false,
        );
        assert_eq!(
            proof_case_fact_conflicts(&exactly_refuted, &assumptions),
            Err(())
        );

        // An unrelated fact is not evidence either, but for a narrower
        // reason since the general prover left the kernel: the exact routes
        // report no conflict at all rather than deriving one by explosion.
        let unrelated = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(MachineTerm::Variable(Variable(2))),
                right: Box::new(MachineTerm::constant(10)),
            },
            true,
        );
        assert_eq!(
            proof_case_fact_conflicts(&unrelated, &assumptions),
            Ok(false)
        );
    }

    #[test]
    fn consistent_exact_conflict_remains_sibling_path_evidence() {
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(MachineTerm::Variable(Variable(1))),
            right: Box::new(MachineTerm::constant(10)),
        };
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::condition_is(condition.clone(), false));
        let fact = Proposition::condition_is(condition, true);

        assert_eq!(proof_case_fact_conflicts(&fact, &assumptions), Ok(true));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/surface/proof/claim_proofs/tests.rs");
    }
}

#[cfg(test)]
mod evidence_tests {
    use super::*;

    #[test]
    fn outcome_resource_evidence_rejects_missing_wrong_claim_and_wrong_path() {
        let source = r#"
            resource marker() { fact 0 == 0; }
            verifying "zero.c";
            int32 zero() { owns marker(); ensures result == 0; }
        "#;
        let verified =
            verify_c_sources(source, &[("zero.c", "int32 zero() { return 0; }")]).unwrap();
        let resource_claim = verified
            .iter()
            .find(|theorem| {
                matches!(&theorem.claim,
            VerifiedClaim::Ensure { clause, .. } if matches!(clause.ensure(), Ensure::Resource(_)))
            })
            .unwrap();
        let VerifiedClaim::Ensure { index, clause } = &resource_claim.claim else {
            unreachable!()
        };
        let Ensure::Resource(resource) = clause.ensure() else {
            unreachable!()
        };
        let execution = &resource_claim.checked_execution;
        let path = &execution.paths()[0];
        let Proposition::ProgramFunctionVerifies {
            state,
            arguments,
            outcome,
            ..
        } = implication_body(path.theorem().proposition())
        else {
            panic!("checked function path")
        };
        let key = FunctionContractClaimKey::Ensure(*index);
        let facts = PureFactStore::from_ordered(&path.assumptions().pure_facts());
        let checked = prove_ensure_resource(
            execution,
            key.clone(),
            "resource evidence",
            0,
            crate::kernel::ExecutionFacts::new,
            &facts,
            resource,
            clause.borrowed(),
            ParameterBinding::new(&[], arguments),
            state,
            state,
            outcome,
            None,
            false,
        )
        .unwrap();
        let closure = ClaimClosure::resource(ClaimCertificate::GroupedTransition, checked);
        closure.require_evidence(execution, 0, &key).unwrap();
        assert!(closure.require_evidence(execution, 1, &key).is_err());
        assert!(
            closure
                .require_evidence(execution, 0, &FunctionContractClaimKey::Ensure(index + 1))
                .is_err()
        );
        assert!(
            closure
                .require_evidence(&CheckedFunctionExecution::clone(execution), 0, &key)
                .is_err()
        );
        assert!(
            ClaimClosure::default()
                .require_evidence(execution, 0, &key)
                .is_err()
        );
        assert!(
            ClaimClosure::vacuous(execution, 0, key, ClaimCertificate::ExactCheck).is_err(),
            "a returning path cannot supply divergent-claim evidence"
        );
    }

    #[test]
    fn outcome_vacuity_requires_the_checked_divergent_path() {
        let source = r#"
            verifying "spin.c";
            int32 spin() diverges { ensures 0 == 1; } by {
                loop diverges { invariant 0 == 0; initialize by solve();
                    maintain by { step(); }
                }
                solve();
            }
        "#;
        let verified = verify_c_sources(
            source,
            &[("spin.c", "int32 spin() { while (1) {} return 0; }")],
        )
        .unwrap();
        let execution = &verified[0].checked_execution;
        let key = FunctionContractClaimKey::Ensure(0);
        let closure =
            ClaimClosure::vacuous(execution, 0, key.clone(), ClaimCertificate::ExactCheck).unwrap();
        closure.require_evidence(execution, 0, &key).unwrap();
        assert!(closure.require_evidence(execution, 1, &key).is_err());
        assert!(ClaimClosure::vacuous(execution, 1, key, ClaimCertificate::ExactCheck).is_err());
    }
}

/// The entry facts a proof starts from: the kernel's contract entry, seen
/// the way the contract's source states it.
/// The refusal of a return fold whose proof assumed `fact` without the path
/// justifying it. It names the fact as written and is placed at the
/// post-return tactic that introduced it, the first whose successor holds
/// it, with the path's checked proof state for `--trace-proof`. A fact the
/// path already held when execution returned keeps the final tactic's site.
fn unjustified_return_fact_error(
    proof: &Proof<'_>,
    facts_before_tactic: &[(usize, PureFactStore)],
    fact: &Proposition,
    message: &str,
    path_index: usize,
) -> ClickError {
    let introduced_at = facts_before_tactic
        .iter()
        .enumerate()
        .find(|(index, (_, before))| {
            !before.contains(fact)
                && facts_before_tactic
                    .get(index + 1)
                    .map_or(proof.facts(), |(_, after)| after)
                    .contains(fact)
        })
        .map(|(_, (source_index, _))| *source_index)
        .filter(|source_index| *source_index != usize::MAX);
    let site = introduced_at.map_or_else(
        || proof.clone(),
        |source_index| proof.at_source_tactic(source_index),
    );
    site.return_fold_certification_error(message.to_owned(), Some(fact.clone()), path_index)
}

#[cfg(test)]
mod contract_closing_tests {
    use super::*;

    #[test]
    fn missing_kernel_claim_is_refused_during_contract_closing() {
        let function = crate::kernel::program_function(
            ProgramType::Int32,
            "missing",
            vec![],
            crate::kernel::program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let outcome = FunctionOutcome::Return {
            value: crate::kernel::int32(0).into(),
            state: Box::new(ExecutionState::new()),
        };
        let error = contract_closing_goal(
            &function,
            None,
            Some(&FunctionContractClaimTarget::EnsureProposition(0)),
            &ExecutionState::new(),
            &[],
            &outcome,
            &PureFactContext::new(),
            &mut None,
        )
        .unwrap_err();
        assert!(
            error
                .message()
                .contains("no postcondition at contract index 0"),
            "{error}"
        );
    }
}
