use super::*;
#[cfg(test)]
thread_local! {
    static SURFACE_LEAF_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[cfg(test)]
use crate::persistent::persistent_node_allocations;
use crate::surface::planning::proposition_search::PropositionSearch;
#[cfg(test)]
use std::sync::Arc;

/// Identifies the `close_invariants` step of a checked certificate well
/// enough to emit a `click timing:` line for the work its caller does on its
/// behalf: the same claim-relative indices the checked drivers use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct InvariantCloserStep {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) statement_index: usize,
}

/// Where a source tactic's expansion is being captured on this path: the
/// deferred capture selected for a post-execution tactic and the C branch
/// choices enclosing it, which the deferred expansion finalizes against
/// after every path has completed.
#[derive(Clone, Default)]
pub(super) struct ExpansionCursor {
    pub(super) deferred_tactic_capture: Option<DeferredTacticCapture>,
    /// Global source occurrences, not local tactic ordinals: a loop body and
    /// its continuation can reuse a local ordinal.
    pub(super) batch_deferred_captures: imbl::OrdMap<usize, DeferredTacticCapture>,
    pub(super) batch_branch_skeleton: Option<Arc<Vec<ProofTactic>>>,
    pub(super) deferred_expansion_path_choices: PersistentSequence<SurfacePathChoice>,
}

/// One arm of a proof `match` as a path-aligned case.
///
/// `source` is the whole `match` as written, shared by every arm of one plan,
/// so paths that took different arms compare it by pointer. The certificate
/// merge rebuilds the `match` from it, replacing each arm that produced paths
/// with their merged certificate and keeping the written tactics of an arm
/// that produced none — the arm a checked `contradiction` closed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ProofMatchArmCase {
    pub(super) source: Arc<ProofMatch>,
    pub(super) arm: usize,
}

#[derive(Clone)]
pub(super) struct CaseAssumption {
    pub(super) tactic_index: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) fact: Option<Proposition>,
    pub(super) at_function_entry: bool,
    /// Set when this case is one arm of a proof `match` rather than one
    /// polarity of a condition.
    pub(super) match_arm: Option<ProofMatchArmCase>,
}

#[derive(Clone, Default)]
pub(super) struct ProofCertificateBuilder {
    pub(super) steps: Vec<ProofStep>,
    pub(super) blocker: Option<String>,
    pub(super) path_choices: Vec<SurfacePathChoice>,
}

/// The path's surface record: what the constructed certificate's own check
/// knows in the current state. Planning sinks seed from it and write the anchor
/// back; a proof-level case split records its choice here.
#[derive(Clone, Default)]
pub(super) struct SurfaceRecord {
    /// The statement entry the most recent step recorded, which later
    /// snapshot-qualified facts resolve against.
    pub(super) last_step_entry: Option<ProgramPointRef>,
    pub(super) path_choices: Vec<SurfacePathChoice>,
    pub(super) blocker: Option<String>,
    /// Exact facts established by ordinary checked `have` nodes on this
    /// execution path. This separate persistent index lets a strict statement
    /// retry recognize an explicitly retained prerequisite leaf without
    /// scanning the ambient proof context.
    pub(super) retained_have_facts: ProofFacts,
}

#[derive(Clone, PartialEq, Eq)]
pub(super) struct DeferredTacticCapture {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) post_execution_index: usize,
    pub(super) branch_skeleton: Arc<Vec<ProofTactic>>,
    pub(super) can_expand_execution_prefix: bool,
}

impl DeferredTacticCapture {
    /// `post_execution_index` of a capture for a tactic nested in a deferred
    /// `if` arm: it matches by tactic index at whatever drained position.
    pub(super) const NESTED: usize = usize::MAX;
}

/// The answer a completed capture already holds: a nested target's own
/// recorded delta, or the flat tactic's.
fn decided_tactic_expansion(
    capture: &ExpansionCapture,
) -> Option<Result<Vec<ProofTactic>, ClickError>> {
    match &capture.nested {
        Some(nested) => nested.result(),
        None => capture.result.clone(),
    }
    .map(|result| result.map_err(ClickError::new))
}

/// The answer when verification succeeded without recording one.
fn undecided_tactic_expansion(
    capture: &ExpansionCapture,
    site: &ProofSite,
    source_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    if capture.dropped_path_occurrence {
        return Ok(Vec::new());
    }
    if let Some(nested) = &capture.nested {
        return Err(ClickError::new(if capture.result.is_some() {
            format!(
                "the selected tactic is written inside the tactic at source tactic {source_index} of {}; that tactic was checked, but no checked step reported the selected tactic's source path {:?}, so its own expansion could not be isolated (a verifier defect: every checked written tactic reports its path); expand the whole claim with `--claim` instead",
                site.description(),
                nested.path
            )
        } else {
            format!(
                "selected {} proof never checked the `have` at source tactic {source_index} that contains the selected tactic",
                site.description()
            )
        }));
    }
    Err(ClickError::new(format!(
        "selected {} proof has no source tactic {source_index}",
        site.description()
    )))
}

pub(in crate::surface) fn capture_c0_tactic_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
    source_index: usize,
    nested_path: &[usize],
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_nested_tactic(site.clone(), source_index, nested_path);
    let verification =
        verify_c0_sources_with_expansion_capture(click_source, c_sources, &mut capture);
    if let Some(result) = decided_tactic_expansion(&capture) {
        return result;
    }
    match verification {
        Err(error) => {
            match super::tactic_expansion_dependency_context(
                click_source,
                c_sources,
                &site,
                source_index,
            )? {
                Some(context) => Err(error.with_context(format!(
                    "selected tactic expansion failed while checking {context}"
                ))),
                None => Err(error),
            }
        }
        Ok(_) => undecided_tactic_expansion(&capture, &site, source_index),
    }
}

pub(in crate::surface) fn capture_project_tactic_expansion(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    site: ProofSite,
    source_index: usize,
    nested_path: &[usize],
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_nested_tactic(site.clone(), source_index, nested_path);
    let verification = verify_project_with_expansion_capture(project, inputs, &mut capture);
    if let Some(result) = decided_tactic_expansion(&capture) {
        return result;
    }
    verification.and_then(|_| undecided_tactic_expansion(&capture, &site, source_index))
}

/// Captures one tactic's expansion over compiler-prepared inputs.
pub(in crate::surface) fn capture_prepared_tactic_expansion(
    click_source: &str,
    sources: &CSourceContext<'_>,
    site: ProofSite,
    source_index: usize,
    nested_path: &[usize],
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_nested_tactic(site.clone(), source_index, nested_path);
    let verification =
        verify_c0_sources_with_expansion_capture_context(click_source, sources, &mut capture);
    if let Some(result) = decided_tactic_expansion(&capture) {
        return result;
    }
    verification.and_then(|_| undecided_tactic_expansion(&capture, &site, source_index))
}

pub(in crate::surface) fn capture_project_proof_site_expansion(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_site(site.clone());
    let verification = verify_project_with_expansion_capture(project, inputs, &mut capture);
    retained_proof_site_expansion(capture, verification, &site)
}

/// Captures a whole proof site's expansion over compiler-prepared inputs.
pub(in crate::surface) fn capture_prepared_proof_site_expansion(
    click_source: &str,
    sources: &CSourceContext<'_>,
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_site(site.clone());
    let verification =
        verify_c0_sources_with_expansion_capture_context(click_source, sources, &mut capture);
    retained_proof_site_expansion(capture, verification, &site)
}

fn retained_proof_site_expansion<T>(
    capture: ExpansionCapture,
    verification: Result<T, ClickError>,
    site: &ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    if let Some(result) = capture.result {
        return result.map_err(ClickError::new);
    }
    verification?;
    Err(ClickError::new(format!(
        "verification did not retain a certificate for {}",
        site.description()
    )))
}

pub(in crate::surface) fn capture_c0_proof_site_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_site(site.clone());
    let verification =
        verify_c0_sources_with_expansion_capture(click_source, c_sources, &mut capture);
    retained_proof_site_expansion(capture, verification, &site)
}

pub(super) fn record_proof_site_tactic_expansion(
    capture: Option<&mut ExpansionCapture>,
    site: &ProofSite,
    source_index: usize,
    tactics: &[ProofTactic],
) {
    let Some(capture) = capture else {
        return;
    };
    if capture.site != *site {
        return;
    }
    let replaces_from = if capture.batch.is_some() {
        crate::surface::expansion::take_expansion_replaces_from()
    } else {
        None
    };
    let Some(capture) = capture.target_mut(source_index) else {
        return;
    };
    capture.active = true;
    capture.replaces_from = replaces_from.or(capture.replaces_from);
    match &mut capture.result {
        None => capture.result = Some(Ok(tactics.to_vec())),
        Some(Ok(existing)) if existing == tactics => {}
        Some(Ok(_)) => {
            capture.result = Some(Err(
                "selected tactic expands differently across proof obligations".to_string(),
            ));
        }
        Some(Err(_)) => {}
    }
}

/// Notes that the selected source tactic occurrence sits inside a checked
/// execution region the kernel proved infeasible, so the driver drops the
/// region without running it.
///
/// This is only a fallback answer. Verification continues, and an occurrence
/// that also runs on a feasible path records its real expansion into
/// `result`, which wins. Without the note, expansion could not tell a tactic
/// that legitimately performed no checked work on any retained path from a
/// capture the lowering lost, so it reported both as a missing source tactic
/// while `click verify` accepted the proof.
pub(super) fn note_dropped_path_tactic_occurrence(capture: Option<&mut ExpansionCapture>) {
    if let Some(capture) = capture {
        capture.dropped_path_occurrence = true;
    }
}

pub(super) fn capture_selects_source(
    capture: Option<&ExpansionCapture>,
    site: &ProofSite,
    source_index: usize,
) -> bool {
    capture.is_some_and(|capture| capture.selects(site, source_index))
}

pub(super) fn selected_tactic_indices_for_site(
    capture: Option<&ExpansionCapture>,
    site: &ProofSite,
) -> Vec<usize> {
    let Some(capture) = capture.filter(|capture| capture.site == *site) else {
        return Vec::new();
    };
    match &capture.batch {
        Some(batch) => batch.targets.keys().copied().collect(),
        None => capture.source_index.into_iter().collect(),
    }
}

pub(super) fn selected_tactic_index_for_site(
    capture: Option<&ExpansionCapture>,
    site: &ProofSite,
) -> Option<usize> {
    capture
        .filter(|capture| capture.site == *site)
        .and_then(|capture| capture.source_index)
}

pub(super) fn proof_site_for_claims(
    function_block: &FunctionBlock,
    claims: &[FunctionClaimRef<'_>],
    grouped_contract: bool,
) -> Option<ProofSite> {
    let claim = if grouped_contract {
        CProofClaim::Grouped
    } else {
        match claims {
            [FunctionClaimRef::Ensure(index, _)] => CProofClaim::Ensure(*index),
            [FunctionClaimRef::ExceptionalEnsure(index, _)] => {
                CProofClaim::ExceptionalEnsure(*index)
            }
            _ => return None,
        }
    };
    Some(ProofSite::FunctionClaim {
        function_name: function_block.signature().name().to_string(),
        claim,
    })
}

/// Marks the capture active when it matches this tactic. The tactic's
/// expansion itself comes from its builder scope; the capture only decides
/// which tactic's scoped result is the requested one.
pub(super) fn begin_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    source_index: usize,
    cursor: &ExpansionCursor,
    proof_site: Option<&ProofSite>,
) -> bool {
    let Some(capture) = capture else {
        return false;
    };
    if proof_site != Some(&capture.site) {
        return false;
    }
    let outer = capture;
    let Some(capture) = outer.target_mut(source_index) else {
        return false;
    };
    let sibling_branch_capture = capture.active
        && !cursor.deferred_expansion_path_choices.is_empty()
        && capture.source_index == Some(source_index)
        && proof_site == Some(&capture.site);
    if capture.active && !sibling_branch_capture
        || capture.source_index != Some(source_index)
        || proof_site != Some(&capture.site)
    {
        return false;
    }
    capture.active = true;
    if let Some(batch) = &mut outer.batch {
        batch.active_source = Some(source_index);
    }
    true
}

/// `allow_empty` accepts an empty expansion as the exact answer: the selected
/// tactic contributed no surface tactics to the accepted certificate, so the
/// rewrite removes it. Every other caller keeps the empty guard — for them an
/// empty capture means the lowering lost the tactics, not that none exist.
///
/// The first completed capture wins; verification continues normally either
/// way.
pub(super) fn finish_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    proof_certificate_builder: &ProofCertificateBuilder,
    allow_empty: bool,
) {
    let Some(capture) = capture else {
        return;
    };
    let Some(capture) = capture.active_target_mut() else {
        return;
    };
    if capture.result.is_some() {
        return;
    }
    capture.result = Some(match &proof_certificate_builder.blocker {
        Some(blocker) => Err(format!("could not expand selected tactic: {blocker}")),
        None if proof_certificate_builder.steps.is_empty() && !allow_empty => {
            Err("selected tactic produced no standalone surface expansion".to_string())
        }
        None => ProofCertificate::from_steps(proof_certificate_builder.steps.clone())
            .map(|certificate| certificate.to_proof_tactics())
            .map_err(|error| error.raw_summary().to_string()),
    });
}

pub(super) fn tactic_expansion_capture_is_active(capture: Option<&ExpansionCapture>) -> bool {
    capture.is_some_and(|capture| match &capture.batch {
        Some(batch) => batch
            .active_source
            .and_then(|index| batch.targets.get(&index))
            .is_some_and(|target| target.active),
        None => capture.active,
    })
}

/// Takes one path-local selected-tactic expansion while leaving the capture
/// installed for a sibling execution path. Frontier-local `branch` uses this
/// to collect the certificate produced at one shared source occurrence under
/// each C arm before it emits their logical case split.
pub(super) fn take_path_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
) -> Result<Vec<ProofTactic>, ClickError> {
    let Some(capture) = capture else {
        return Err(ClickError::new(
            "selected-tactic expansion capture was lost between branch paths",
        ));
    };
    let capture = capture
        .active_target_mut()
        .ok_or_else(|| ClickError::new("selected branch capture lost its active source"))?;
    let result = capture.result.take().ok_or_else(|| {
        ClickError::new("selected tactic completed without recording its branch expansion")
    })?;
    capture.active = false;
    result.map_err(ClickError::new)
}

pub(super) fn resume_deferred_tactic_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    cursor: &ExpansionCursor,
    proof_site: Option<&ProofSite>,
) -> Result<(), ClickError> {
    let Some(deferred) = &cursor.deferred_tactic_capture else {
        return Ok(());
    };
    let Some(capture) = capture else {
        return Err(ClickError::new(
            "selected-tactic expansion capture was lost before deferred finalization",
        ));
    };
    if proof_site != Some(&capture.site) || !capture.selects(&capture.site, deferred.source_index) {
        return Err(ClickError::new(
            "deferred tactic capture no longer matches the selected proof occurrence",
        ));
    }
    if let Some(batch) = &mut capture.batch {
        batch.active_source = Some(deferred.source_index);
    }
    if let Some(target) = capture.target_mut(deferred.source_index) {
        target.active = true;
    }
    Ok(())
}

#[derive(Clone)]
pub(super) struct SurfacePathChoice {
    pub(super) occurrence: usize,
    pub(super) selector: SurfacePathSelector,
    pub(super) value: bool,
    pub(super) tactic_offset: usize,
}

#[derive(Clone, PartialEq)]
pub(super) enum SurfacePathSelector {
    Proposition(ClickProposition),
    CallOutcome,
}

impl ProofCertificateBuilder {
    pub(super) fn block(&mut self, message: impl Into<String>) {
        if self.blocker.is_none() {
            self.blocker = Some(message.into());
            self.steps.clear();
            self.path_choices.clear();
        }
    }
}

pub(super) fn record_post_execution_surface_tactic(
    surface_recorded: bool,
    path_tactics: &mut Vec<ProofTactic>,
    capture_tactics: &mut Vec<ProofTactic>,
    deferred_capture: Option<&DeferredTacticCapture>,
    post_execution_index: usize,
    tactic_index: usize,
    tactic: ProofTactic,
) {
    if surface_recorded {
        return;
    }
    if deferred_capture.is_some_and(|capture| {
        capture.tactic_index == tactic_index
            && (capture.post_execution_index == post_execution_index
                || capture.post_execution_index == DeferredTacticCapture::NESTED)
    }) {
        capture_tactics.push(tactic.clone());
    }
    path_tactics.push(tactic);
}

fn append_surface_step_to_certificate(proof: &mut ProofCertificate, step: ProofStep) {
    if !proof.is_pruned_execution_arm() {
        append_surface_step_to_leaves(proof.steps_mut(), step);
    }
}

pub(super) fn append_surface_step_to_leaves(steps: &mut Vec<ProofStep>, step: ProofStep) {
    #[cfg(test)]
    SURFACE_LEAF_VISITS.with(|visits| visits.set(visits.get() + 1));
    if matches!(steps.last(), Some(ProofStep::Contradiction(_))) {
        return;
    }
    if let Some(ProofStep::Match {
        scrutinee, arms, ..
    }) = steps.last_mut()
    {
        // The terminal join retains a path selector for deferred operations.
        // Serialize those operations inside the original lexical constructor
        // arms, not after the match where field names escape.
        let selected = (0..arms.len())
            .map(|index| match_arm_suffix(&step, scrutinee, arms, index))
            .collect::<Option<Vec<_>>>();
        match selected {
            Some(per_arm) => {
                for (arm, suffix) in arms.iter_mut().zip(per_arm) {
                    for next in suffix {
                        append_surface_step_to_certificate(&mut arm.proof, next);
                    }
                }
            }
            None => {
                for arm in arms {
                    append_surface_step_to_certificate(&mut arm.proof, step.clone());
                }
            }
        }
        return;
    }
    if let Some(ProofStep::If {
        condition: existing_condition,
        then_proof,
        else_proof,
        ..
    }) = steps.last_mut()
    {
        if let ProofStep::If {
            condition,
            then_proof: selected_then,
            else_proof: selected_else,
            ..
        } = &step
            && condition == existing_condition
        {
            for next in selected_then.steps() {
                append_surface_step_to_certificate(then_proof, next.clone());
            }
            for next in selected_else.steps() {
                append_surface_step_to_certificate(else_proof, next.clone());
            }
            return;
        }
        append_surface_step_to_certificate(then_proof, step.clone());
        append_surface_step_to_certificate(else_proof, step);
    } else if let Some(ProofStep::CallOutcomes {
        returned_proof,
        threw_proof,
    }) = steps.last_mut()
    {
        if let ProofStep::CallOutcomes {
            returned_proof: selected_returned,
            threw_proof: selected_threw,
        } = &step
        {
            for next in selected_returned.steps() {
                append_surface_step_to_certificate(returned_proof, next.clone());
            }
            for next in selected_threw.steps() {
                append_surface_step_to_certificate(threw_proof, next.clone());
            }
            return;
        }
        append_surface_step_to_certificate(returned_proof, step.clone());
        append_surface_step_to_certificate(threw_proof, step);
    } else {
        steps.push(step);
    }
}

/// Resolves a deferred step against one constructor arm of an enclosing
/// `match`.
///
/// A match of any width is joined by a chain of two-way group splits, so a
/// deferred operation arrives as a nested `if` tree whose conditions select
/// constructor subsets. Following the chain down to `index` gives that arm
/// exactly the operations its own path ran. `None` means the step is an
/// ordinary surface `if` that belongs in every arm; cloning the whole tree
/// into every arm instead would re-emit the complete N-leaf join tree N times,
/// making the certificate quadratic in the constructor count.
fn match_arm_suffix(
    step: &ProofStep,
    scrutinee: &ContractExpression,
    arms: &[CertificateInductionArm],
    index: usize,
) -> Option<Vec<ProofStep>> {
    let ProofStep::If {
        condition,
        then_proof,
        else_proof,
        ..
    } = step
    else {
        return None;
    };
    let selection = match_arm_selection(condition, scrutinee, arms)?;
    let side = if *selection.get(index)? {
        then_proof
    } else {
        else_proof
    };
    let mut suffix = Vec::with_capacity(side.steps().len());
    for next in side.steps() {
        match match_arm_suffix(next, scrutinee, arms, index) {
            Some(nested) => suffix.extend(nested),
            None => suffix.push(next.clone()),
        }
    }
    Some(suffix)
}

/// Reads a group-split condition as the constructor subset it selects.
///
/// The condition a match group split writes is a match over the same
/// scrutinee, arm for arm, whose body is `1` on the selected constructors and
/// `0` on the rest, compared against `1`. `Some(selection)` holds one flag per
/// constructor arm, in arm order; `None` means the condition is an ordinary
/// surface `if` that belongs in every arm.
///
/// A group split always separates the constructors into two non-empty sides,
/// so a condition that selects all of them or none of them is not one, and
/// keeping both sides for it preserves the earlier two-constructor rule.
fn match_arm_selection(
    condition: &ClickProposition,
    scrutinee: &ContractExpression,
    arms: &[CertificateInductionArm],
) -> Option<Vec<bool>> {
    let ClickProposition::Comparison {
        left:
            ContractExpression::AlgebraicMatch {
                scrutinee: selected,
                arms: selector_arms,
            },
        operator: ComparisonOperator::Equal,
        right:
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(Bitvector32Term::Constant(
                1,
            )))),
    } = condition
    else {
        return None;
    };
    if arms.len() != selector_arms.len() || selected.as_ref() != scrutinee {
        return None;
    }
    let selection = arms
        .iter()
        .zip(selector_arms)
        .map(|(arm, selector)| {
            let ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(value),
            ))) = &selector.body
            else {
                return None;
            };
            (arm.type_name == selector.type_name
                && arm.variant == selector.variant
                && arm.bindings == selector.bindings
                && *value <= 1)
                .then_some(*value == 1)
        })
        .collect::<Option<Vec<_>>>()?;
    (selection.iter().any(|selected| *selected) && selection.iter().any(|selected| !selected))
        .then_some(selection)
}

pub(super) fn append_surface_tactics_by_leaf(
    steps: &mut Vec<ProofStep>,
    path_tactics: &[Vec<ProofTactic>],
    call_edges: Option<&[bool]>,
) -> Result<(), String> {
    let path_steps = path_tactics
        .iter()
        .map(|tactics| {
            ProofCertificate::from_proof_tactics(tactics)
                .map(ProofCertificate::into_steps)
                .map_err(|error| format!("path contained a non-simple tactic: {error:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(common) = path_steps.first()
        && path_steps.iter().all(|path| path == common)
    {
        for step in common {
            append_surface_step_to_leaves(steps, step.clone());
        }
        return Ok(());
    }
    if let Some([first, second]) = call_edges
        && first != second
        && path_steps.len() == 2
    {
        let returned_steps = &path_steps[usize::from(!*first)];
        let threw_steps = &path_steps[usize::from(*first)];
        if let Some(ProofStep::CallOutcomes {
            returned_proof,
            threw_proof,
        }) = steps.last_mut()
        {
            returned_proof
                .steps_mut()
                .extend(returned_steps.iter().cloned());
            threw_proof.steps_mut().extend(threw_steps.iter().cloned());
            return Ok(());
        }
        if !matches!(
            steps.last(),
            Some(ProofStep::If { .. } | ProofStep::Match { .. })
        ) {
            steps.push(ProofStep::CallOutcomes {
                returned_proof: Box::new(
                    ProofCertificate::from_steps(returned_steps.clone())
                        .map_err(|error| error.raw_summary().to_string())?,
                ),
                threw_proof: Box::new(
                    ProofCertificate::from_steps(threw_steps.clone())
                        .map_err(|error| error.raw_summary().to_string())?,
                ),
            });
            return Ok(());
        }
    }

    fn append_certificate(
        proof: &mut ProofCertificate,
        path_steps: &[Vec<ProofStep>],
        next_path: &mut usize,
    ) {
        if !proof.is_pruned_execution_arm() {
            append(proof.steps_mut(), path_steps, next_path);
        }
    }

    pub(super) fn append(
        steps: &mut Vec<ProofStep>,
        path_steps: &[Vec<ProofStep>],
        next_path: &mut usize,
    ) {
        #[cfg(test)]
        SURFACE_LEAF_VISITS.with(|visits| visits.set(visits.get() + 1));
        if matches!(steps.last(), Some(ProofStep::Contradiction(_))) {
            return;
        }
        if let Some(ProofStep::Match { arms, .. }) = steps.last_mut() {
            for arm in arms {
                append_certificate(&mut arm.proof, path_steps, next_path);
            }
            return;
        }
        if let Some(ProofStep::If {
            then_proof,
            else_proof,
            ..
        }) = steps.last_mut()
        {
            append_certificate(then_proof, path_steps, next_path);
            append_certificate(else_proof, path_steps, next_path);
        } else if let Some(ProofStep::CallOutcomes {
            returned_proof,
            threw_proof,
        }) = steps.last_mut()
        {
            // A call fork joins its returned arm's paths before its threw
            // arm's, as a C `if` joins then before else.
            append_certificate(returned_proof, path_steps, next_path);
            append_certificate(threw_proof, path_steps, next_path);
        } else if let Some(suffix) = path_steps.get(*next_path) {
            steps.extend(suffix.iter().cloned());
            *next_path += 1;
        }
    }

    let mut next_path = 0;
    append(steps, &path_steps, &mut next_path);
    if next_path == path_steps.len() {
        Ok(())
    } else {
        Err(format!(
            "surface/certificate path coverage diverged at p{next_path}: surface has {next_path} paths but frame certificate has {}",
            path_steps.len()
        ))
    }
}

/// The steps a branch path continues through when a certificate ends in a
/// proof `match` with exactly one arm, such as a match on a single-variant
/// model field: every path takes that arm, so it selects nothing and the
/// path's later surface `if`s sit inside it. A match with several arms is a
/// decision of its own and stops the walk.
pub(super) fn through_single_arm_matches(mut steps: &[ProofStep]) -> &[ProofStep] {
    while let Some(ProofStep::Match { arms, .. }) = steps.last()
        && let [arm] = arms.as_slice()
    {
        steps = arm.proof.steps();
    }
    steps
}

/// [`through_single_arm_matches`] for a certificate being extended.
pub(super) fn through_single_arm_matches_mut(
    mut steps: &mut Vec<ProofStep>,
) -> &mut Vec<ProofStep> {
    while matches!(steps.last(), Some(ProofStep::Match { arms, .. }) if arms.len() == 1) {
        let Some(ProofStep::Match { arms, .. }) = steps.last_mut() else {
            unreachable!()
        };
        steps = arms[0].proof.steps_mut();
    }
    steps
}

/// Appends a suffix at the one leaf of a surface certificate selected by
/// `branch_path`, following each terminal surface `if` outermost first. The
/// leaf takes the suffix the way [`append_surface_step_to_leaves`] would.
pub(super) fn append_surface_steps_at_step_branch_path(
    steps: &mut Vec<ProofStep>,
    branch_path: &[bool],
    suffix: Vec<ProofStep>,
) -> Result<(), String> {
    let mut current = through_single_arm_matches_mut(steps);
    for selected_then in branch_path {
        let Some(ProofStep::If {
            then_proof,
            else_proof,
            ..
        }) = current.last_mut()
        else {
            return Err(
                "execution path selects more surface branches than the certificate has".to_string(),
            );
        };
        current = through_single_arm_matches_mut(if *selected_then {
            then_proof.steps_mut()
        } else {
            else_proof.steps_mut()
        });
    }
    if matches!(current.last(), Some(ProofStep::If { .. })) {
        return Err("execution path stops before its surface branch leaf".to_string());
    }
    for step in suffix {
        append_surface_step_to_leaves(current, step);
    }
    Ok(())
}

/// Appends one context's post-execution surface tactics as a flat top-level
/// suffix. A proof-branch context records its branch decision as a
/// [`SurfacePathChoice`]; the tactics it runs after that decision belong after
/// the branch choice — where cross-context synthesis will place the surface
/// `if` — not inside the leaves of an earlier execution branch, which would
/// graft one case's closers onto execution paths the case excluded.
pub(super) fn append_surface_tactics_flat(
    steps: &mut Vec<ProofStep>,
    path_tactics: &[Vec<ProofTactic>],
) -> Result<(), String> {
    let Some(common) = path_tactics.first() else {
        return Ok(());
    };
    if !path_tactics.iter().all(|tactics| tactics == common) {
        return Err(
            "proof-branch context paths need differing surface tactics after the branch choice"
                .to_string(),
        );
    }
    let proof = ProofCertificate::from_proof_tactics(common)
        .map_err(|error| format!("path contained a non-simple tactic: {error:?}"))?;
    // A proof `match` is a branch choice whose arms bind names. The tactics
    // that follow it were written inside an arm and may read those names, so
    // they go back inside the arms the match left open, not after it.
    if matches!(steps.last(), Some(ProofStep::Match { .. })) {
        for step in proof.into_steps() {
            append_surface_step_to_leaves(steps, step);
        }
    } else {
        steps.extend(proof.into_steps());
    }
    Ok(())
}

/// Appends a path-independent suffix at every leaf of a surface tactic tree.
/// An empty leaf takes the suffix; a leaf that already carries different
/// tactics is a stitching conflict.
pub(super) fn append_surface_tactics_at_every_leaf(
    tactics: &mut Vec<ProofTactic>,
    suffix: &[ProofTactic],
) -> Result<(), String> {
    if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
        append_surface_tactics_at_every_leaf(&mut proof_if.then_tactics, suffix)?;
        append_surface_tactics_at_every_leaf(&mut proof_if.else_tactics, suffix)?;
        return Ok(());
    }
    if let Some(ProofTactic::CallOutcomes(outcomes)) = tactics.last_mut() {
        append_surface_tactics_at_every_leaf(&mut outcomes.returned_tactics, suffix)?;
        append_surface_tactics_at_every_leaf(&mut outcomes.threw_tactics, suffix)?;
        return Ok(());
    }
    if tactics.is_empty() {
        tactics.extend(suffix.iter().cloned());
        Ok(())
    } else if tactics == suffix {
        Ok(())
    } else {
        Err(
            "a path-independent tactic expansion conflicts with a leaf's existing expansion"
                .to_string(),
        )
    }
}

pub(super) fn append_surface_tactics_at_branch_path(
    tactics: &mut Vec<ProofTactic>,
    branch_path: &[bool],
    suffix: &[ProofTactic],
) -> Result<(), String> {
    pub(super) fn append(
        tactics: &mut Vec<ProofTactic>,
        branch_path: &[bool],
        next_branch: usize,
        suffix: &[ProofTactic],
    ) -> Result<(), String> {
        if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
            let selected_then = *branch_path.get(next_branch).ok_or_else(|| {
                "surface branch skeleton has more branches than its execution path".to_string()
            })?;
            return append(
                if selected_then {
                    &mut proof_if.then_tactics
                } else {
                    &mut proof_if.else_tactics
                },
                branch_path,
                next_branch + 1,
                suffix,
            );
        }
        if let Some(ProofTactic::CallOutcomes(outcomes)) = tactics.last_mut() {
            let returned = *branch_path.get(next_branch).ok_or_else(|| {
                "surface call skeleton has more branches than its execution path".to_string()
            })?;
            return append(
                if returned {
                    &mut outcomes.returned_tactics
                } else {
                    &mut outcomes.threw_tactics
                },
                branch_path,
                next_branch + 1,
                suffix,
            );
        }
        if next_branch != branch_path.len() {
            return Err(format!(
                "execution path has {} branches but the surface skeleton has {next_branch}",
                branch_path.len()
            ));
        }
        if tactics.is_empty() {
            tactics.extend(suffix.iter().cloned());
        } else if tactics != suffix {
            return Err(
                "two execution paths require different tactic expansions at one surface leaf"
                    .to_string(),
            );
        }
        Ok(())
    }

    append(tactics, branch_path, 0, suffix)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn surface_branch_path_for_outcome(
    tactics: &[ProofTactic],
    available: &(impl PropositionSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    recorded_snapshots: &RecordedSnapshots,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<bool>, String> {
    let mut branch_path = Vec::new();
    let mut current = tactics;
    loop {
        let Some(proof_if) = current.iter().rev().find_map(|tactic| match tactic {
            ProofTactic::If(proof_if) => Some(proof_if),
            _ => None,
        }) else {
            return Ok(branch_path);
        };
        let lowered = lower_outcome_proposition_with_recorded_snapshots(
            parameter_binding,
            pre_state,
            post_state,
            result,
            available,
            &proof_if.condition,
            spec_definitions,
            recorded_snapshots,
        )?;
        let assumptions = assumptions_from_propositions(available);
        let is_true = exact_fact_is_available(&lowered, available) || assumptions.proves(&lowered);
        let is_false = available
            .propositions()
            .any(|fact| propositions_are_exact_negations(fact, &lowered))
            || fact_conflicts_with_assumptions(&lowered, &assumptions);
        let selected_then = match (is_true, is_false) {
            (true, false) => true,
            (false, true) => false,
            (false, false) => {
                return Err(format!(
                    "execution path does not decide surface branch `{}`",
                    describe_click_proposition(&proof_if.condition)
                ));
            }
            (true, true) => {
                return Err(format!(
                    "execution path proves both sides of surface branch `{}`",
                    describe_click_proposition(&proof_if.condition)
                ));
            }
        };
        branch_path.push(selected_then);
        current = if selected_then {
            &proof_if.then_tactics
        } else {
            &proof_if.else_tactics
        };
    }
}

/// Keeps the outermost surface case split of an already-admitted certificate,
/// recursively. Every retained step came from an admitted certificate.
pub(super) fn surface_branch_skeleton(steps: &[ProofStep]) -> Vec<ProofStep> {
    let Some(branch) = steps
        .iter()
        .rev()
        .find(|step| matches!(step, ProofStep::If { .. } | ProofStep::CallOutcomes { .. }))
    else {
        return Vec::new();
    };
    let arm = |proof: &ProofCertificate| {
        Box::new(ProofCertificate::from_validated_steps(
            surface_branch_skeleton(proof.steps()),
        ))
    };
    vec![match branch {
        ProofStep::If {
            condition,
            ensuring,
            then_proof,
            else_proof,
        } => ProofStep::If {
            condition: condition.clone(),
            ensuring: ensuring.clone(),
            then_proof: arm(then_proof),
            else_proof: arm(else_proof),
        },
        ProofStep::CallOutcomes {
            returned_proof,
            threw_proof,
        } => ProofStep::CallOutcomes {
            returned_proof: arm(returned_proof),
            threw_proof: arm(threw_proof),
        },
        _ => unreachable!(),
    }]
}

/// Repeated guards need their original execution points: their snapshots
/// can denote different iterations by the time execution has returned.
pub(super) fn surface_has_repeated_branch_conditions(steps: &[ProofStep]) -> bool {
    let mut pending = vec![steps];
    let mut conditions = std::collections::HashSet::new();
    while let Some(steps) = pending.pop() {
        for step in steps {
            match step {
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                    ..
                } => {
                    if !conditions.insert(condition) {
                        return true;
                    }
                    pending.push(then_proof.steps());
                    pending.push(else_proof.steps());
                }
                ProofStep::CallOutcomes {
                    returned_proof,
                    threw_proof,
                } => {
                    pending.push(returned_proof.steps());
                    pending.push(threw_proof.steps());
                }
                ProofStep::Match { arms, .. } => {
                    pending.extend(arms.iter().map(|arm| arm.proof.steps()));
                }
                _ => {}
            }
        }
    }
    false
}

pub(super) fn synthesize_surface_alternatives(
    paths: Vec<ProofCertificateBuilder>,
) -> Result<Vec<ProofStep>, String> {
    if paths.is_empty() {
        return Err("certified alternatives contained no paths".to_string());
    }
    if let Some(blocker) = paths.iter().find_map(|path| path.blocker.clone()) {
        return Err(blocker);
    }
    synthesize_surface_paths(paths)
}

pub(super) fn synthesize_surface_paths(
    paths: Vec<ProofCertificateBuilder>,
) -> Result<Vec<ProofStep>, String> {
    if paths.len() == 1 {
        return Ok(paths.into_iter().next().unwrap().steps);
    }
    if paths.iter().all(|path| path.path_choices.is_empty())
        && paths.windows(2).all(|pair| pair[0].steps == pair[1].steps)
    {
        return Ok(paths.into_iter().next().unwrap().steps);
    }
    let first_choice = paths
        .first()
        .and_then(|path| path.path_choices.first())
        .ok_or_else(|| "distinct certified paths have no surface branch condition".to_string())?
        .clone();
    let prefix = paths[0]
        .steps
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
            || choice.selector != first_choice.selector
            || choice.tactic_offset != first_choice.tactic_offset
            || path.steps.get(..choice.tactic_offset) != Some(prefix.as_slice())
        {
            return Err("certified paths do not share one branch prefix".to_string());
        }
        path.steps.drain(..choice.tactic_offset);
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

    let mut steps = prefix;
    let then_proof = Box::new(
        ProofCertificate::from_steps(synthesize_surface_paths(then_paths)?)
            .map_err(|error| error.raw_summary().to_string())?,
    );
    let else_proof = Box::new(
        ProofCertificate::from_steps(synthesize_surface_paths(else_paths)?)
            .map_err(|error| error.raw_summary().to_string())?,
    );
    steps.push(match first_choice.selector {
        SurfacePathSelector::Proposition(condition) => ProofStep::If {
            ensuring: None,
            condition,
            then_proof,
            else_proof,
        },
        SurfacePathSelector::CallOutcome => ProofStep::CallOutcomes {
            returned_proof: then_proof,
            threw_proof: else_proof,
        },
    });
    Ok(steps)
}

#[derive(Clone)]
pub(super) enum PostExecutionTactic {
    Both(ProofBoth),
    Fold(ResourceClause),
    Unfold(ResourceClause),
    Construct(ResourceClause),
    CloseOpen {
        resource: ResourceClause,
        preserve_exposed_body: bool,
    },
    UnfoldPredicate(String),
    /// `unfold(f(args))`, with the `using` guard list when the source wrote
    /// one. A pure-function unfold is proposition-only work, so it defers
    /// past function exit exactly as a predicate unfold does.
    UnfoldFunction {
        application: ClickFunctionApplication,
        premises: Option<Vec<ClickProposition>>,
    },
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
    LetSatisfy(ProofLetSatisfy),
    Witness(ProofWitness),
    /// `intro()`, or `intro() as name` with the chosen name.
    Intro(Option<String>),
    Assumption,
    Normalize,
    NormalizeUsing(Vec<ClickProposition>),
    /// `arithmetic() using { ... }`: the explicit simple closer for an
    /// int32 comparison claim, written where `simp()` would otherwise
    /// search. It closes a focused claim goal from exactly its listed
    /// premises, so it belongs to the same post-execution closer family as
    /// `normalize`.
    ArithmeticUsing(Vec<ClickProposition>),
    /// A retained checked arithmetic certificate, emitted when expanding a
    /// smart `arithmetic() using` closer.  This is deliberately a separate
    /// post-execution operation so rechecking the expansion applies exactly
    /// the supplied certificate and never invokes a planner.
    ArithmeticCertificate(ArithmeticCertificate),
    Rewrite(ClickProposition),
    /// Surface-only control structure scheduled after terminal execution.
    /// The arms contain no semantic state: ordered finalization asks the
    /// focused outcome `Proof` to decide the condition, then applies only the
    /// selected arm's checked operations to that same descendant.
    If {
        condition: ClickProposition,
        /// A terminal join routes its deferred operations through this exact
        /// checked decision. Written post-execution cases have no such route.
        execution_route: Option<usize>,
        then_tactics: Vec<DeferredPostExecutionTactic>,
        else_tactics: Vec<DeferredPostExecutionTactic>,
    },
    CallOutcomes {
        returned_tactics: Vec<DeferredPostExecutionTactic>,
        threw_tactics: Vec<DeferredPostExecutionTactic>,
    },
    /// `auto` closing the pending claims: `simp`, then the rest of
    /// `auto`'s search on each claim `simp` leaves open.
    AutoClose,
    Simp,
    SimpUsing(ProofSimpUsing),
}

#[derive(Clone)]
pub(super) struct PlannedLoopReturns {
    pub(super) paths: Arc<Vec<Arc<LoopReturnProof>>>,
    pub(super) entry_facts: ProofFacts,
}

/// Surface ownership of one returned loop path. It grants no proof authority:
/// finalization still checks the kernel outcome and all contract obligations.
#[derive(Clone)]
pub(super) struct LoopReturnProof {
    pub(super) loop_index: usize,
    pub(super) owners: PersistentSequence<(usize, usize)>,
    pub(super) case_path: Vec<ProofCaseChoice>,
    pub(super) tactics: PersistentSequence<DeferredPostExecutionTactic>,
    pub(super) capture: Option<DeferredTacticCapture>,
    pub(super) batch_captures: imbl::OrdMap<usize, DeferredTacticCapture>,
}

#[derive(Clone)]
pub(super) struct DeferredPostExecutionTactic {
    pub(super) lexical_bindings:
        Option<crate::persistent::PersistentMap<String, ContractExpression>>,
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) tactic: PostExecutionTactic,
    /// The tactic's surface steps are already retained by checked `Proof`
    /// provenance or a legacy surface record. The exit drain performs only
    /// the deferred outcome work and must not record those steps again.
    pub(super) surface_recorded: bool,
}

#[cfg(test)]
mod proof_fact_store_tests {
    use super::*;

    #[test]
    fn outcome_suffix_placement_skips_pruned_arms_in_linear_work() {
        fn branch(then_proof: ProofCertificate, else_proof: ProofCertificate) -> ProofStep {
            ProofStep::If {
                condition: ClickProposition::Comparison {
                    left: ContractExpression::IntegerLiteral("0".into()),
                    operator: ComparisonOperator::Equal,
                    right: ContractExpression::IntegerLiteral("0".into()),
                },
                ensuring: None,
                then_proof: Box::new(then_proof),
                else_proof: Box::new(else_proof),
            }
        }
        fn tree(count: usize) -> ProofCertificate {
            if count == 1 {
                return ProofCertificate::from_steps(vec![branch(
                    ProofCertificate::from_steps(Vec::new()).unwrap(),
                    ProofCertificate::pruned_execution_arm(),
                )])
                .unwrap();
            }
            ProofCertificate::from_steps(vec![branch(tree(count / 2), tree(count / 2))]).unwrap()
        }
        for count in [16, 64, 256] {
            for common in [true, false] {
                let mut steps = tree(count).into_steps();
                let suffixes = (0..count)
                    .map(|index| {
                        vec![ProofTactic::Mark(if common {
                            "shared".into()
                        } else {
                            index.to_string()
                        })]
                    })
                    .collect::<Vec<_>>();
                SURFACE_LEAF_VISITS.with(|visits| visits.set(0));
                append_surface_tactics_by_leaf(&mut steps, &suffixes, None).unwrap();
                let visits = SURFACE_LEAF_VISITS.with(std::cell::Cell::get);
                assert!(visits <= 4 * count, "{count} leaves: {visits} visits");
                let mut pending = vec![steps.as_slice()];
                let mut live = 0;
                let mut pruned = 0;
                while let Some(steps) = pending.pop() {
                    if let [
                        ProofStep::If {
                            then_proof,
                            else_proof,
                            ..
                        },
                    ] = steps
                    {
                        for proof in [else_proof, then_proof] {
                            if proof.is_pruned_execution_arm() {
                                assert!(proof.steps().is_empty());
                                pruned += 1;
                            } else {
                                pending.push(proof.steps());
                            }
                        }
                    } else {
                        let [ProofStep::Mark(value)] = steps else {
                            panic!("live leaf lost its closer");
                        };
                        assert_eq!(
                            value,
                            &if common {
                                "shared".into()
                            } else {
                                live.to_string()
                            }
                        );
                        live += 1;
                    }
                }
                assert_eq!((live, pruned), (count, count));
            }
        }
    }

    #[test]
    fn call_outcome_closers_keep_independent_certificates() {
        let mut steps = vec![ProofStep::Step];
        append_surface_tactics_by_leaf(
            &mut steps,
            &[vec![ProofTactic::Normalize], vec![ProofTactic::Assumption]],
            Some(&[true, false]),
        )
        .unwrap();
        let [
            ProofStep::Step,
            ProofStep::CallOutcomes {
                returned_proof,
                threw_proof,
            },
        ] = steps.as_slice()
        else {
            panic!("distinct call edges must retain a structured certificate");
        };
        assert_eq!(returned_proof.steps(), &[ProofStep::Normalize]);
        assert_eq!(threw_proof.steps(), &[ProofStep::Assumption]);
    }

    #[test]
    fn persistent_sequence_forks_share_history_and_preserve_order() {
        let mut sequence = PersistentSequence::default();
        for value in 0..4096 {
            sequence.push(value);
        }
        let ancestor = sequence.clone();
        assert!(sequence.shares_tail_with(&ancestor));

        sequence.push(4096);

        assert_eq!(
            ancestor.iter().copied().collect::<Vec<_>>(),
            (0..4096).collect::<Vec<_>>()
        );
        assert_eq!(
            sequence.iter().copied().collect::<Vec<_>>(),
            (0..=4096).collect::<Vec<_>>()
        );
        assert!(!sequence.shares_tail_with(&ancestor));
        assert_eq!(ancestor.tail_strong_count(), Some(2));
    }

    #[test]
    fn persistent_sequence_drops_large_shared_histories_iteratively() {
        let mut sequence = PersistentSequence::default();
        for value in 0..16_384 {
            sequence.push(value);
        }
        let ancestor = sequence.clone();
        sequence.push(16_384);

        drop(sequence);
        assert_eq!(ancestor.len(), 16_384);
        drop(ancestor);
    }

    #[test]
    fn execution_frontier_forks_share_remaining_c_and_continuation_history() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut statement = CStatement::Skip;
            for _ in 0..size {
                statement = c_seq(CStatement::Skip, statement);
            }
            let remaining = Arc::new(statement);
            let mut frontier = ExecutionFrontier {
                position: FrontierPosition::StatementEntry {
                    remaining: remaining.clone(),
                },
                continuations: PersistentSequence::default(),
                ..ExecutionFrontier::default()
            };
            frontier.continuations.push(ProofExecutionContinuation {
                remaining: Some(remaining.clone()),
                next_statement_index: 1,
                loop_exit_statement_index: 2,
                exceptional: None,
            });
            let ancestor = frontier.clone();

            let (
                FrontierPosition::StatementEntry {
                    remaining: fork_remaining,
                },
                FrontierPosition::StatementEntry {
                    remaining: ancestor_remaining,
                },
            ) = (&frontier.position, &ancestor.position)
            else {
                panic!("test frontiers should remain at statement entry")
            };
            assert!(Arc::ptr_eq(fork_remaining, ancestor_remaining));
            assert!(
                frontier
                    .continuations
                    .shares_tail_with(&ancestor.continuations),
                "size {size} frontier clone copied its continuation history"
            );

            frontier.continuations.push(ProofExecutionContinuation {
                remaining: Some(remaining.clone()),
                next_statement_index: 2,
                loop_exit_statement_index: 3,
                exceptional: None,
            });
            assert!(
                frontier
                    .continuations
                    .tail_parent_is(&ancestor.continuations),
                "the local continuation should point to the shared ancestor tail"
            );
            assert_eq!(ancestor.continuations.len(), 1);
            assert_eq!(frontier.continuations.len(), 2);
            assert_eq!(
                frontier
                    .continuations
                    .pop()
                    .expect("local continuation")
                    .next_statement_index,
                2
            );
            assert!(
                frontier
                    .continuations
                    .shares_tail_with(&ancestor.continuations),
                "popping the local suffix should restore the shared ancestor stack"
            );
        }
    }

    #[test]
    fn persistent_ordered_set_forks_and_local_insertions_scale_logarithmically() {
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut set = PersistentOrderedSet::default();
            for value in 0..size {
                assert!(set.insert(value));
            }
            let ancestor = set.clone();
            assert!(set.shares_storage_with(&ancestor));

            let before = persistent_node_allocations();
            assert!(set.insert(size));
            let allocations = persistent_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 4 * logarithmic_height + 8;
            assert!(
                allocations <= allocation_bound,
                "size {size} local insertion allocated {allocations} set nodes (bound {allocation_bound})"
            );
            assert!(!ancestor.contains(&size));
            assert!(set.contains(&size));
            assert_eq!(
                set.iter().copied().collect::<Vec<_>>(),
                (0..=size).collect::<Vec<_>>()
            );

            let before_duplicate = persistent_node_allocations();
            assert!(!set.insert(size));
            assert_eq!(persistent_node_allocations(), before_duplicate);
        }
    }

    #[test]
    fn ordered_set_introduced_since_reports_only_new_members() {
        let mut set = PersistentOrderedSet::default();
        set.insert(1u32);
        set.insert(2);
        let ancestor = set.clone();
        set.insert(3);
        set.insert(2);
        set.insert(4);

        assert_eq!(set.introduced_since(&ancestor), Some(vec![3, 4]));
        assert_eq!(ancestor.introduced_since(&ancestor), Some(Vec::new()));
        assert_eq!(ancestor.introduced_since(&set), None);
    }

    #[test]
    fn shared_vec_suffix_since_reports_the_appended_entries() {
        let mut history = SharedVec::from(vec![1u32, 2]);
        let ancestor = history.clone();
        history.push(3);
        history.push(4);

        assert_eq!(history.suffix_since(&ancestor), Some(&[3u32, 4][..]));
        assert_eq!(ancestor.suffix_since(&ancestor), Some(&[][..]));
        assert_eq!(ancestor.suffix_since(&history), None);
    }
}

pub(super) fn post_execution_tactic_timing(
    post_tactic: &PostExecutionTactic,
) -> (&'static str, &'static str) {
    match post_tactic {
        PostExecutionTactic::Both(_) => ("both", "control"),
        PostExecutionTactic::Apply(_) => ("apply", "smart"),
        PostExecutionTactic::Have(have) => (
            "have",
            if smart_simp_unfold_prefix(&have.proof).is_some() {
                "smart"
            } else {
                "control"
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
        PostExecutionTactic::Simp | PostExecutionTactic::SimpUsing(_) => ("simp", "smart"),
        PostExecutionTactic::AutoClose => ("auto", "smart"),
        PostExecutionTactic::Fold(_) => ("fold", "simple"),
        PostExecutionTactic::Unfold(_) => ("unfold", "simple"),
        PostExecutionTactic::Construct(_) => ("construct", "simple"),
        PostExecutionTactic::CloseOpen { .. } => ("open", "control"),
        PostExecutionTactic::UnfoldPredicate(_) => ("unfold", "simple"),
        PostExecutionTactic::UnfoldFunction { .. } => ("unfold", "simple"),
        PostExecutionTactic::ApplyUsing { .. } => ("apply", "simple"),
        PostExecutionTactic::Choose(_) => ("choose", "simple"),
        PostExecutionTactic::LetSatisfy(_) => ("obtain", "simple"),
        PostExecutionTactic::Witness(_) => ("witness", "simple"),
        PostExecutionTactic::Intro(_) => ("intro", "simple"),
        PostExecutionTactic::Assumption => ("assumption", "simple"),
        PostExecutionTactic::Normalize => ("normalize", "simple"),
        PostExecutionTactic::NormalizeUsing(_) => ("normalize", "simple"),
        PostExecutionTactic::ArithmeticUsing(_) => ("arithmetic", "smart"),
        PostExecutionTactic::ArithmeticCertificate(_) => ("arithmetic_certificate", "simple"),
        PostExecutionTactic::Rewrite(_) => ("rewrite", "simple"),
        PostExecutionTactic::If { .. } => ("if", "control"),
        PostExecutionTactic::CallOutcomes { .. } => ("outcomes", "control"),
    }
}

/// The execution data that lowering and fixed-state proofs read: the frontier,
/// the recorded snapshots, the surface spellings, the effect
/// facts, and the state `old(...)` resolves to. Owners build it from
/// wherever they keep those fields, so consumers do not depend on the
/// check bag's layout.
#[derive(Clone, Copy)]
pub(super) struct ExecutionView<'a> {
    pub(super) frontier: &'a ExecutionFrontier,
    pub(super) recorded_snapshots: &'a RecordedSnapshots,
    pub(super) surface_propositions: &'a SurfacePropositionMap,
    pub(super) effect_facts: &'a ExecutionFacts,
    function_entry_state: Option<&'a CState>,
    /// Lexical names available where this certificate is emitted. They are
    /// presentation hints, never proof authority.
    pub(super) proof_bindings: Option<&'a PersistentMap<String, ContractExpression>>,
}

impl<'a> ExecutionView<'a> {
    /// The state the current region started from, or the current state
    /// when no region is open.
    pub(super) fn execution_start_state<'s>(&self, current_state: &'s CState) -> &'s CState
    where
        'a: 's,
    {
        self.frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(current_state)
    }

    /// The state that `old(...)` and `at(function.entry, ...)` resolve to when
    /// a contract clause is lowered here.
    pub(super) fn old_reference_state<'s>(&self, current_state: &'s CState) -> &'s CState
    where
        'a: 's,
    {
        match self.function_entry_state {
            Some(entry_state) => entry_state,
            None => self.execution_start_state(current_state),
        }
    }
}

impl<'a> ExecutionView<'a> {
    pub(super) fn new(
        frontier: &'a ExecutionFrontier,
        effect_facts: &'a ExecutionFacts,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        function_entry_state: Option<&'a CState>,
    ) -> Self {
        ExecutionView {
            frontier,
            recorded_snapshots,
            surface_propositions,
            effect_facts,
            function_entry_state,
            proof_bindings: None,
        }
    }
}

/// Route all return closers in one traversal of the retained certificate.
/// Looking up each loop by rescanning the whole proof would be quadratic in
/// a function with many independent returning loops.
pub(super) fn append_loop_return_closers(
    steps: &mut [ProofStep],
    returns: &[LoopReturnClosure],
    claim_index: Option<usize>,
) -> Result<(), ClickError> {
    fn arm<'a>(
        steps: &'a mut Vec<ProofStep>,
        choices: &[ProofCaseChoice],
    ) -> Result<&'a mut Vec<ProofStep>, ClickError> {
        let Some((choice, rest)) = choices.split_first() else {
            return Ok(steps);
        };
        let position = steps
            .iter()
            .position(|step| match step {
                ProofStep::If { condition, .. } => {
                    choice.match_arm.is_none() && *condition == choice.condition
                }
                ProofStep::Match { .. } => choice.match_arm.is_some(),
                _ => false,
            })
            .ok_or_else(|| ClickError::new("loop return lost its preservation arm"))?;
        match &mut steps[position] {
            ProofStep::If {
                then_proof,
                else_proof,
                ..
            } => arm(
                if choice.value {
                    then_proof.steps_mut()
                } else {
                    else_proof.steps_mut()
                },
                rest,
            ),
            ProofStep::Match { arms, .. } => arm(
                arms.get_mut(choice.match_arm.as_ref().unwrap().arm)
                    .ok_or_else(|| ClickError::new("loop return lost its match arm"))?
                    .proof
                    .steps_mut(),
                rest,
            ),
            _ => unreachable!(),
        }
    }
    let mut by_loop = BTreeMap::<usize, Vec<(&LoopReturnProof, Vec<ProofTactic>)>>::new();
    for (returned, post, grouped, per_claim) in returns {
        let closer = claim_index.map_or(grouped, |index| &per_claim[index]);
        by_loop
            .entry(returned.loop_index)
            .or_default()
            .push((returned, post.iter().chain(closer).cloned().collect()));
    }
    fn visit(
        steps: &mut [ProofStep],
        by_loop: &mut BTreeMap<usize, Vec<(&LoopReturnProof, Vec<ProofTactic>)>>,
    ) -> Result<(), ClickError> {
        for step in steps {
            crate::instrumentation::record_deterministic_work(1);
            match step {
                ProofStep::Loop(clause) => {
                    if let Some(preserve) = clause.preserve_proof.as_mut() {
                        if let CodeRegion::Loop(index) = clause.region
                            && let Some(returns) = by_loop.remove(&index)
                        {
                            for (returned, suffix) in returns {
                                let target = arm(preserve.steps_mut(), &returned.case_path)?;
                                let certificate = ProofCertificate::from_proof_tactics(&suffix)
                                    .map_err(|error| {
                                        ClickError::new(format!(
                                            "loop return closer is not simple: {error:?}"
                                        ))
                                    })?;
                                target.extend(certificate.into_steps());
                            }
                        }
                        visit(preserve.steps_mut(), by_loop)?;
                    }
                }
                ProofStep::If {
                    then_proof,
                    else_proof,
                    ..
                } => {
                    visit(then_proof.steps_mut(), by_loop)?;
                    visit(else_proof.steps_mut(), by_loop)?;
                }
                ProofStep::Match { arms, .. } => {
                    for arm in arms {
                        visit(arm.proof.steps_mut(), by_loop)?;
                    }
                }
                ProofStep::CallOutcomes {
                    returned_proof,
                    threw_proof,
                } => {
                    visit(returned_proof.steps_mut(), by_loop)?;
                    visit(threw_proof.steps_mut(), by_loop)?;
                }
                _ => {}
            }
        }
        Ok(())
    }
    if by_loop.is_empty() {
        return Ok(());
    }
    visit(steps, &mut by_loop)?;
    if !by_loop.is_empty() {
        return Err(ClickError::new(
            "loop return lost its enclosing loop certificate",
        ));
    }
    Ok(())
}

type LoopReturnClosure = (
    Arc<LoopReturnProof>,
    Vec<ProofTactic>,
    Vec<ProofTactic>,
    Vec<Vec<ProofTactic>>,
);

/// The loop's provisional expansion was recorded during execution, before
/// its returned outcomes were checked. Complete that same capture now.
pub(super) fn complete_loop_return_expansion(
    capture: Option<&mut ExpansionCapture>,
    steps: &[ProofStep],
    returns: &[LoopReturnClosure],
) -> Result<(), ClickError> {
    let Some(capture) = capture else {
        return Ok(());
    };
    let Some(loop_index) = returns.iter().find_map(|(p, _, _, _)| {
        p.owners
            .iter()
            .find(|(_, source)| Some(*source) == capture.source_index)
            .map(|(index, _)| *index)
    }) else {
        return Ok(());
    };
    fn find(steps: &[ProofStep], index: usize) -> Option<&ProofStep> {
        for step in steps {
            match step {
                ProofStep::Loop(clause) if clause.region == CodeRegion::Loop(index) => {
                    return Some(step);
                }
                ProofStep::Loop(clause) => {
                    if let Some(found) = clause
                        .preserve_proof
                        .as_ref()
                        .and_then(|proof| find(proof.steps(), index))
                    {
                        return Some(found);
                    }
                }
                ProofStep::Match { arms, .. } => {
                    for arm in arms {
                        if let Some(found) = find(arm.proof.steps(), index) {
                            return Some(found);
                        }
                    }
                }
                ProofStep::CallOutcomes {
                    returned_proof,
                    threw_proof,
                } => {
                    if let Some(found) = find(returned_proof.steps(), index)
                        .or_else(|| find(threw_proof.steps(), index))
                    {
                        return Some(found);
                    }
                }
                ProofStep::If {
                    then_proof,
                    else_proof,
                    ..
                } => {
                    if let Some(found) =
                        find(then_proof.steps(), index).or_else(|| find(else_proof.steps(), index))
                    {
                        return Some(found);
                    }
                }
                _ => {}
            }
        }
        None
    }
    let step = find(steps, loop_index)
        .ok_or_else(|| ClickError::new("selected loop return expansion lost its loop"))?;
    capture.result = Some(Ok(
        ProofCertificate::from_steps(vec![step.clone()])?.to_proof_tactics()
    ));
    Ok(())
}

#[cfg(test)]
mod loop_return_routing_tests {
    use super::*;

    #[test]
    fn loop_return_closer_routing_scales_with_certificate_size() {
        for size in [16, 64, 256] {
            let mut steps = Vec::new();
            let mut returns = Vec::new();
            for index in 0..size {
                steps.push(ProofStep::Loop(CertificateStructuralClause {
                    region: CodeRegion::Loop(index),
                    label: None,
                    decreases: None,
                    diverges: false,
                    items: Vec::new(),
                    resources: Vec::new(),
                    initialize_proof: None,
                    preserve_proof: Some(Box::new(
                        ProofCertificate::from_steps(vec![ProofStep::Step]).unwrap(),
                    )),
                }));
                returns.push((
                    Arc::new(LoopReturnProof {
                        loop_index: index,
                        owners: PersistentSequence::default(),
                        case_path: Vec::new(),
                        tactics: PersistentSequence::default(),
                        capture: None,
                        batch_captures: imbl::OrdMap::new(),
                    }),
                    Vec::new(),
                    vec![ProofTactic::Assumption],
                    Vec::new(),
                ));
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                append_loop_return_closers(&mut steps, &returns, None)
            });
            result.unwrap();
            assert!(work <= 8 * size, "{size} loops required {work} work units");
            for step in steps {
                let ProofStep::Loop(clause) = step else {
                    unreachable!()
                };
                assert!(matches!(
                    clause.preserve_proof.unwrap().steps(),
                    [ProofStep::Step, ProofStep::Assumption]
                ));
            }
        }
    }
}
