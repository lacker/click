use super::*;
#[cfg(test)]
use crate::persistent::persistent_node_allocations;
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
    pub(super) deferred_expansion_path_choices: PersistentSequence<SurfacePathChoice>,
}

#[derive(Clone)]
pub(super) struct CaseAssumption {
    pub(super) tactic_index: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) fact: Option<Proposition>,
    pub(super) at_function_entry: bool,
}

#[derive(Clone, Default)]
pub(super) struct ProofCertificateBuilder {
    pub(super) steps: Vec<ProofStep>,
    pub(super) blocker: Option<String>,
    pub(super) last_step_entry: Option<ProgramPointRef>,
    pub(super) path_choices: Vec<SurfacePathChoice>,
    /// Prevents the planner-metadata wrapper for a statement transition from
    /// re-entering itself while it emits the ordinary surface step.
    pub(super) lowering_planned_transition: bool,
}

/// Deterministically ordered proof facts with an exact-membership index.
///
/// Certificate emission and diagnostics retain insertion order, while a
/// named premise never scans unrelated earlier facts. All mutation stays
/// behind this type so the two views cannot diverge.
#[derive(Clone, Default)]
pub(super) struct ProofFactStore {
    ordered: PersistentSequence<Proposition>,
    exact: PersistentSet<Proposition>,
}

impl ProofFactStore {
    pub(super) fn from_ordered(facts: Vec<Proposition>) -> Self {
        let mut store = Self::default();
        for fact in facts {
            store.insert(fact);
        }
        store
    }

    pub(super) fn insert(&mut self, fact: Proposition) -> bool {
        if self.exact.contains(&fact) {
            return false;
        }
        self.exact = self.exact.with_value(fact.clone());
        self.ordered.push(fact);
        true
    }

    pub(super) fn retain(&mut self, mut keep: impl FnMut(&Proposition) -> bool) {
        let mut retained = Self::default();
        for fact in self.ordered.iter() {
            if keep(fact) {
                retained.insert(fact.clone());
            }
        }
        *self = retained;
    }

    pub(super) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
    }

    pub(super) fn iter(&self) -> PersistentSequenceIter<'_, Proposition> {
        self.ordered.iter()
    }

    pub(super) fn to_vec(&self) -> Vec<Proposition> {
        self.iter().cloned().collect()
    }

    #[cfg(test)]
    fn shares_persistent_storage_with(&self, other: &Self) -> bool {
        self.ordered.shares_tail_with(&other.ordered) && self.exact.shares_root_with(&other.exact)
    }
}

/// Environments a planning executor needs to construct the [`ProofStep`]
/// for each committed search move at the moment the move is made. Passing
/// `None` runs the executor without surface-certificate construction.
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
    /// The facts the constructed certificate's own check will have at the
    /// current state. Planning executes with automatically transported facts,
    /// but certificate validation carries only path facts, statement-local
    /// rewrites, and explicit surface transports across each step. Generated
    /// evidence is written against this certificate-visible set.
    pub(super) certificate_facts: ProofFactStore,
}

/// One planning call's construction gate: the environments the constructed
/// steps lower against and the sink they are recorded into.
pub(super) struct Construction<'a> {
    pub(super) environments: ConstructionEnvironments<'a>,
    pub(super) sink: &'a mut ProofCertificateBuilder,
}

impl Construction<'_> {
    pub(super) fn reborrow(&mut self) -> Construction<'_> {
        Construction {
            environments: self.environments,
            sink: self.sink,
        }
    }
}

#[derive(Clone, Copy)]
pub(super) struct ConstructionEnvironments<'a> {
    pub(super) predicate_environment: &'a PredicateEnvironment,
    pub(super) click_function_environment: &'a ClickFunctionEnvironment,
}

#[derive(Clone, PartialEq, Eq)]
pub(super) struct DeferredTacticCapture {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) post_execution_index: usize,
    pub(super) branch_skeleton: Vec<ProofTactic>,
}

impl DeferredTacticCapture {
    /// `post_execution_index` of a capture for a tactic nested in a deferred
    /// `if` arm: it matches by tactic index at whatever drained position.
    pub(super) const NESTED: usize = usize::MAX;
}

pub(in crate::surface) fn capture_c0_tactic_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
    source_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_tactic(site.clone(), source_index);
    let verification =
        verify_c0_sources_with_expansion_capture(click_source, c_sources, &mut capture);
    if let Some(result) = capture.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) => {
            match super::tactic_expansion_dependency_context(
                click_source,
                c_sources,
                &site,
                source_index,
            )? {
                Some(context) => Err(ClickError::new(format!(
                    "selected tactic expansion failed while checking {context}: {}",
                    error.message()
                ))),
                None => Err(error),
            }
        }
        Ok(_) => Err(ClickError::new(format!(
            "selected {} proof has no source tactic {source_index}",
            site.description()
        ))),
    }
}

pub(in crate::surface) fn capture_c0_proof_site_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut capture = ExpansionCapture::for_site(site.clone());
    let verification =
        verify_c0_sources_with_expansion_capture(click_source, c_sources, &mut capture);
    if let Some(result) = capture.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) => Err(error),
        Ok(_) if matches!(site, ProofSite::LoopPhase { .. }) => {
            // A loop phase nested under an unreachable C path can have no
            // initialization/preservation obligations at all. There is no
            // path certificate to retain, and a synthesized stand-in proof
            // would present itself as verified evidence; report the empty
            // obligation set instead of inventing one.
            Err(ClickError::new(format!(
                "verification retained no certificate for {}: the phase produced no proof obligations (its loop may sit under an unreachable path), so there is no proof to expand",
                site.description()
            )))
        }
        Ok(_) => Err(ClickError::new(format!(
            "verification did not retain a certificate for {}",
            site.description()
        ))),
    }
}

pub(super) fn finish_proof_site_expansion_capture(
    capture: Option<&mut ExpansionCapture>,
    site: &ProofSite,
    certificate: &ProofCertificate,
) {
    let Some(capture) = capture else {
        return;
    };
    if capture.site != *site || capture.source_index.is_some() || capture.result.is_some() {
        return;
    }
    capture.active = true;
    capture.result = Some(Ok(certificate.to_proof_tactics().to_vec()));
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
    if capture.site != *site || capture.source_index != Some(source_index) {
        return;
    }
    capture.active = true;
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
            [FunctionClaimRef::Effect(index, _)] => CProofClaim::Effect(*index),
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
    if capture.result.is_some() {
        return;
    }
    capture.result = Some(match &proof_certificate_builder.blocker {
        Some(blocker) => Err(format!("could not expand selected tactic: {blocker}")),
        None if proof_certificate_builder.steps.is_empty() && !allow_empty => {
            Err("selected tactic produced no standalone surface expansion".to_string())
        }
        None => Ok(
            ProofCertificate::from_steps(proof_certificate_builder.steps.clone())
                .to_proof_tactics(),
        ),
    });
}

pub(super) fn tactic_expansion_capture_is_active(capture: Option<&ExpansionCapture>) -> bool {
    capture.is_some_and(|capture| capture.active)
}

pub(super) fn tactic_expansion_capture_matches(
    capture: Option<&ExpansionCapture>,
    site: Option<&ProofSite>,
    source_index: usize,
) -> bool {
    capture.is_some_and(|capture| {
        capture.active && site == Some(&capture.site) && capture.source_index == Some(source_index)
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
    if proof_site != Some(&capture.site) || capture.source_index != Some(deferred.source_index) {
        return Err(ClickError::new(
            "deferred tactic capture no longer matches the selected proof occurrence",
        ));
    }
    capture.active = true;
    Ok(())
}

#[derive(Clone)]
pub(super) struct SurfacePathChoice {
    pub(super) occurrence: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) tactic_offset: usize,
}

impl ProofCertificateBuilder {
    pub(super) fn push_step(&mut self, step: ProofStep) {
        if self.blocker.is_none() {
            append_surface_step_to_leaves(&mut self.steps, step);
        }
    }

    pub(super) fn push_source_tactic(&mut self, tactic: ProofTactic) {
        if self.blocker.is_some() {
            return;
        }
        match ProofCertificate::from_proof_tactics(std::slice::from_ref(&tactic)) {
            Ok(proof) => {
                let [step] = proof.steps.as_slice() else {
                    unreachable!("one surface tactic must produce one proof step")
                };
                self.push_step(step.clone());
            }
            Err(error) => self.block(format!(
                "attempted to record a non-simple surface proof step at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            )),
        }
    }

    pub(super) fn push_have(&mut self, proposition: ClickProposition, proof: SourceProof) {
        let SourceProof::Script(tactics) = proof else {
            self.block("generated `have` proof was not an explicit simple script");
            return;
        };
        match ProofCertificate::from_proof_tactics(&tactics) {
            Ok(proof) => self.push_step(ProofStep::Have {
                proposition,
                proof: Box::new(proof),
            }),
            Err(error) => self.block(format!(
                "generated `have` body was not a simple proof at {:?}: {:?}",
                error.path(),
                error.tactic_class()
            )),
        }
    }

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

pub(super) fn append_surface_step_to_leaves(steps: &mut Vec<ProofStep>, step: ProofStep) {
    if let Some(ProofStep::If {
        then_proof,
        else_proof,
        ..
    }) = steps.last_mut()
    {
        append_surface_step_to_leaves(&mut then_proof.steps, step.clone());
        append_surface_step_to_leaves(&mut else_proof.steps, step);
    } else {
        steps.push(step);
    }
}

pub(super) fn append_surface_tactics_by_leaf(
    steps: &mut Vec<ProofStep>,
    path_tactics: &[Vec<ProofTactic>],
) -> Result<(), String> {
    let path_steps = path_tactics
        .iter()
        .map(|tactics| {
            ProofCertificate::from_proof_tactics(tactics)
                .map(|proof| proof.steps)
                .map_err(|error| format!("path contained a non-simple tactic: {error:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    // Distinct C execution paths do not necessarily correspond to distinct
    // surface proof branches.  When every path produced the same certificate,
    // it is path-independent and belongs on every existing surface leaf.
    if let Some(common) = path_steps.first()
        && path_steps.iter().all(|path| path == common)
    {
        for step in common {
            append_surface_step_to_leaves(steps, step.clone());
        }
        return Ok(());
    }

    pub(super) fn append(
        steps: &mut Vec<ProofStep>,
        path_steps: &[Vec<ProofStep>],
        next_path: &mut usize,
    ) {
        if let Some(ProofStep::If {
            then_proof,
            else_proof,
            ..
        }) = steps.last_mut()
        {
            append(&mut then_proof.steps, path_steps, next_path);
            append(&mut else_proof.steps, path_steps, next_path);
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
    steps.extend(proof.steps);
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
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
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
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            available,
            &proof_if.condition,
            predicate_environment,
            click_function_environment,
            recorded_snapshots,
        )?;
        let assumptions = assumptions_from_propositions(available);
        let is_true = exact_fact_is_available(&lowered, available) || assumptions.proves(&lowered);
        let is_false = available
            .iter()
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

pub(super) fn surface_branch_skeleton(steps: &[ProofStep]) -> Vec<ProofStep> {
    let Some((condition, then_proof, else_proof)) =
        steps.iter().rev().find_map(|step| match step {
            ProofStep::If {
                condition,
                then_proof,
                else_proof,
            } => Some((condition, then_proof, else_proof)),
            _ => None,
        })
    else {
        return Vec::new();
    };
    vec![ProofStep::If {
        condition: condition.clone(),
        then_proof: Box::new(ProofCertificate::from_steps(surface_branch_skeleton(
            then_proof.steps(),
        ))),
        else_proof: Box::new(ProofCertificate::from_steps(surface_branch_skeleton(
            else_proof.steps(),
        ))),
    }]
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
            || choice.condition != first_choice.condition
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
    steps.push(ProofStep::If {
        condition: first_choice.condition,
        then_proof: Box::new(ProofCertificate::from_steps(synthesize_surface_paths(
            then_paths,
        )?)),
        else_proof: Box::new(ProofCertificate::from_steps(synthesize_surface_paths(
            else_paths,
        )?)),
    });
    Ok(steps)
}

#[derive(Clone)]
pub(super) enum PostExecutionTactic {
    Fold(ResourceClause),
    CloseOpen {
        resource: ResourceClause,
        preserve_exposed_body: bool,
    },
    UnfoldPredicate(String),
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
    Witness(ProofWitness),
    Assumption,
    Normalize,
    Rewrite(ClickProposition),
    FrameRegion(CodeRegionRef),
    Frame,
    FrameUsing {
        region: Option<CodeRegionRef>,
        premises: Vec<ClickProposition>,
    },
    CheckedFrameUsing {
        authority: CheckedFrameAuthority,
        region: Option<CodeRegionRef>,
        premises: Vec<ClickProposition>,
        /// Exact checked Surface contribution retained until ordered
        /// finalization reaches this source operation. This is expansion
        /// provenance only; the other fields are the complete semantic input.
        surface_tactics: Option<Vec<ProofTactic>>,
    },
    /// Surface-only control structure scheduled after terminal execution.
    /// The arms contain no semantic state: ordered finalization asks the
    /// focused outcome `Proof` to decide the condition, then applies only the
    /// selected arm's checked operations to that same descendant.
    If {
        condition: ClickProposition,
        then_tactics: Vec<DeferredPostExecutionTactic>,
        else_tactics: Vec<DeferredPostExecutionTactic>,
    },
    Simp,
}

#[derive(Clone)]
pub(super) struct DeferredPostExecutionTactic {
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

    fn fact(value: bool) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::Constant(value), true)
    }

    #[test]
    fn proof_fact_store_preserves_order_and_indexes_exact_membership() {
        let first = fact(true);
        let second = fact(false);
        let mut facts = ProofFactStore::default();

        assert!(facts.insert(first.clone()));
        assert!(facts.insert(second.clone()));
        assert!(!facts.insert(first.clone()));
        assert_eq!(facts.to_vec(), &[first.clone(), second.clone()]);
        assert!(facts.exact.contains(&first));

        facts.retain(|candidate| candidate != &first);
        assert_eq!(facts.to_vec(), std::slice::from_ref(&second));
        assert!(!facts.exact.contains(&first));
        assert!(facts.exact.contains(&second));
    }

    #[test]
    fn proof_fact_store_forks_share_certificate_history() {
        let mut facts = ProofFactStore::default();
        for index in 0..4096 {
            facts.insert(Proposition::ConditionIs(
                ConditionTerm::Variable(Variable(index)),
                true,
            ));
        }
        let ancestor = facts.clone();
        assert!(facts.shares_persistent_storage_with(&ancestor));

        let added = Proposition::ConditionIs(ConditionTerm::Variable(Variable(4096)), true);
        facts.insert(added.clone());

        assert!(!ancestor.contains(&added));
        assert!(facts.contains(&added));
        assert_eq!(ancestor.iter().count(), 4096);
        assert_eq!(facts.iter().count(), 4097);
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
        PostExecutionTactic::Simp => ("simp", "smart"),
        PostExecutionTactic::Fold(_) => ("fold", "simple"),
        PostExecutionTactic::CloseOpen { .. } => ("open", "control"),
        PostExecutionTactic::UnfoldPredicate(_) => ("unfold", "simple"),
        PostExecutionTactic::ApplyUsing { .. } => ("apply", "simple"),
        PostExecutionTactic::Choose(_) => ("choose", "simple"),
        PostExecutionTactic::Witness(_) => ("witness", "simple"),
        PostExecutionTactic::Assumption => ("assumption", "simple"),
        PostExecutionTactic::Normalize => ("normalize", "simple"),
        PostExecutionTactic::Rewrite(_) => ("rewrite", "simple"),
        PostExecutionTactic::FrameRegion(_) => ("frame", "simple"),
        PostExecutionTactic::Frame => ("frame", "simple"),
        PostExecutionTactic::FrameUsing { .. } | PostExecutionTactic::CheckedFrameUsing { .. } => {
            ("frame", "simple")
        }
        PostExecutionTactic::If { .. } => ("if", "control"),
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
    pub(super) effect_facts: &'a [ExecutionPureFact],
    function_entry_state: Option<&'a CState>,
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
        effect_facts: &'a [ExecutionPureFact],
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
        }
    }
}
