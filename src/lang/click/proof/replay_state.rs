use super::*;

/// Identifies the `close_invariants` step of a replayed certificate well
/// enough to emit a `click timing:` line for the work its caller does on its
/// behalf: the same claim-relative indices `replay_linear_tactics` would use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct InvariantCloserStep {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) statement_index: usize,
}

#[derive(Clone, Default)]
pub(super) struct TacticReplayState {
    pub(super) proof_site: Option<ProofSite>,
    pub(super) loop_effect_goal: Option<LoopEffectReplayGoal>,
    pub(super) frontier: ExecutionFrontier,
    pub(super) source_layout: SourceExecutionLayout,
    pub(super) program_point_states: ProgramPointStates,
    /// C `if` regions completed by the most recent execution transition.
    /// A frontier-local `branch` uses this edge-local record to distinguish
    /// reaching its join from executing past it in a later tactic.
    pub(super) completed_branch_regions: Vec<usize>,
    /// This proof path has passed through a frontier-local `branch`. Unlike
    /// `branch_path`, this excludes pure proof-level `if` diagnostics and can
    /// therefore distinguish an already selected C path at function exit.
    pub(super) has_structured_branch_history: bool,
    pub(super) frames: BTreeSet<Option<CodeRegionRef>>,
    pub(super) unfolded_predicates: Vec<String>,
    pub(super) post_execution_tactics: Vec<DeferredPostExecutionTactic>,
    pub(super) region_simp: Option<(usize, usize)>,
    pub(super) region_invariants_closed: bool,
    /// Where the replayed `close_invariants` tactic sat, so the invariant
    /// bundle check its caller performs after the replay finishes can be
    /// timed against that tactic's own identity instead of going unattributed.
    ///
    /// `close_invariants` only records the intent during replay; the kernel
    /// re-derivation that gives it meaning runs in
    /// `verify_one_loop_preservation_proof` once the whole certificate has
    /// replayed. Without this the dominant cost of the loop-invariant bundle
    /// carries no class tag at all (`git history (profiler coverage, 2026-07-31)`).
    pub(super) invariant_closer_step: Option<InvariantCloserStep>,
    pub(super) case_assumptions: Vec<ReplayCaseAssumption>,
    pub(super) effect_facts: Vec<ExecutionPureFact>,
    pub(super) region_proof: bool,
    pub(super) loop_invariant_region: bool,
    pub(super) ordered_finalization: bool,
    pub(super) grouped_contract: bool,
    pub(super) next_opaque_call: u64,
    pub(super) next_verification_variable: u64,
    pub(super) next_path_choice: usize,
    pub(super) execution_start_facts: Vec<Proposition>,
    /// Frontier-local loop proofs become part of the checked function proof,
    /// not temporary tactic state.  Final kernel certification rebuilds the
    /// annotated function from these bound clauses and reuses these rules.
    pub(super) frontier_loop_clauses: Vec<StructuralClause>,
    pub(super) frontier_loop_rules: Vec<CVerifiedLoopRule>,
    /// The snapshot that `old(...)` — and `at(function.entry, ...)`, which is
    /// the same reference under another spelling — names in this region.
    ///
    /// `old` denotes function entry, but certificate replay used to resolve it
    /// *positionally*, to whichever state the enclosing proof region started
    /// from. Inside a function-body proof those coincide; inside a
    /// loop-preservation region they do not, so the same surface text meant
    /// loop-entry memory here and function-entry memory in the Click -> Spec
    /// lowering the kernel certified against. Naming the state explicitly is
    /// what makes the two agree; see
    /// `docs/advanced/memory-dag.md` (stage 2a).
    ///
    /// `None` keeps the previous positional resolution, so every region that
    /// does not record a function-entry snapshot behaves exactly as before.
    pub(super) function_entry_state: Option<CState>,
    pub(super) concrete_loop_execution: bool,
    /// The execution frontier was intentionally replaced by a branch
    /// interface. Its state is a specification abstraction, not an exact
    /// symbolic body outcome; whole-function kernel certification checks every
    /// concrete path before any contract claim is exported.
    pub(super) execution_abstraction: bool,
    pub(super) planned_tactics: Vec<ProofTactic>,
    pub(super) surface_propositions: SurfacePropositionMap,
    pub(super) surface_replay: SurfaceReplay,
    pub(super) deferred_tactic_capture: Option<DeferredTacticCapture>,
    /// C branch choices enclosing a selected tactic in their common
    /// continuation. Deferred post-execution expansion is finalized after
    /// `execute_internal_proof` has returned one context per path, so it must
    /// retain this typed path rather than reconstructing it from diagnostics.
    pub(super) deferred_expansion_path_choices: Vec<SurfacePathChoice>,
}

#[derive(Clone)]
pub(super) struct LoopEffectReplayGoal {
    pub(super) before_state: CState,
    pub(super) check: CLoopEffectCheck,
    pub(super) closed: bool,
}

#[derive(Clone)]
pub(super) struct ReplayCaseAssumption {
    pub(super) tactic_index: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) fact: Option<Proposition>,
    pub(super) at_function_entry: bool,
}

#[derive(Clone, Default)]
pub(super) struct SurfaceReplay {
    pub(super) tactics: Vec<ProofTactic>,
    pub(super) blocker: Option<String>,
    pub(super) last_step_entry: Option<ProgramPointRef>,
    pub(super) path_choices: Vec<SurfacePathChoice>,
}

#[derive(Clone)]
pub(super) struct DeferredTacticCapture {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) post_execution_index: usize,
    pub(super) branch_skeleton: Vec<ProofTactic>,
}

pub(super) struct TacticExpansionProbe {
    pub(super) site: ProofSite,
    pub(super) source_index: Option<usize>,
    pub(super) active: bool,
    pub(super) result: Option<Result<Vec<ProofTactic>, String>>,
}

thread_local! {
    pub(super) static TACTIC_EXPANSION_PROBE: std::cell::RefCell<Option<TacticExpansionProbe>> =
        const { std::cell::RefCell::new(None) };
    pub(super) static SUPPRESS_TACTIC_EXPANSION_CAPTURE: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

pub(in crate::lang::click) fn capture_c0_tactic_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
    source_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        if probe.is_some() {
            return Err(ClickError::new(
                "cannot nest selected-tactic expansion requests",
            ));
        }
        *probe = Some(TacticExpansionProbe {
            site: site.clone(),
            source_index: Some(source_index),
            active: false,
            result: None,
        });
        Ok(())
    })?;

    let verification = verify_c0_sources(click_source, c_sources);
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow_mut().take());
    let Some(captured) = captured else {
        return Err(ClickError::new("selected-tactic expansion probe was lost"));
    };
    if let Some(result) = captured.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) if !error.is_expansion_complete() => {
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
        Err(_) => Err(ClickError::new(
            "selected tactic completed without recording an expansion",
        )),
        Ok(_) => Err(ClickError::new(format!(
            "selected {} proof has no source tactic {source_index}",
            site.description()
        ))),
    }
}

pub(in crate::lang::click) fn active_c0_tactic_expansion_request()
-> Option<(ProofSite, Option<usize>)> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .map(|probe| (probe.site.clone(), probe.source_index))
    })
}

pub(in crate::lang::click) fn capture_c0_proof_site_expansion(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: ProofSite,
) -> Result<Vec<ProofTactic>, ClickError> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut probe = probe.borrow_mut();
        if probe.is_some() {
            return Err(ClickError::new(
                "cannot nest selected-proof expansion requests",
            ));
        }
        *probe = Some(TacticExpansionProbe {
            site: site.clone(),
            source_index: None,
            active: false,
            result: None,
        });
        Ok(())
    })?;

    let verification = verify_c0_sources(click_source, c_sources);
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow_mut().take());
    let Some(captured) = captured else {
        return Err(ClickError::new("selected-proof expansion probe was lost"));
    };
    if let Some(result) = captured.result {
        return result.map_err(ClickError::new);
    }
    match verification {
        Err(error) if !error.is_expansion_complete() => Err(error),
        Err(_) => Err(ClickError::new(
            "selected proof completed without recording an expansion",
        )),
        Ok(_) if matches!(site, ProofSite::LoopPhase { .. }) => {
            // A loop phase nested under an unreachable C path can have no
            // initialization/preservation obligations at all.  There is no
            // path certificate to retain in that case; emit a canonical
            // simple proof.  Reverification remains the authority and will
            // reject `assumption` if the phase was actually reachable.
            Ok(vec![ProofTactic::Assumption])
        }
        Ok(_) => Err(ClickError::new(format!(
            "verification did not retain a certificate for {}",
            site.description()
        ))),
    }
}

pub(super) fn finish_proof_site_expansion_capture(
    site: &ProofSite,
    certificate: &TacticCertificate,
) -> Result<(), ClickError> {
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return false;
        };
        if probe.site != *site || probe.source_index.is_some() {
            return false;
        }
        probe.active = true;
        probe.result = Some(Ok(certificate.tactics().to_vec()));
        true
    });
    if captured {
        Err(ClickError::expansion_complete())
    } else {
        Ok(())
    }
}

pub(super) fn record_proof_site_tactic_expansion(
    site: &ProofSite,
    source_index: usize,
    tactics: &[ProofTactic],
) {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return;
        };
        if probe.site != *site || probe.source_index != Some(source_index) {
            return;
        }
        probe.active = true;
        match &mut probe.result {
            None => probe.result = Some(Ok(tactics.to_vec())),
            Some(Ok(existing)) if existing == tactics => {}
            Some(Ok(_)) => {
                probe.result = Some(Err(
                    "selected tactic expands differently across proof obligations".to_string(),
                ));
            }
            Some(Err(_)) => {}
        }
    });
}

pub(super) fn selected_tactic_index_for_site(site: &ProofSite) -> Option<usize> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe
            .borrow()
            .as_ref()
            .filter(|probe| probe.site == *site)
            .and_then(|probe| probe.source_index)
    })
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

/// Begins a selected-tactic capture when the probe matches this tactic.
/// Returns the branch skeleton of the surface tactics recorded so far
/// (computed before the surface replay is reset), or `None` when no capture
/// begins. The skeleton is only materialized on the single capturing
/// iteration, keeping ordinary verification free of that per-tactic cost.
pub(super) fn begin_tactic_expansion_capture(
    source_index: usize,
    _tactic: &ProofTactic,
    replay: &mut TacticReplayState,
) -> Option<Vec<ProofTactic>> {
    if SUPPRESS_TACTIC_EXPANSION_CAPTURE.with(std::cell::Cell::get) {
        return None;
    }
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let probe = slot.as_mut()?;
        let sibling_branch_capture = probe.active
            && !replay.deferred_expansion_path_choices.is_empty()
            && probe.source_index == Some(source_index)
            && replay.proof_site.as_ref() == Some(&probe.site);
        if probe.active && !sibling_branch_capture
            || probe.source_index != Some(source_index)
            || replay.proof_site.as_ref() != Some(&probe.site)
        {
            return None;
        }
        probe.active = true;
        let branch_skeleton = surface_branch_skeleton(&replay.surface_replay.tactics);
        let last_step_entry = replay.surface_replay.last_step_entry.clone();
        replay.surface_replay = SurfaceReplay {
            last_step_entry,
            ..SurfaceReplay::default()
        };
        Some(branch_skeleton)
    })
}

/// `allow_empty` accepts an empty expansion as the exact answer: the selected
/// tactic contributed no surface tactics to the accepted certificate, so the
/// rewrite removes it. Every other caller keeps the empty guard — for them an
/// empty capture means the lowering lost the tactics, not that none exist.
pub(super) fn finish_tactic_expansion_capture(
    surface_replay: &SurfaceReplay,
    allow_empty: bool,
) -> ClickError {
    let captured = TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return false;
        };
        probe.result = Some(match &surface_replay.blocker {
            Some(blocker) => Err(format!("could not expand selected tactic: {blocker}")),
            None if surface_replay.tactics.is_empty() && !allow_empty => {
                Err("selected tactic produced no standalone surface expansion".to_string())
            }
            None => Ok(surface_replay.tactics.clone()),
        });
        true
    });
    if !captured {
        return ClickError::new(
            "could not expand the selected tactic: the expansion probe was no longer active",
        );
    }
    ClickError::expansion_complete()
}

pub(super) fn tactic_expansion_capture_is_active() -> bool {
    TACTIC_EXPANSION_PROBE.with(|probe| probe.borrow().as_ref().is_some_and(|probe| probe.active))
}

pub(super) fn tactic_expansion_capture_matches(
    site: Option<&ProofSite>,
    source_index: usize,
) -> bool {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        probe.borrow().as_ref().is_some_and(|probe| {
            probe.active && site == Some(&probe.site) && probe.source_index == Some(source_index)
        })
    })
}

/// Takes one path-local selected-tactic expansion while leaving the probe
/// installed for a sibling execution path. Frontier-local `branch` uses this
/// to collect the certificate produced at one shared source occurrence under
/// each C arm before it emits their logical case split.
pub(super) fn take_path_tactic_expansion_capture() -> Result<Vec<ProofTactic>, ClickError> {
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return Err(ClickError::new(
                "selected-tactic expansion probe was lost between branch paths",
            ));
        };
        let result = probe.result.take().ok_or_else(|| {
            ClickError::new("selected tactic completed without recording its branch expansion")
        })?;
        probe.active = false;
        result.map_err(ClickError::new)
    })
}

pub(super) fn resume_deferred_tactic_expansion_capture(
    replay: &TacticReplayState,
) -> Result<(), ClickError> {
    let Some(deferred) = &replay.deferred_tactic_capture else {
        return Ok(());
    };
    TACTIC_EXPANSION_PROBE.with(|probe| {
        let mut slot = probe.borrow_mut();
        let Some(probe) = slot.as_mut() else {
            return Err(ClickError::new(
                "selected-tactic expansion probe was lost before deferred finalization",
            ));
        };
        if replay.proof_site.as_ref() != Some(&probe.site)
            || probe.source_index != Some(deferred.source_index)
        {
            return Err(ClickError::new(
                "deferred tactic capture no longer matches the selected proof occurrence",
            ));
        }
        probe.active = true;
        Ok(())
    })
}

#[derive(Clone)]
pub(super) struct SurfacePathChoice {
    pub(super) occurrence: usize,
    pub(super) condition: ClickProposition,
    pub(super) value: bool,
    pub(super) tactic_offset: usize,
}

impl SurfaceReplay {
    pub(super) fn push(&mut self, tactic: ProofTactic) {
        if self.blocker.is_none() {
            append_surface_tactic_to_leaves(&mut self.tactics, tactic);
        }
    }

    pub(super) fn block(&mut self, message: impl Into<String>) {
        if self.blocker.is_none() {
            self.blocker = Some(message.into());
            self.tactics.clear();
            self.path_choices.clear();
        }
    }
}

pub(super) fn record_post_execution_surface_tactic(
    path_tactics: &mut Vec<ProofTactic>,
    capture_tactics: &mut Vec<ProofTactic>,
    deferred_capture: Option<&DeferredTacticCapture>,
    post_execution_index: usize,
    tactic_index: usize,
    tactic: ProofTactic,
) {
    if deferred_capture.is_some_and(|capture| {
        capture.tactic_index == tactic_index && capture.post_execution_index == post_execution_index
    }) {
        capture_tactics.push(tactic.clone());
    }
    path_tactics.push(tactic);
}

pub(super) fn append_surface_tactic_to_leaves(tactics: &mut Vec<ProofTactic>, tactic: ProofTactic) {
    if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
        append_surface_tactic_to_leaves(&mut proof_if.then_tactics, tactic.clone());
        append_surface_tactic_to_leaves(&mut proof_if.else_tactics, tactic);
    } else {
        tactics.push(tactic);
    }
}

pub(super) fn append_surface_tactics_by_leaf(
    tactics: &mut Vec<ProofTactic>,
    path_tactics: &[Vec<ProofTactic>],
) -> Result<(), String> {
    // Distinct C execution paths do not necessarily correspond to distinct
    // surface proof branches.  When every path produced the same certificate,
    // it is path-independent and belongs on every existing surface leaf.
    if let Some(common) = path_tactics.first()
        && path_tactics.iter().all(|path| path == common)
    {
        for tactic in common {
            append_surface_tactic_to_leaves(tactics, tactic.clone());
        }
        return Ok(());
    }

    pub(super) fn append(
        tactics: &mut Vec<ProofTactic>,
        path_tactics: &[Vec<ProofTactic>],
        next_path: &mut usize,
    ) {
        if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
            append(&mut proof_if.then_tactics, path_tactics, next_path);
            append(&mut proof_if.else_tactics, path_tactics, next_path);
        } else if let Some(suffix) = path_tactics.get(*next_path) {
            tactics.extend(suffix.iter().cloned());
            *next_path += 1;
        }
    }

    let mut next_path = 0;
    append(tactics, path_tactics, &mut next_path);
    if next_path == path_tactics.len() {
        Ok(())
    } else {
        Err(format!(
            "surface/certificate path coverage diverged at p{next_path}: surface has {next_path} paths but frame certificate has {}",
            path_tactics.len()
        ))
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
    program_point_states: &ProgramPointStates,
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
        let lowered = lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            available,
            &proof_if.condition,
            predicate_environment,
            click_function_environment,
            program_point_states,
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

pub(super) fn surface_branch_skeleton(tactics: &[ProofTactic]) -> Vec<ProofTactic> {
    let Some(proof_if) = tactics.iter().rev().find_map(|tactic| match tactic {
        ProofTactic::If(proof_if) => Some(proof_if),
        _ => None,
    }) else {
        return Vec::new();
    };
    vec![ProofTactic::If(ProofIf {
        condition: proof_if.condition.clone(),
        then_tactics: surface_branch_skeleton(&proof_if.then_tactics),
        else_tactics: surface_branch_skeleton(&proof_if.else_tactics),
    })]
}

pub(super) fn synthesize_surface_alternatives(
    paths: Vec<SurfaceReplay>,
) -> Result<Vec<ProofTactic>, String> {
    if paths.is_empty() {
        return Err("certified alternatives contained no paths".to_string());
    }
    if let Some(blocker) = paths.iter().find_map(|path| path.blocker.clone()) {
        return Err(blocker);
    }
    synthesize_surface_paths(paths)
}

pub(super) fn synthesize_surface_paths(
    paths: Vec<SurfaceReplay>,
) -> Result<Vec<ProofTactic>, String> {
    if paths.len() == 1 {
        return Ok(paths.into_iter().next().unwrap().tactics);
    }
    let first_choice = paths
        .first()
        .and_then(|path| path.path_choices.first())
        .ok_or_else(|| "distinct certified paths have no surface branch condition".to_string())?
        .clone();
    let prefix = paths[0]
        .tactics
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
            || path.tactics.get(..choice.tactic_offset) != Some(prefix.as_slice())
        {
            return Err("certified paths do not share one branch prefix".to_string());
        }
        path.tactics.drain(..choice.tactic_offset);
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

    let mut tactics = prefix;
    tactics.push(ProofTactic::If(ProofIf {
        condition: first_choice.condition,
        then_tactics: synthesize_surface_paths(then_paths)?,
        else_tactics: synthesize_surface_paths(else_paths)?,
    }));
    Ok(tactics)
}

#[derive(Clone)]
pub(super) enum PostExecutionTactic {
    Fold(ResourceClause),
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
        facts: Vec<Proposition>,
    },
    CertifiedFrame(Vec<Vec<PropositionDerivation>>),
    Simp,
}

#[derive(Clone)]
pub(super) struct DeferredPostExecutionTactic {
    pub(super) tactic_index: usize,
    pub(super) source_index: usize,
    pub(super) tactic: PostExecutionTactic,
}

impl TacticReplayState {
    pub(super) fn defer_post_execution(
        &mut self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
    ) {
        self.post_execution_tactics
            .push(DeferredPostExecutionTactic {
                tactic_index,
                source_index,
                tactic,
            });
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
        PostExecutionTactic::UnfoldPredicate(_) => ("unfold", "simple"),
        PostExecutionTactic::ApplyUsing { .. } => ("apply", "simple"),
        PostExecutionTactic::Choose(_) => ("choose", "simple"),
        PostExecutionTactic::Witness(_) => ("witness", "simple"),
        PostExecutionTactic::Assumption => ("assumption", "simple"),
        PostExecutionTactic::Normalize => ("normalize", "simple"),
        PostExecutionTactic::Rewrite(_) => ("rewrite", "simple"),
        PostExecutionTactic::FrameRegion(_) => ("frame", "simple"),
        PostExecutionTactic::Frame => ("frame", "simple"),
        PostExecutionTactic::FrameUsing { .. } => ("frame", "simple"),
        PostExecutionTactic::CertifiedFrame(_) => ("frame", "simple"),
    }
}

#[derive(Clone, Default)]
pub(super) struct ExecutionFrontier {
    pub(super) point: ProofExecutionPoint,
    pub(super) execution_start_state: Option<CState>,
    pub(super) next_statement_index: usize,
    pub(super) continuations: Vec<ProofExecutionContinuation>,
}

#[derive(Clone)]
pub(super) struct ProofExecutionContinuation {
    pub(super) remaining: Option<CStatement>,
    pub(super) next_statement_index: usize,
    pub(super) kind: ProofExecutionContinuationKind,
}

#[derive(Clone, Copy)]
pub(super) enum ProofExecutionContinuationKind {
    Branch { statement_index: usize },
    LoopIteration,
}

#[derive(Clone, Default)]
pub(super) enum ProofExecutionPoint {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: CStatement,
    },
    FunctionExit {
        execution: CFunctionExecutionCandidates,
    },
}

#[derive(Clone)]
pub(super) struct ProofReplayContext {
    pub(super) state: CState,
    pub(super) pure_facts: Vec<Proposition>,
    pub(super) replay: TacticReplayState,
    pub(super) branch_path: Vec<String>,
}

impl TacticReplayState {
    pub(super) fn is_at_function_exit(&self) -> bool {
        matches!(
            self.frontier.point,
            ProofExecutionPoint::FunctionExit { .. }
        )
    }

    pub(super) fn is_at_function_entry(&self) -> bool {
        matches!(self.frontier.point, ProofExecutionPoint::FunctionEntry)
    }

    pub(super) fn execution(&self) -> Option<&CFunctionExecutionCandidates> {
        match &self.frontier.point {
            ProofExecutionPoint::FunctionEntry | ProofExecutionPoint::StatementEntry { .. } => None,
            ProofExecutionPoint::FunctionExit { execution, .. } => Some(execution),
        }
    }

    pub(super) fn execution_start_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        self.frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(current_state)
    }

    /// The state that `old(...)` and `at(function.entry, ...)` resolve to when
    /// a contract clause is lowered here.
    ///
    /// This is the one place that answers "which memory does `old` mean", so
    /// the answer is a *named* snapshot rather than whichever state happens to
    /// sit at the enclosing frame's `pre_state` position. When the region
    /// recorded its function-entry snapshot, that snapshot is the answer —
    /// it is the same `CState` the Click -> Spec lowering used as
    /// `SpecMemory::Fixed(entry_memory)` for every `old` operand in this
    /// function's contracts, so both sides name the same interned node.
    ///
    /// Nothing here is trusted on the strength of the naming alone. A lowered
    /// candidate is accepted only by exact equality against the certified
    /// proposition, and a `MemoryLoad` carries its snapshot inside the term,
    /// so a candidate resolved to the wrong state cannot match: selecting the
    /// state by name adds a spelling to search, and the certificate check
    /// remains the thing that validates it.
    ///
    /// Falling back to [`Self::execution_start_state`] keeps every region that
    /// records no function-entry snapshot on its previous behaviour.
    pub(super) fn old_reference_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        match &self.function_entry_state {
            Some(entry_state) => entry_state,
            None => self.execution_start_state(current_state),
        }
    }
}
