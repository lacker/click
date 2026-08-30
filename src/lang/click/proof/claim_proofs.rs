use super::*;
use crate::kernel::apply_c_function_contract_resource_transition;
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static FLAT_PROOF_UNITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(in crate::lang::click) fn count_flat_proof_units<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = FLAT_PROOF_UNITS.with(std::cell::Cell::get);
    let result = operation();
    let after = FLAT_PROOF_UNITS.with(std::cell::Cell::get);
    (result, after - before)
}

pub(in crate::lang::click) struct ClaimProofResult {
    pub(in crate::lang::click) theorems: Vec<VerifiedCTheorem>,
}

fn select_checked_post_execution_tactics<'a>(
    proof: &Proof<'_>,
    tactics: impl IntoIterator<Item = &'a DeferredPostExecutionTactic>,
    selected: &mut Vec<&'a DeferredPostExecutionTactic>,
) -> Result<(), ClickError> {
    for deferred in tactics {
        match &deferred.tactic {
            PostExecutionTactic::If {
                condition,
                then_tactics,
                else_tactics,
            } => {
                let arm = if proof.checked_outcome_if_value(condition)? {
                    then_tactics
                } else {
                    else_tactics
                };
                select_checked_post_execution_tactics(proof, arm, selected)?;
            }
            _ => selected.push(deferred),
        }
    }
    Ok(())
}

fn collect_post_execution_if_have_indices<'a>(
    tactics: impl IntoIterator<Item = &'a DeferredPostExecutionTactic>,
    indices: &mut BTreeSet<usize>,
) {
    for deferred in tactics {
        let PostExecutionTactic::If {
            then_tactics,
            else_tactics,
            ..
        } = &deferred.tactic
        else {
            continue;
        };
        for arm in [then_tactics, else_tactics] {
            for nested in arm {
                match &nested.tactic {
                    PostExecutionTactic::Have(_) => {
                        indices.insert(nested.tactic_index);
                    }
                    PostExecutionTactic::If { .. } => {
                        collect_post_execution_if_have_indices(std::iter::once(nested), indices);
                    }
                    _ => {}
                }
            }
        }
    }
}

/// Selects the complete-proof route for supported top-level composite scopes
/// and execution branches. Tactics before, between, and after structures
/// remain linear; a scope body may also contain the checked C-branch forms
/// owned by the typed scope driver. Heap-backed contract predicates, scopes
/// nested inside branch arms, quantified scope bodies, and unsupported logical
/// structures retain their separately audited compatibility paths. Sequential
/// nested scopes, quantified contract resources, and counted populations use
/// the same checked resource entry and close operations as ordinary composite
/// scopes.
/// The terminal diagnostic for a proof no checked driver accepts. The
/// drivers are the single verification engine; a shape they decline is a
/// gap to close in a driver, never a reason to run a second engine.
fn unsupported_proof_shape(proof_label: &str) -> ClickError {
    let declines = take_driver_declines();
    let declined_at = if declines.is_empty() {
        String::new()
    } else {
        let sites = declines
            .iter()
            .map(|location| format!("{}:{}", location.file(), location.line()))
            .collect::<Vec<_>>();
        format!(" (driver declines: {})", sites.join(", "))
    };
    ClickError::new(format!(
        "`{proof_label}`: this proof shape is not accepted by the checked proof drivers{declined_at}"
    ))
}

fn leading_fixed_state_have_supported(have: &ProofHave) -> bool {
    // Proposition lowering and every accepted body operation are owned by the
    // nested Proof scope. Keep one capability query for that source driver;
    // a second leading-scope classifier can only lag behind checked steps
    // (as it previously did for `contradiction`).
    Proof::supports_linear_source(&have.proof)
}

/// Classifies the source-ordered empty-frame segment whose intervening outcome
/// operations are checked on `Proof`: after the latest execution operation,
/// every operation before the exact empty function frame must be a supported
/// `have`, checked transport, predicate unfold, theorem application,
/// proposition rewrite, or checked proposition closer. The returned indices
/// identify haves whose bodies become authoritative as part of this route;
/// the final flag records whether such a frame sealed a transport segment.
///
/// This is one linear source pass. In particular, admitting several haves does
/// not rescan their shared prefix or make explicit checking quadratic.
fn exact_empty_frame_outcome_segment(tactics: &[ProofTactic]) -> (bool, BTreeSet<usize>, bool) {
    let is_execution = |tactic: &ProofTactic| {
        matches!(
            tactic,
            ProofTactic::Step
                | ProofTactic::SmartExecute
                | ProofTactic::SmartExecuteAllPaths
                | ProofTactic::ExecuteUntil(_)
        )
    };
    let mut saw_execution = false;
    let mut segment_supported = false;
    let mut pending_haves = Vec::new();
    let mut authoritative_haves = BTreeSet::new();
    let mut pending_transport = false;
    let mut authoritative_transport = false;
    for (index, tactic) in tactics.iter().enumerate() {
        if is_execution(tactic) {
            saw_execution = true;
            segment_supported = true;
            pending_haves.clear();
            pending_transport = false;
            continue;
        }
        if saw_execution
            && segment_supported
            && matches!(tactic, ProofTactic::Have(have) if leading_fixed_state_have_supported(have))
        {
            pending_haves.push(index);
            continue;
        }
        if saw_execution
            && segment_supported
            && matches!(
                tactic,
                ProofTactic::Transport { .. } | ProofTactic::TransportUsing { .. }
            )
        {
            pending_transport = true;
            continue;
        }
        if saw_execution
            && segment_supported
            && matches!(tactic, ProofTactic::Assumption | ProofTactic::Normalize)
        {
            continue;
        }
        if saw_execution
            && segment_supported
            && matches!(
                tactic,
                ProofTactic::UnfoldPredicate(_)
                    | ProofTactic::ApplyTheorem(_)
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::Rewrite(_)
            )
        {
            continue;
        }
        if matches!(
            tactic,
            ProofTactic::FrameUsing {
                region: None | Some(CodeRegionRef::Function),
                premises,
            } if premises.is_empty()
        ) {
            if !saw_execution || !segment_supported {
                return (false, BTreeSet::new(), false);
            }
            authoritative_haves.extend(pending_haves.drain(..));
            authoritative_transport |= pending_transport;
            // A second empty frame needs its own execution segment.
            segment_supported = false;
            pending_transport = false;
            continue;
        }
        if saw_execution {
            segment_supported = false;
            pending_haves.clear();
            pending_transport = false;
        }
    }
    (true, authoritative_haves, authoritative_transport)
}

fn reject_grouped_top_level_existential_operations(
    proof_label: &str,
    tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    for (tactic_index, tactic) in tactics.iter().enumerate() {
        let operation = match tactic {
            ProofTactic::Witness(_) => "witness",
            ProofTactic::Choose(_) => "choose",
            _ => continue,
        };
        return Err(ClickError::new(format!(
            "`{proof_label}` tactic {tactic_index}: top-level `{operation}` is not available in a grouped proof; use it inside `have proposition by {{ ... }}`"
        )));
    }
    Ok(())
}

fn apply_checked_contract_resource_transition(
    outcome: &mut CFunctionOutcome,
    pre_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    available: &[Proposition],
    execution_facts: &[ExecutionPureFact],
    proof_label: &str,
    path_index: usize,
) -> Result<(), ClickError> {
    let mut facts = available.to_vec();
    facts.extend(
        execution_facts
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    let assumptions = assumptions_from_propositions(&facts);
    let (transitioned, _obligations) = apply_c_function_contract_resource_transition(
        pre_state,
        function,
        arguments,
        outcome.clone(),
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{proof_label}` path {path_index}: could not apply checked contract resource effect: {message}"
        ))
    })?;
    *outcome = transitioned;
    Ok(())
}

pub(in crate::lang::click) fn prove_claim_by_tactics(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<ClaimProofResult, ClickError> {
    if tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty explicit proof script"
        )));
    }
    let program = build_internal_proof_with_source(tactics, claim_label, tactic_source)?;
    let generated_by_source_index = match tactic_source {
        ProofTacticSource::SourceSyntax => None,
        ProofTacticSource::GeneratedBy { source_index } => Some(source_index),
    };
    let (state, arguments, pure_facts, surface_propositions) = initial_claim_context(
        function_block,
        parsed_function,
        resource_environment,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;
    let state = canonical_claim_caller_state(
        state,
        function_block
            .structural_clauses()
            .iter()
            .any(|clause| matches!(clause.region(), CodeRegion::Loop(_))),
        &function,
        &arguments,
        &pure_facts,
        claim_label,
    )?;
    let function_entry_state =
        c_function_entry_state(&state, &function, &arguments).ok_or_else(|| {
            ClickError::new(format!("`{claim_label}` could not bind function arguments"))
        })?;
    let proof_claims = [*claim];
    let constants = ExecutionProofConstants {
        proof_site: proof_site_for_claims(function_block, &proof_claims, false),
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        execution_start_facts: Arc::new(pure_facts.clone()),
        function_entry_state: Some(function_entry_state),
        grouped_contract: false,
    };
    let frontier = ExecutionFrontier::default();
    let mut recorded_snapshots = RecordedSnapshots::new();
    record_current_statement_entry(
        &frontier,
        &mut recorded_snapshots,
        &state,
        function_block,
        &function,
        &arguments,
        claim_label,
        0,
        "proof entry",
    )?;
    let initial = ExecutionProofState::at_entry(
        state,
        frontier,
        recorded_snapshots,
        surface_propositions,
        PersistentSequence::default(),
    );
    // The checked drivers are tried in order: the structural driver owns
    // scopes and branches, and the flat driver owns linear proofs. A decline
    // tries the next checked driver; an error is terminal.
    let structural = match try_check_structural_function_proof(
        &initial,
        &pure_facts,
        &constants,
        &program,
        generated_by_source_index,
        expansion_capture.as_deref_mut(),
        function_block,
        parsed_function,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    ) {
        Ok(proof) => proof,
        Err(error) => return Err(error),
    };
    let direct_proof = if structural.is_some() {
        structural
    } else {
        match try_check_flat_function_proof(
            &initial,
            &pure_facts,
            &constants,
            &program,
            generated_by_source_index,
            expansion_capture.as_deref_mut(),
            function_block,
            parsed_function,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            &function,
            &arguments,
        ) {
            Ok(proof) => proof,
            Err(error) => return Err(error),
        }
    };
    if let Some(proof) = direct_proof {
        match finish_ordered_proof_units(
            expansion_capture.as_deref_mut(),
            vec![proof],
            source_path,
            function_block,
            parsed_function,
            &proof_claims,
            false,
            predicate_environment,
            click_function_environment,
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
                return Ok(ClaimProofResult { theorems });
            }
            Err(error) => return Err(error),
        }
    }
    Err(unsupported_proof_shape(claim_label))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn prove_claims_by_grouped_tactics(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<ClaimProofResult, ClickError> {
    let proof_label = format!("{}.contract", function_block.signature().name());
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
    reject_grouped_top_level_existential_operations(&proof_label, tactics)?;
    let program = build_internal_proof_with_source(tactics, &proof_label, tactic_source)?;
    let generated_by_source_index = match tactic_source {
        ProofTacticSource::SourceSyntax => None,
        ProofTacticSource::GeneratedBy { source_index } => Some(source_index),
    };
    let (state, arguments, pure_facts, surface_propositions) = initial_claim_context(
        function_block,
        parsed_function,
        resource_environment,
        predicate_environment,
        click_function_environment,
        &proof_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        false,
    )?;
    let state = canonical_claim_caller_state(
        state,
        function_block
            .structural_clauses()
            .iter()
            .any(|clause| matches!(clause.region(), CodeRegion::Loop(_))),
        &function,
        &arguments,
        &pure_facts,
        &proof_label,
    )?;
    let function_entry_state =
        c_function_entry_state(&state, &function, &arguments).ok_or_else(|| {
            ClickError::new(format!("`{proof_label}` could not bind function arguments"))
        })?;
    let constants = ExecutionProofConstants {
        proof_site: proof_site_for_claims(function_block, claims, true),
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        execution_start_facts: Arc::new(pure_facts.clone()),
        function_entry_state: Some(function_entry_state),
        grouped_contract: true,
    };
    let frontier = ExecutionFrontier::default();
    let mut recorded_snapshots = RecordedSnapshots::new();
    record_current_statement_entry(
        &frontier,
        &mut recorded_snapshots,
        &state,
        function_block,
        &function,
        &arguments,
        &proof_label,
        0,
        "proof entry",
    )?;
    let initial = ExecutionProofState::at_entry(
        state,
        frontier,
        recorded_snapshots,
        surface_propositions,
        PersistentSequence::default(),
    );
    // Same order as the single-claim route: structural, then flat.
    let structural = match try_check_structural_function_proof(
        &initial,
        &pure_facts,
        &constants,
        &program,
        generated_by_source_index,
        expansion_capture.as_deref_mut(),
        function_block,
        parsed_function,
        &proof_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    ) {
        Ok(proof) => proof,
        Err(error) => return Err(error),
    };
    let direct_proof = if structural.is_some() {
        structural
    } else {
        match try_check_flat_function_proof(
            &initial,
            &pure_facts,
            &constants,
            &program,
            generated_by_source_index,
            expansion_capture.as_deref_mut(),
            function_block,
            parsed_function,
            &proof_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            &function,
            &arguments,
        ) {
            Ok(proof) => proof,
            Err(error) => return Err(error),
        }
    };
    if let Some(proof) = direct_proof {
        match finish_ordered_proof_units(
            expansion_capture.as_deref_mut(),
            vec![proof],
            source_path,
            function_block,
            parsed_function,
            claims,
            true,
            predicate_environment,
            click_function_environment,
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
                return Ok(ClaimProofResult { theorems });
            }
            Err(error) => return Err(error),
        }
    }
    Err(unsupported_proof_shape(&proof_label))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn prove_claims_by_grouped_auto(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut tactics = vec![ProofTactic::SmartExecute];
    tactics.extend(
        loop_effect_summary_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofTactic::FrameUsing {
                region: Some(CodeRegionRef::Loop(loop_index)),
                premises: Vec::new(),
            }),
    );
    if claims
        .iter()
        .any(|claim| matches!(claim, FunctionClaimRef::Effect(_, _)))
    {
        tactics.push(ProofTactic::FrameUsing {
            region: None,
            premises: Vec::new(),
        });
    }
    if claims
        .iter()
        .any(|claim| matches!(claim, FunctionClaimRef::Ensure(_, _)))
    {
        tactics.push(ProofTactic::Simp);
    }

    let verified = prove_claims_by_grouped_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &tactics,
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )?;
    Ok(verified.theorems)
}

/// An explicit grouped proof script. The completed proof unit is accepted
/// directly; retained provenance is serialized only for expansion.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn prove_claims_by_grouped_script(
    expansion_capture: Option<&mut ExpansionCapture>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let verified = prove_claims_by_grouped_tactics(
        expansion_capture,
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        tactics,
        ProofTacticSource::SourceSyntax,
    )?;
    Ok(verified.theorems)
}

/// Exit-claim closure: structural evidence that the current semantic proof
/// unit discharged a claim. Surface tactics are retained only as provenance;
/// they are not proof_candidate as an ordinary-verification acceptance gate.
///
/// Mid-execution the invariant is already structural — a smart operation can
/// continue only from its accepted checked `Proof` descendant, so "accepted
/// without a checked transition" is not synthesizable. At function exit the
/// per-claim drain used to write closure easily:
/// closure was `closed_claims[i] = true`, a bool any site could set, with the
/// surface records hanging off parallel arrays.
///
/// `ClosedClaim` restores the mid-execution shape. Its field is private to
/// this module, so no site outside can build one, and the variant that carries
/// a generated certificate has exactly one constructor:
/// `by_checked_certificate`, which accepts only a structured certificate
/// already checked either by the Proof API or by the remaining legacy
/// certifier. The other constructors each take the evidence that discharged
/// the claim.
mod exit_claim {
    use super::*;

    /// The certificate a closed exit claim carries.
    #[derive(Clone, Debug)]
    pub(super) enum ClaimCertificate {
        /// Surface tactics that discharge exactly this claim. They are
        /// appended to the claim's own expansion.
        Claim(Vec<ProofTactic>),
        /// Discharged by the path's grouped transition certificate, which
        /// covers every claim the transition closes and is recorded once for
        /// the path rather than once per claim.
        GroupedTransition,
        /// Discharged by an exact kernel check rather than a proof search:
        /// `assumption`, `normalize`, `frame`, a certified frame, or the
        /// implicit closer of a single-claim proof. Where the script written
        /// a closing tactic it is already in the path's recorded surface
        /// tactics; there is no search to certify.
        ExactCheck,
    }

    /// A claim closed at function exit, holding the certificate that
    /// discharged it. Only this module can build one.
    #[derive(Clone, Debug)]
    pub(super) struct ClosedClaim {
        certificate: ClaimCertificate,
    }

    impl ClosedClaim {
        /// The tactics this claim contributes to its own expansion. Grouped
        /// and exact closures contribute none: their tactics belong to the
        /// path's tactic list, not to one claim.
        pub(super) fn claim_tactics(&self) -> &[ProofTactic] {
            match &self.certificate {
                ClaimCertificate::Claim(tactics) => tactics,
                ClaimCertificate::GroupedTransition | ClaimCertificate::ExactCheck => &[],
            }
        }
    }

    /// A claim's state in the per-path exit drain.
    #[derive(Clone, Debug)]
    pub(super) enum ClaimClosure {
        /// Not discharged yet; carries the last closing attempt's message so
        /// the drain can explain an unproved claim.
        Open(Option<String>),
        Closed(ClosedClaim),
    }

    impl Default for ClaimClosure {
        fn default() -> Self {
            Self::Open(None)
        }
    }

    impl ClaimClosure {
        pub(super) fn is_closed(&self) -> bool {
            matches!(self, Self::Closed(_))
        }

        pub(super) fn closed(&self) -> Option<&ClosedClaim> {
            match self {
                Self::Closed(closed) => Some(closed),
                Self::Open(_) => None,
            }
        }

        pub(super) fn last_error(&self) -> Option<&str> {
            match self {
                Self::Open(error) => error.as_deref(),
                Self::Closed(_) => None,
            }
        }

        pub(super) fn record_failure(&mut self, message: String) {
            if let Self::Open(error) = self {
                *error = Some(message);
            }
        }

        /// Close a claim with a structured certificate already checked by a
        /// Proof successor or by the remaining explicit legacy certifier.
        pub(super) fn by_checked_certificate(certificate: &ProofCertificate) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::Claim(certificate.to_proof_tactics().to_vec()),
            })
        }

        /// Close a claim covered by the path's grouped transition
        /// certificate. Taking the certificate is the point: it is either the
        /// terminal output of the checked fixed-state-obligation Proof operation or
        /// the output of the remaining grouped legacy certifier.
        pub(super) fn by_grouped_transition(_certificate: &ProofCertificate) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::GroupedTransition,
            })
        }

        /// Close a claim that an exact kernel check discharged.
        pub(super) fn by_exact_check() -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::ExactCheck,
            })
        }
    }
}

use exit_claim::{ClaimClosure, ClosedClaim};

/// Selects the one ungrouped proposition claim refined by top-level
/// `choose`/`witness` operations and starts its result-aware judgment from the
/// current outcome Proof. Rewrites and active unfolds are re-applied inside
/// this independently serializable claim body exactly as expansion requires,
/// but every operation advances this retained Proof directly.
fn begin_outcome_existence_proof<'a>(
    outcome_root: &Proof<'a>,
    outcome: &CFunctionOutcome,
    path_requirements: &[Proposition],
    claims: &[FunctionClaimRef<'_>],
    closures: &[ClaimClosure],
    rewrite_claim_equalities: &[Vec<ClickProposition>],
    unfolded_predicates: &[String],
) -> Result<(usize, ClickProposition, Proof<'a>), ClickError> {
    let mut open = claims
        .iter()
        .enumerate()
        .filter_map(|(claim_index, claim)| {
            if closures[claim_index].is_closed() {
                return None;
            }
            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                return None;
            };
            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
                return None;
            };
            Some((claim_index, surface_goal.clone()))
        });
    let Some((claim_index, surface_goal)) = open.next() else {
        return Err(ClickError::new(
            "top-level existential operation has no current proposition claim",
        ));
    };
    if open.next().is_some() {
        return Err(ClickError::new(
            "top-level existential operation is ambiguous across multiple proposition claims",
        ));
    }

    let root = outcome_root
        .with_outcome_snapshot(outcome)?
        .with_checked_outcome_facts(path_requirements)?;
    let mut proof = root.focus_fixed_state_surface_goal(&surface_goal)?;
    for equality in &rewrite_claim_equalities[claim_index] {
        proof = proof.apply_step(ProofStep::Rewrite(equality.clone()))?;
    }
    // These steps make the retained nested body independently surface
    // checkable. An unfold already inherited by the outcome is harmlessly
    // skipped, matching the former checked-scope behavior.
    for name in unfolded_predicates {
        match proof.apply_step(ProofStep::UnfoldPredicate(name.clone())) {
            Ok(next) => proof = next,
            Err(_) => check_verification_deadline()?,
        }
    }
    Ok((claim_index, surface_goal, proof))
}

/// Serializes a completed existential claim Proof in the established
/// independently-checkable surface form. This is extraction only: the body
/// has already discharged the claim, and this certificate is never applied
/// during ordinary verification.
fn outcome_existence_surface_certificate(
    surface_goal: ClickProposition,
    completed: &Proof<'_>,
) -> ProofCertificate {
    ProofCertificate::from_steps(vec![
        ProofStep::Have {
            proposition: surface_goal,
            proof: Box::new(completed.certificate()),
        },
        ProofStep::Assumption,
    ])
}

#[derive(Clone)]
struct CachedIndependentExecution {
    pre_state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    concrete_loop_execution: bool,
    execution: CCheckedFunctionExecution,
}

thread_local! {
    static INDEPENDENT_EXECUTION_CACHE: std::cell::RefCell<Vec<CachedIndependentExecution>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Empties the independent-execution cache at a verification boundary: its
/// entries embed snapshots of the arena being retired.
pub(in crate::lang::click) fn clear_independent_execution_cache() {
    INDEPENDENT_EXECUTION_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Places a path-independent terminal frame on each explicit execution leaf.
/// The retained Proof provenance records the frame after the joined execution
/// branch; Surface Click must spell that same checked operation inside each
/// branch so the rewritten source can reach the corresponding frontier before
/// applying it. This is a structural serialization of retained provenance,
/// not a semantic search or reconstruction.
fn surface_steps_from_checked_proof(proof: &Proof<'_>) -> Result<Vec<ProofStep>, ClickError> {
    fn append_retained_tactics_to_leaves(tactics: &mut Vec<ProofTactic>, suffix: &[ProofTactic]) {
        if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
            append_retained_tactics_to_leaves(&mut proof_if.then_tactics, suffix);
            append_retained_tactics_to_leaves(&mut proof_if.else_tactics, suffix);
        } else {
            tactics.extend(suffix.iter().cloned());
        }
    }

    let mut tactics = proof.certificate().to_proof_tactics();
    let terminal_frame = matches!(
        tactics.last(),
        Some(ProofTactic::FrameUsing { region: None, .. })
    )
    .then(|| tactics.pop())
    .flatten();
    if let Some(frame) = terminal_frame {
        if let Some(ProofTactic::If(proof_if)) = tactics.last_mut() {
            append_retained_tactics_to_leaves(
                &mut proof_if.then_tactics,
                std::slice::from_ref(&frame),
            );
            append_retained_tactics_to_leaves(
                &mut proof_if.else_tactics,
                std::slice::from_ref(&frame),
            );
        } else {
            tactics.push(frame);
        }
    }
    ProofCertificate::from_proof_tactics(&tactics)
        .map(|certificate| certificate.steps().to_vec())
        .map_err(|error| {
            ClickError::new(format!(
                "checked Proof provenance is not surface-expressible: {error:?}"
            ))
        })
}

#[allow(clippy::too_many_arguments)]
fn cached_independent_execution(
    pre_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    concrete_loop_execution: bool,
    compute: impl FnOnce() -> CCheckedFunctionExecution,
) -> CCheckedFunctionExecution {
    if let Some(execution) = INDEPENDENT_EXECUTION_CACHE.with(|cache| {
        cache
            .borrow()
            .iter()
            .rev()
            .find(|entry| {
                entry.pre_state == *pre_state
                    && entry.function == *function
                    && entry.arguments == arguments
                    && entry.assumptions == *assumptions
                    && entry.environment == *environment
                    && entry.concrete_loop_execution == concrete_loop_execution
            })
            .map(|entry| entry.execution.clone())
    }) {
        return execution;
    }
    let execution = compute();
    if execution.limit().is_none() && !execution.paths().is_empty() {
        INDEPENDENT_EXECUTION_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.len() >= 32 {
                cache.remove(0);
            }
            cache.push(CachedIndependentExecution {
                pre_state: pre_state.clone(),
                function: function.clone(),
                arguments: arguments.to_vec(),
                assumptions: assumptions.clone(),
                environment: environment.clone(),
                concrete_loop_execution,
                execution: execution.clone(),
            });
        });
    }
    execution
}

fn proof_case_fact_conflicts(
    fact: &Proposition,
    assumptions: &PureFactContext,
) -> Result<bool, ()> {
    let conflicts = fact_conflicts_with_assumptions(fact, assumptions);
    if conflicts && crate::kernel::pure_fact_context_is_inconsistent(assumptions) {
        return Err(());
    }
    Ok(conflicts)
}

pub(super) fn finish_ordered_proof<'a>(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof: Proof<'a>,
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
    certificate_tactics: &[ProofTactic],
    certification_cache: &mut Vec<(Vec<Proposition>, CState, bool, CCheckedFunctionExecution)>,
    claim_surface_builders: &mut Vec<(VerifiedClaim, ProofCertificateBuilder)>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let proof_label = if require_explicit_closers {
        format!("{}.contract", function_block.signature().name())
    } else {
        function_claim_label(function_block.signature().name(), &claims[0])
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
    let mut authoritative_outcome_haves = exact_empty_frame_outcome_segment(certificate_tactics).1;
    collect_post_execution_if_have_indices(
        direct_view.execution.post_execution_tactics.iter(),
        &mut authoritative_outcome_haves,
    );
    let pure_facts = direct_view.facts.clone();
    let requirement_facts =
        Arc::new(pure_facts[..function_block.requires().len().min(pure_facts.len())].to_vec());
    let outcome_substrate = proof.split_function_outcomes(requirement_facts).ok();
    let (state, frontier, proof_execution, proof_context, branch_path) = (
        direct_view.state,
        direct_view.frontier,
        direct_view.execution,
        direct_view.context,
        direct_view.branch_path,
    );
    let retained_surface = {
        let record = &proof_execution.surface_record;
        let mut retained = ProofCertificateBuilder {
            last_step_entry: record.last_step_entry.clone(),
            path_choices: record.path_choices.clone(),
            blocker: record.blocker.clone(),
            ..ProofCertificateBuilder::default()
        };
        retained.steps = surface_steps_from_checked_proof(&proof)?;
        retained
    };
    let pre_state = frontier.execution_start_state(state);
    let frontier_function_block = (!proof_execution.frontier_loop_clauses.is_empty()).then(|| {
        function_block
            .with_bound_frontier_loop_clauses(&proof_execution.frontier_loop_clauses.to_vec())
    });
    let frontier_function = frontier_function_block
        .as_ref()
        .map(|frontier_function_block| {
            annotated_function(
                frontier_function_block,
                parsed_function,
                pre_state,
                arguments,
                predicate_environment,
                click_function_environment,
                resource_environment,
                false,
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
    let result = (|| {
        let execution = frontier.execution().ok_or_else(|| {
            ClickError::new(format!(
                "`{proof_label}` execution proof must reach function exit with `step()`, `execute()`, or `execute()`"
            ))
        })?;
        if execution.paths().is_empty() {
            return Err(ClickError::new(format!(
                "execution proof could not prove any complete execution path for `{proof_label}`"
            )));
        }
        let mut certification_facts = proof_context
            .constants
            .execution_start_facts
            .as_ref()
            .clone();
        certification_facts.extend(
            proof_execution
                .core
                .function_entry_execution_prerequisites
                .iter()
                .cloned(),
        );
        certification_facts.extend(
            proof_execution
                .case_assumptions
                .iter()
                .filter(|case| case.at_function_entry)
                .filter_map(|case| case.fact.clone()),
        );
        // Frontier-local loop clauses are bound after the initial claim
        // context is built.  Their phase proofs can unfold predicates just
        // like legacy structural clauses, so fresh whole-function
        // certification must expose those definitions at function entry as
        // well. Otherwise the proof can initialize an invariant from an
        // unfolded requirement while kernel certification sees only the
        // opaque predicate and rejects the verified loop rule.
        certification_facts = requirements_with_structural_unfolds(
            predicate_environment,
            click_function_environment,
            frontier_function_block.as_ref().unwrap_or(function_block),
            &certification_facts,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "kernel certification setup for `{proof_label}` failed: {message}"
            ))
        })?;
        // A checked unit that joined a terminal proof-level case split keeps
        // every case's outcome paths. Kernel certification runs once per
        // group of paths with the same recorded case decisions, with that
        // group's case facts assumed at function entry, as the compatibility
        // interpreter certifies each case as its own context.
        let path_case_facts: Vec<Vec<Proposition>> = (0..execution.paths().len())
            .map(|path_index| {
                direct_view
                    .path_case_decisions(path_index)
                    .into_iter()
                    .filter_map(|(condition, value)| {
                        let lowered = super::fixed_state_proofs::lower_fixed_state_proposition(
                            &condition,
                            &certification_facts,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            pre_state,
                            None,
                            &proof_execution.recorded_snapshots,
                            predicate_environment,
                            click_function_environment,
                        )
                        .ok()?;
                        let fact = if value {
                            lowered
                        } else {
                            Proposition::Not(Box::new(lowered))
                        };
                        Some(crate::kernel::canonical_condition_fact(&fact))
                    })
                    .collect()
            })
            .collect();
        let mut case_groups: Vec<(Vec<Proposition>, Vec<usize>)> = Vec::new();
        for (path_index, facts) in path_case_facts.iter().enumerate() {
            match case_groups
                .iter_mut()
                .find(|(group_facts, _)| group_facts == facts)
            {
                Some((_, members)) => members.push(path_index),
                None => case_groups.push((facts.clone(), vec![path_index])),
            }
        }
        if case_groups.is_empty() {
            case_groups.push((Vec::new(), Vec::new()));
        }
        let base_certification_facts = certification_facts;
        let mut certified_executions = Vec::with_capacity(case_groups.len());
        let mut certified_outcomes_by_group = Vec::with_capacity(case_groups.len());
        let mut merged_pairing: Vec<Option<(usize, usize)>> = vec![None; execution.paths().len()];
        for (group_index, (group_facts, group_members)) in case_groups.iter().enumerate() {
            let mut certification_facts = base_certification_facts.clone();
            for fact in group_facts {
                if !certification_facts.contains(fact) {
                    certification_facts.push(fact.clone());
                }
            }
            let certified_execution = crate::instrumentation::measure_operation(
                function_block.signature().name(),
                &proof_label,
                "independent kernel certification",
                || {
                    if proof_execution.core.frontier_loop_rules.is_empty()
                        && let Some((_, _, _, execution)) = certification_cache.iter().find(
                            |(facts, cached_state, concrete_loop_execution, _)| {
                                facts == &certification_facts
                                    && cached_state == pre_state
                                    && *concrete_loop_execution
                                        == proof_execution.core.concrete_loop_execution
                            },
                        )
                    {
                        execution.clone()
                    } else {
                        let execution_start_assumptions =
                            assumptions_from_propositions(&certification_facts);
                        let execution = cached_independent_execution(
                            pre_state,
                            function,
                            arguments,
                            &execution_start_assumptions,
                            function_environment,
                            proof_execution.core.concrete_loop_execution,
                            || {
                                prove_checked_c_function_execution_with_environment(
                                    pre_state.clone(),
                                    function.clone(),
                                    arguments.to_vec(),
                                    execution_start_assumptions.clone(),
                                    function_environment.clone(),
                                    if proof_execution.core.concrete_loop_execution
                                        || !proof_execution.core.frontier_loop_rules.is_empty()
                                    {
                                        CExecutionSemantics::APPLY_VERIFIED_RULES
                                    } else {
                                        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS
                                    },
                                    if proof_execution.core.concrete_loop_execution {
                                        CFunctionContractExecutionMode::ExecuteLoops
                                    } else {
                                        CFunctionContractExecutionMode::VerifyLoops
                                    },
                                )
                            },
                        );
                        if proof_execution.core.frontier_loop_rules.is_empty() {
                            certification_cache.push((
                                certification_facts.clone(),
                                pre_state.clone(),
                                proof_execution.core.concrete_loop_execution,
                                execution.clone(),
                            ));
                        }
                        execution
                    }
                },
            );
            let certified_execution = checked_c_function_execution_with_entry_derivations(
                certified_execution,
                proof_execution.core.function_entry_derivations.to_vec(),
                proof_execution
                    .core
                    .function_entry_execution_prerequisites
                    .to_vec(),
            );
            if let Some(limit) = certified_execution.limit() {
                if matches!(limit, crate::kernel::ExecutionLimit::Deadline) {
                    return Err(ClickError::new(format!(
                        "verification budget exhausted inside {}",
                        crate::instrumentation::deadline_context()
                    )));
                }
                return Err(ClickError::new(format!(
                    "kernel certification hit execution limit {limit:?} for `{proof_label}`"
                )));
            }
            let certified_outcomes = certified_execution
            .paths()
            .iter()
            .map(|path| match implication_body(path.theorem().proposition()) {
                Proposition::CFunctionVerifies {
                    state,
                    function: proved_function,
                    arguments: proved_arguments,
                    outcome,
                } if state == pre_state
                    && proved_function == function
                    && proved_arguments == arguments =>
                {
                    Ok(outcome.clone())
                }
                proposition => Err(ClickError::new(format!(
                    "kernel certification for `{proof_label}` produced an inexact theorem body {proposition:?}"
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;
            let proof_outcomes = execution
                .paths()
                .iter()
                .map(|path| path.outcome().clone())
                .collect::<Vec<_>>();
            let outcomes_match = |proof_candidate: &crate::kernel::CFunctionExecutionCandidate,
                                  certified_index: usize| {
                let certified = &certified_outcomes[certified_index];
                let certified_path = &certified_execution.paths()[certified_index];
                let certified_facts = certified_path
                    .execution_facts()
                    .into_iter()
                    .map(|fact| fact.proposition().clone())
                    .collect::<Vec<_>>();
                let proof_facts = proof_candidate
                    .execution_facts()
                    .into_iter()
                    .map(|fact| fact.proposition().clone())
                    .collect::<Vec<_>>();
                // Do not make two different branch paths appear equal by first
                // assuming their contradictory guards. In an inconsistent
                // context every outcome is provably equal, which used to pair a
                // recursive branch with an unrelated base-case certificate.
                let certified_path_conditions = certified_facts.iter().chain(
                    certified_path
                        .obligations()
                        .iter()
                        .map(ProofObligation::proposition),
                );
                let proof_path_conditions = proof_facts
                    .iter()
                    .chain(
                        proof_candidate
                            .obligations()
                            .iter()
                            .map(ProofObligation::proposition),
                    )
                    .collect::<Vec<_>>();
                if certified_path_conditions.into_iter().any(|certified_fact| {
                    proof_path_conditions.iter().any(|checked_fact| {
                        propositions_are_exact_negations(certified_fact, checked_fact)
                    })
                }) {
                    return false;
                }
                // A proof-level branch can select an execution path even when a
                // simple statement certificate deliberately omitted the C branch
                // guard from its own fact list. Include that selected branch when
                // pairing the check candidate with an independently certified
                // path, or a recursive return known to equal zero can be paired
                // with the unrelated base-case path merely because their final
                // observable values coincide.
                if !proof_execution.case_assumptions.is_empty() {
                    let CFunctionOutcome::Return {
                        value: result,
                        state: post_state,
                    } = proof_candidate.outcome()
                    else {
                        return false;
                    };
                    let mut proof_available = pure_facts.clone();
                    proof_available.extend(
                        proof_candidate
                            .facts()
                            .iter()
                            .map(|fact| fact.proposition().clone()),
                    );
                    for case in &proof_execution.case_assumptions {
                        let case_fact = if let Some(fact) = &case.fact {
                            fact.clone()
                        } else {
                            let Ok(condition) = lower_outcome_proposition_with_recorded_snapshots(
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &proof_available,
                                &case.condition,
                                predicate_environment,
                                click_function_environment,
                                &proof_execution.recorded_snapshots,
                            ) else {
                                return false;
                            };
                            if case.value {
                                condition
                            } else {
                                Proposition::Not(Box::new(condition))
                            }
                        };
                        if proof_path_conditions.iter().any(|checked_fact| {
                            propositions_are_exact_negations(checked_fact, &case_fact)
                        }) {
                            // The check execution still contains every C path;
                            // proof-level branching filters the incompatible ones
                            // later.  Such a path only needs its ordinary matching
                            // kernel certificate, not a certificate compatible
                            // with a proof branch that will discard it.
                            break;
                        }
                        if certified_facts.iter().any(|certified_fact| {
                            propositions_are_exact_negations(certified_fact, &case_fact)
                        }) {
                            return false;
                        }
                    }
                }
                let mut path_assumptions = certified_path.assumptions().clone();
                for fact in certification_facts.iter().chain(&certified_facts) {
                    path_assumptions = path_assumptions.assume_proposition(fact.clone());
                }
                for fact in &pure_facts {
                    path_assumptions = path_assumptions.assume_proposition(fact.clone());
                }
                for fact in proof_facts {
                    path_assumptions = path_assumptions.assume_proposition(fact);
                }
                for equation in
                    crate::kernel::certified_store_equations(&proof_candidate.execution_facts())
                        .into_iter()
                        .chain(crate::kernel::certified_store_equations(
                            &certified_path.execution_facts(),
                        ))
                {
                    path_assumptions = path_assumptions.assume_proposition(equation);
                }
                if let CFunctionOutcome::Return { state, .. } = certified
                    && let Ok(resource_facts) =
                        state.resources().observable_facts(&path_assumptions)
                {
                    for fact in resource_facts {
                        path_assumptions = path_assumptions.assume_proposition(fact);
                    }
                }
                c_function_outcomes_program_state_definitionally_equal(
                    proof_candidate.outcome(),
                    certified,
                    &path_assumptions,
                ) || c_function_outcomes_program_state_equal_by_execution_provenance(
                    proof_candidate.outcome(),
                    &proof_candidate.execution_facts(),
                    certified,
                    &certified_path.execution_facts(),
                    &path_assumptions,
                )
            };
            // A nested proof branch can carry a self-contradictory case set: its
            // sibling contexts own every execution path, and this context is
            // vacuous. Such a path needs no matching kernel certificate — the
            // exit drain below skips it by the same case reasoning.
            let path_excluded_by_proof_branch =
            |proof_candidate: &crate::kernel::CFunctionExecutionCandidate| -> Result<bool, ClickError> {
                if proof_execution.case_assumptions.is_empty() {
                    return Ok(false);
                }
                let CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                } = proof_candidate.outcome()
                else {
                    return Ok(false);
                };
                let mut available = pure_facts.clone();
                available.extend(
                    proof_candidate
                        .facts()
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                for case in &proof_execution.case_assumptions {
                    let fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let Ok(condition) = lower_outcome_proposition_with_recorded_snapshots(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &available,
                            &case.condition,
                            predicate_environment,
                            click_function_environment,
                            &proof_execution.recorded_snapshots,
                        ) else {
                            return Ok(false);
                        };
                        if case.value {
                            condition
                        } else {
                            Proposition::Not(Box::new(condition))
                        }
                    };
                    if available
                        .iter()
                        .any(|existing| propositions_are_exact_negations(existing, &fact))
                    {
                        return Ok(true);
                    }
                    let routed_assumptions = assumptions_from_propositions(&available);
                    match proof_case_fact_conflicts(&fact, &routed_assumptions) {
                        Ok(true) => return Ok(true),
                        Ok(false) => {}
                        Err(()) => {
                            return Err(ClickError::new(format!(
                                "execution pass for `{proof_label}` cannot attribute a path to a sibling proof branch: the routed assumptions are already inconsistent"
                            )));
                        }
                    }
                    available.push(fact);
                }
                Ok(false)
            };
            let certified_path_for_proof = crate::instrumentation::measure_operation(
                function_block.signature().name(),
                &proof_label,
                "certified outcome pairing",
                || -> Result<Option<Vec<Option<usize>>>, ClickError> {
                    if proof_execution.core.execution_abstraction {
                        return Ok((!certified_outcomes.is_empty())
                            .then(|| vec![Some(0); execution.paths().len()]));
                    }
                    let mut pairing = Vec::with_capacity(execution.paths().len());
                    for (path_index, proof_candidate) in execution.paths().iter().enumerate() {
                        if !group_members.contains(&path_index) {
                            pairing.push(None);
                            continue;
                        }
                        if outcome_substrate.as_ref().is_some_and(|(substrate, _)| {
                            substrate.outcome_branch_for_path(path_index).is_none()
                        }) {
                            // The Proof-owned N-way outcome derivation rejected
                            // this candidate under an exact contradictory path
                            // fact. It owns no semantic goal and needs no whole-
                            // function pairing; a compatible certified sibling
                            // remains addressed by its original path index.
                            pairing.push(None);
                            continue;
                        }
                        if let Some(certified_index) =
                            (0..certified_outcomes.len()).find(|certified_index| {
                                outcomes_match(proof_candidate, *certified_index)
                            })
                        {
                            pairing.push(Some(certified_index));
                        } else if path_excluded_by_proof_branch(proof_candidate)? {
                            pairing.push(None);
                        } else {
                            return Ok(None);
                        }
                    }
                    Ok(Some(pairing))
                },
            )?;
            let Some(certified_path_for_proof) = certified_path_for_proof else {
                // Outcome equality is a conservative kernel query: once the
                // ambient limit fires it returns `false`, which used to turn a
                // valid check into a ghost-region or memory mismatch. Give the
                // limit priority over the semantic pairing diagnostic.
                check_verification_deadline()?;
                return Err(ClickError::new(format!(
                    "execution pass for `{proof_label}` contains a path not reproduced by kernel certification\n  check: {proof_outcomes:?}\n  certified: {certified_outcomes:?}"
                )));
            };
            for &member in group_members {
                if let Some(certified_index) = certified_path_for_proof[member] {
                    merged_pairing[member] = Some((group_index, certified_index));
                }
            }
            certified_executions.push(certified_execution);
            certified_outcomes_by_group.push(certified_outcomes);
        }
        let certified_path_for_proof = merged_pairing;
        let certification_facts = base_certification_facts;
        let mut verified = Vec::new();
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_grouped_closers_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_branches_by_path = Vec::with_capacity(execution.paths().len());
        // Whether the implicit exact closer of a single-claim proof would
        // have discharged every open proposition claim on the path without
        // surface tactics. Consulted only when the captured expansions
        // disagree across paths (see the stitch below).
        let mut implicit_closure_by_path = Vec::with_capacity(execution.paths().len());

        crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &proof_label,
            "execution path finishing",
            || -> Result<(), ClickError> {
                'execution_path: for (path_index, path) in execution.paths().iter().enumerate() {
                    let _path_preparation_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "execution path preparation",
                    );
                    let Some(certified_path_index) = certified_path_for_proof[path_index] else {
                        // This context's proof-branch case set excludes the path; a
                        // sibling context certifies it.
                        continue 'execution_path;
                    };
                    let certified_path = &certified_executions[certified_path_index.0].paths()
                        [certified_path_index.1];
                    let mut path_grouped_surface_closers = Vec::new();
                    let mut path_surface_post_tactics = Vec::new();
                    let mut path_deferred_capture_tactics = Vec::new();
                    let missing_obligations = crate::instrumentation::measure_operation(
                        function_block.signature().name(),
                        &proof_label,
                        "path obligation lookup",
                        || {
                            path.obligations()
                                .iter()
                                .filter(|obligation| {
                                    !exact_fact_is_available(obligation.proposition(), &pure_facts)
                                })
                                .cloned()
                                .collect::<Vec<_>>()
                        },
                    );
                    if !missing_obligations.is_empty() {
                        return Err(ClickError::new(format!(
                            "execution proof failed for `{proof_label}` path {path_index}: {}",
                            describe_missing_proof_obligations(
                                &missing_obligations,
                                &pure_facts,
                                pre_state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                path.facts()
                            )
                        )));
                    }
                    let (mut outcome, mut path_requirements) =
                        crate::instrumentation::measure_operation(
                            function_block.signature().name(),
                            &proof_label,
                            "path fact working-set construction",
                            || {
                                let outcome = path.outcome().clone();
                                let mut path_requirements = pure_facts.clone();
                                path_requirements.extend(
                                    path.facts().iter().map(|fact| fact.proposition().clone()),
                                );
                                (outcome, path_requirements)
                            },
                        );
                    let _case_routing_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "proof case path routing",
                    );
                    if !proof_execution.case_assumptions.is_empty() {
                        let CFunctionOutcome::Return {
                            value: result,
                            state: post_state,
                        } = &outcome
                        else {
                            return Err(ClickError::new(format!(
                                "execution proof failed for `{proof_label}` path {path_index}: proof-level `if` requires a return outcome"
                            )));
                        };
                        let mut routed_assumptions =
                            assumptions_from_propositions(&path_requirements);
                        for case in &proof_execution.case_assumptions {
                            let case_lowering_timing = crate::instrumentation::OperationTiming::new(
                                function_block.signature().name(),
                                &proof_label,
                                "proof case condition lowering",
                            );
                            let fact = if let Some(fact) = &case.fact {
                                fact.clone()
                            } else {
                                let condition = lower_outcome_proposition_with_recorded_snapshots(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &path_requirements,
                            &case.condition,
                            predicate_environment,
                            click_function_environment,
                            &proof_execution.recorded_snapshots,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {}: could not lower `if` condition: {message}",
                                case.tactic_index
                            ))
                        })?;
                                if case.value {
                                    condition
                                } else {
                                    Proposition::Not(Box::new(condition))
                                }
                            };
                            drop(case_lowering_timing);
                            if crate::instrumentation::measure_operation(
                                function_block.signature().name(),
                                &proof_label,
                                "proof case exact-negation lookup",
                                || {
                                    path_requirements.iter().any(|available| {
                                        propositions_are_exact_negations(available, &fact)
                                    })
                                },
                            ) {
                                continue 'execution_path;
                            }
                            // Test the case fact against the incrementally maintained
                            // path assumptions. Some alias guards genuinely require
                            // the prover's whole-context inconsistency fallback, whose
                            // completed result is memoized by assumptions identity.
                            let case_conflicts = crate::instrumentation::measure_operation(
                                function_block.signature().name(),
                                &proof_label,
                                "proof case contradiction check",
                                || proof_case_fact_conflicts(&fact, &routed_assumptions),
                            );
                            match case_conflicts {
                                Err(()) => {
                                    return Err(ClickError::new(format!(
                                        "execution proof failed for `{proof_label}` path {path_index}: proof branch routing reached an inconsistent assumption context at tactic {}",
                                        case.tactic_index
                                    )));
                                }
                                Ok(true) => {
                                    // A proof-level branch only owns execution outcomes
                                    // compatible with its assumption.  The sibling branch
                                    // certifies this path; checking this branch's exact
                                    // per-outcome certificate against a contradictory
                                    // path would require it to list an unrelated
                                    // contradiction instead of the premises it was
                                    // generated from.
                                    continue 'execution_path;
                                }
                                Ok(false) => {}
                            }
                            routed_assumptions =
                                routed_assumptions.assume_proposition(fact.clone());
                            path_requirements.push(fact);
                        }
                    }
                    drop(_case_routing_timing);
                    // `None` marks a path-independent capture: an abstracted post-join
                    // path cannot decide the pre-join surface branches, and the tactic
                    // it carries belongs on every leaf.
                    let deferred_capture_branch_path = if let Some(deferred) =
                        proof_execution.expansion.deferred_tactic_capture.as_ref()
                    {
                        match &outcome {
                            CFunctionOutcome::Return {
                                value: result,
                                state: post_state,
                            } => direct_view
                                .surface_branch_path(path_index, &deferred.branch_skeleton)
                                .or_else(|| {
                                    surface_branch_path_for_outcome(
                                        &deferred.branch_skeleton,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        result,
                                        &proof_execution.recorded_snapshots,
                                        predicate_environment,
                                        click_function_environment,
                                    )
                                    // A compatibility post-join path may carry no
                                    // pre-join guard facts and therefore cannot decide
                                    // the surface branches. A completed Proof uses its
                                    // retained typed split provenance above.
                                    .ok()
                                }),
                            _ if deferred.branch_skeleton.is_empty() => Some(Vec::new()),
                            _ => {
                                return Err(ClickError::new(format!(
                                    "execution proof failed for `{proof_label}` path {path_index}: selected post-execution tactic has no return outcome for its proof branch"
                                )));
                            }
                        }
                    } else {
                        Some(Vec::new())
                    };
                    let mut unfolded_predicates = direct_view.unfolded_predicates.clone();
                    path_requirements = crate::instrumentation::measure_operation(
                        function_block.signature().name(),
                        &proof_label,
                        "path predicate fact unfolding",
                        || {
                            unfold_available_predicate_facts(
                                predicate_environment,
                                click_function_environment,
                                &unfolded_predicates,
                                &path_requirements,
                            )
                        },
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "execution proof failed for `{proof_label}` path {path_index}: {message}"
                        ))
                    })?;
                    path_requirements = crate::instrumentation::measure_operation(
                        function_block.signature().name(),
                        &proof_label,
                        "outcome resource fact projection",
                        || {
                            project_outcome_resource_facts(
                                resource_environment,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                &outcome,
                                &path_requirements,
                                predicate_environment,
                                click_function_environment,
                                &proof_label,
                                path_index,
                            )
                        },
                    )?;

                    let (
                        mut closures,
                        mut rewritten_claim_goals,
                        mut frame_certified_claim_goals,
                        mut surface_certificate_facts,
                        mut outcome_surface_propositions,
                    ) = crate::instrumentation::measure_operation(
                        function_block.signature().name(),
                        &proof_label,
                        "path certificate working-set construction",
                        || {
                            (
                                vec![ClaimClosure::default(); claims.len()],
                                vec![None::<Proposition>; claims.len()],
                                vec![None::<Proposition>; claims.len()],
                                path_requirements.clone(),
                                proof_execution.surface_propositions.clone(),
                            )
                        },
                    );
                    // The ordered surface equalities each claim's goal was
                    // rewritten through, parallel to `rewritten_claim_goals`.
                    // The direct Simp path checks them inside its checked
                    // `have` scope, so a rewritten claim proves the same
                    // rewritten goal the legacy closer checks.
                    let mut rewrite_claim_equalities: Vec<Vec<ClickProposition>> =
                        vec![Vec::new(); claims.len()];
                    // Facts established after execution all describe this fixed
                    // outcome snapshot. Keep them separately so `fold` can reuse an
                    // exact lowering without accidentally selecting the same surface
                    // form from an earlier program point.
                    let mut current_outcome_surface_propositions = SurfacePropositionMap::default();
                    // This path's evolving result-aware proof: tactic kinds
                    // that have migrated onto the outcome goal advance this
                    // one lineage and retain their checked steps directly.
                    // One authoritative import of the prepared working set
                    // happens here. Transport and `have` keep their own
                    // imports because theirs are semantic supersets.
                    let mut outcome_proof =
                        outcome_substrate.as_ref().and_then(|(substrate, _)| {
                            let goal = substrate.outcome_branch_for_path(path_index)?;
                            let focused = substrate.focus_branch(goal).ok()?;
                            focused
                                .with_outcome_snapshot(&outcome)
                                .and_then(|proof| {
                                    proof.with_checked_outcome_facts(&path_requirements)
                                })
                                .ok()
                        });
                    // An ungrouped top-level `choose`/`witness` refines one
                    // result-aware claim. Retain that typed judgment between
                    // source operations; syntax is recorded only for surface
                    // attribution, never reapplied as a candidate certificate.
                    let mut existence_proof = None;
                    // Contract resource/population effects are applied once
                    // at the frame that certifies them. A grouped proof sees
                    // the effect goals directly; an isolated ensure proof
                    // does not, but still needs the same transitioned outcome
                    // before lowering its postcondition.
                    let mut resource_transition_applied = false;
                    drop(_path_preparation_timing);
                    let _post_execution_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "post-execution claim tactics",
                    );
                    let mut selected_post_execution_tactics = Vec::new();
                    if let Some(branch_proof) = outcome_proof.as_ref() {
                        select_checked_post_execution_tactics(
                            branch_proof,
                            proof_execution.post_execution_tactics.iter(),
                            &mut selected_post_execution_tactics,
                        )?;
                    } else {
                        if proof_execution
                            .post_execution_tactics
                            .iter()
                            .any(|deferred| {
                                matches!(deferred.tactic, PostExecutionTactic::If { .. })
                            })
                        {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}: post-execution `if` has no focused outcome Proof"
                            )));
                        }
                        selected_post_execution_tactics
                            .extend(proof_execution.post_execution_tactics.iter());
                    }
                    for (post_execution_index, deferred) in
                        selected_post_execution_tactics.into_iter().enumerate()
                    {
                        let tactic_index = &deferred.tactic_index;
                        let source_index = &deferred.source_index;
                        let post_tactic = &deferred.tactic;
                        let _timing = crate::instrumentation::enabled().then(|| {
                            let (tactic_name, tactic_class) =
                                post_execution_tactic_timing(post_tactic);
                            if crate::instrumentation::starts_enabled() {
                                crate::instrumentation::emit(
                                    crate::instrumentation::VerificationEvent::TacticStarted(
                                        crate::instrumentation::TacticEvent {
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
                                claim_label: proof_label.clone(),
                                tactic_index: *tactic_index,
                                source_index: *source_index,
                                tactic_name: tactic_name.to_string(),
                                tactic_class: tactic_class.to_string(),
                                statement_index: frontier.next_statement_index,
                            };
                            push_timing_tactic(timing_context.clone());
                            TacticTiming {
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
                        match post_tactic {
                            PostExecutionTactic::Fold(resource) => {
                                let Some(evolving) = outcome_proof.take() else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: typed outcome `fold` has no Proof goal"
                                    )));
                                };
                                let before = evolving.checkpoint();
                                let folded = evolving
                                    .apply_step(ProofStep::FoldResource(resource.clone()))?;
                                outcome = folded.focused_outcome_snapshot()?;
                                let surface_tactics =
                                    folded.certificate_since(&before)?.to_proof_tactics();
                                outcome_proof = Some(folded);
                                for tactic in surface_tactics {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::CloseOpen {
                                resource,
                                preserve_exposed_body,
                            } => {
                                outcome = fold_composite_resources_on_outcome(
                                    resource_environment,
                                    std::slice::from_ref(resource),
                                    &proof_label,
                                    path_index,
                                    path.facts(),
                                    &path_requirements,
                                    &current_outcome_surface_propositions,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &unfolded_predicates,
                                    ResourceBodyClosure::CloseOpen {
                                        preserve_exposed_body: *preserve_exposed_body,
                                    },
                                )?;
                                path_requirements = project_outcome_resource_facts(
                                    resource_environment,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    &path_requirements,
                                    predicate_environment,
                                    click_function_environment,
                                    &proof_label,
                                    path_index,
                                )?;
                                // Install the checked resource projection on
                                // the retained outcome proof.
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving
                                            .with_outcome_snapshot(&outcome)?
                                            .with_checked_outcome_facts(&path_requirements)?,
                                    );
                                }
                            }
                            PostExecutionTactic::UnfoldPredicate(name) => {
                                let CFunctionOutcome::Return {
                                    value: _result,
                                    state: _post_state,
                                } = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: predicate unfolding requires a return outcome"
                                    )));
                                };

                                let (added_facts, certificate) = if let Some(evolving) =
                                    outcome_proof.take()
                                {
                                    // The migrated path: the tactic advances
                                    // this path's one evolving outcome proof
                                    // and retains its checked step directly.
                                    let before = evolving.checkpoint();
                                    let unfolded = evolving
                                        .apply_step(ProofStep::UnfoldPredicate(name.clone()))?;
                                    let added_facts = unfolded.added_facts().to_vec();
                                    let certificate = unfolded.certificate_since(&before)?;
                                    outcome_proof = Some(unfolded);
                                    (added_facts, certificate)
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                if !unfolded_predicates.contains(name) {
                                    unfolded_predicates.push(name.clone());
                                }
                                for fact in added_facts {
                                    if !path_requirements.contains(&fact) {
                                        path_requirements.push(fact.clone());
                                        if !surface_certificate_facts.contains(&fact) {
                                            surface_certificate_facts.push(fact);
                                        }
                                    }
                                }
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Apply(application) => {
                                let CFunctionOutcome::Return {
                                    value: _result,
                                    state: _post_state,
                                } = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: theorem application requires a return outcome"
                                    )));
                                };

                                let (added_facts, certificate) = if let Some(evolving) =
                                    outcome_proof.take()
                                {
                                    // The migrated smart case: selection reads
                                    // the goal-aware view and the accepted
                                    // application advances this path's
                                    // evolving outcome proof.
                                    let before = evolving.checkpoint();
                                    let applied =
                                        evolving.apply_theorem_application(application)?;
                                    let added_facts = applied.added_facts().to_vec();
                                    let certificate = applied.certificate_since(&before)?;
                                    outcome_proof = Some(applied);
                                    (added_facts, certificate)
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                // The retained `apply using` step is prefixed to every
                                // claim certificate, so independent verification holds the
                                // same checked conclusions when the closer runs.
                                for fact in added_facts {
                                    if !path_requirements.contains(&fact) {
                                        path_requirements.push(fact.clone());
                                        if !surface_certificate_facts.contains(&fact) {
                                            surface_certificate_facts.push(fact);
                                        }
                                    }
                                }
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::ApplyUsing {
                                application,
                                premises,
                            } => {
                                let CFunctionOutcome::Return {
                                    value: _result,
                                    state: _post_state,
                                } = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: theorem application requires a return outcome"
                                    )));
                                };

                                let added_facts = if let Some(evolving) = outcome_proof.take() {
                                    // The migrated explicit case: the checked
                                    // application advances this path's
                                    // evolving outcome proof directly.
                                    let applied =
                                        evolving.apply_step(ProofStep::ApplyTheoremUsing {
                                            application: application.clone(),
                                            premises: premises.clone(),
                                        })?;
                                    let added_facts = applied.added_facts().to_vec();
                                    outcome_proof = Some(applied);
                                    added_facts
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                for fact in added_facts {
                                    if !path_requirements.contains(&fact) {
                                        path_requirements.push(fact.clone());
                                        if !surface_certificate_facts.contains(&fact) {
                                            surface_certificate_facts.push(fact);
                                        }
                                    }
                                }
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::ApplyTheoremUsing {
                                        application: application.clone(),
                                        premises: premises.clone(),
                                    },
                                );
                            }
                            PostExecutionTactic::Have(have) => {
                                let CFunctionOutcome::Return { .. } = &outcome else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `have` requires a return outcome"
                                    )));
                                };
                                let certificate_available =
                                    crate::instrumentation::measure_operation(
                                        function_block.signature().name(),
                                        &proof_label,
                                        "post-execution have context assembly",
                                        || {
                                            let mut available = path_requirements.clone();
                                            for fact in &proof_execution.core.effect_facts {
                                                if matches!(
                                                    fact.proposition(),
                                                    Proposition::CMemoryMutatesOnly { .. }
                                                        | Proposition::CMemoryEffectSummary { .. }
                                                        | Proposition::CHeapAllocationFreed { .. }
                                                ) && !available.contains(fact.proposition())
                                                {
                                                    available.push(fact.proposition().clone());
                                                }
                                            }
                                            for equation in crate::kernel::certified_store_equations(
                                                &proof_execution.core.effect_facts,
                                            ) {
                                                if !available.contains(&equation) {
                                                    available.push(equation);
                                                }
                                            }
                                            for fact in
                                                crate::kernel::certified_store_loadability_facts(
                                                    &proof_execution.core.effect_facts,
                                                )
                                            {
                                                if !available.contains(&fact) {
                                                    available.push(fact);
                                                }
                                            }
                                            available
                                        },
                                    );
                                // Post-execution proof certificates check against
                                // the same kernel-certified loadability consequences
                                // of stores that were available while planning them.
                                // Restricting these facts to hand-written `derive`
                                // scripts let smart `simp` search succeed and then
                                // fail when its generated certificate was proof_candidate.
                                // The migrated path first: the `have` scope
                                // opens on this path's evolving outcome proof.
                                // Haves in the audited execute/have/empty-frame
                                // segment are authoritative; other outcome
                                // shapes retain their compatibility adapter.
                                let authoritative_have =
                                    authoritative_outcome_haves.contains(tactic_index);
                                let Some(evolving_root) = outcome_proof.take() else {
                                    // The unconditional substrate makes this
                                    // unreachable; fail loudly rather than
                                    // silently routing the whole `have`
                                    // through the deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                let evolving_have = {
                                    let evolving = evolving_root;
                                    let attempt = (|| -> Result<
                                        Option<(Proof<'_>, Proposition, ProofCertificate)>,
                                        ClickError,
                                    > {
                                        let resynced = evolving
                                            .with_outcome_snapshot(&outcome)?
                                            .with_checked_outcome_facts(&certificate_available)?;
                                        let before = resynced.checkpoint();
                                        let scope =
                                            resynced.begin_have(have.proposition.clone())?;
                                        let selected = match &have.proof {
                                            SourceProof::Default
                                            | SourceProof::Tactic(
                                                SmartTactic::Auto | SmartTactic::Simp,
                                            ) => scope.try_simp_closure()?,
                                            SourceProof::Script(tactics) => {
                                                let selected = if authoritative_have {
                                                    scope.try_authoritative_linear_script(tactics)?
                                                } else {
                                                    scope.try_linear_script(tactics)?
                                                };
                                                match selected {
                                                    Some(selected) => Some(selected),
                                                    None if !authoritative_have => {
                                                        scope.try_planned_linear_script(tactics)?
                                                    }
                                                    None => None,
                                                }
                                            }
                                            SourceProof::Tactic(SmartTactic::Frame) => None,
                                        };
                                        let Some(closed) = selected else {
                                            return Err(ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `have` search did not retain a complete proof",
                                            )));
                                        };
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
                                            outcome_proof = Some(joined);
                                            Some((fact, Some(certificate)))
                                        }
                                        None => {
                                            outcome_proof = Some(evolving);
                                            None
                                        }
                                    }
                                };
                                let Some((fact, Some(certificate))) = evolving_have else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `have` did not retain a complete certificate",
                                    )));
                                };
                                let tactics = certificate.to_proof_tactics();
                                let [surface_have] = tactics.as_slice() else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked smart `have` did not retain one `have` certificate"
                                    )));
                                };
                                let surface_have = surface_have.clone();
                                outcome_surface_propositions
                                    .record_lowering(&have.proposition, &fact)?;
                                current_outcome_surface_propositions
                                    .record_lowering(&have.proposition, &fact)?;
                                if !path_requirements.contains(&fact) {
                                    path_requirements.push(fact);
                                }
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    surface_have,
                                );
                            }
                            PostExecutionTactic::Transport {
                                source,
                                target,
                                premises,
                            } => {
                                let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
                                } = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `transport` requires a return outcome"
                                    )));
                                };

                                let transition_facts = path.execution_facts();
                                let mut transport_available = path_requirements.clone();
                                for equation in
                                    crate::kernel::certified_store_equations(&transition_facts)
                                {
                                    if outcome_surface_propositions
                                        .surfaces(&equation)
                                        .next()
                                        .is_some()
                                        && !transport_available.contains(&equation)
                                    {
                                        transport_available.push(equation);
                                    }
                                }
                                let path_unfolds = direct_view.unfolded_predicates.to_vec();
                                let candidates = if premises.is_none() {
                                    Some(fact_transport_candidates_at_outcome(
                                        &transport_available,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        result,
                                        proof_execution.view(proof_context),
                                        &path_unfolds,
                                        predicate_environment,
                                        click_function_environment,
                                    )?)
                                } else {
                                    None
                                };
                                let (added_facts, checked_facts, certificate) = if let Some(
                                    evolving,
                                ) =
                                    outcome_proof.take()
                                {
                                    // The migrated cases: an explicit
                                    // transport applies its source step and
                                    // a smart one searches its gathered
                                    // candidates, both advancing this
                                    // path's evolving outcome proof, which
                                    // records the checked lowerings on the
                                    // goal atomically.
                                    let resynced = evolving
                                        .with_outcome_snapshot(&outcome)?
                                        .with_checked_outcome_facts(&transport_available)?;
                                    let before = resynced.checkpoint();
                                    let transported = if let Some(premises) = premises {
                                        resynced.apply_step(ProofStep::TransportUsing {
                                            source: source.clone(),
                                            target: target.clone(),
                                            premises: premises.clone(),
                                        })?
                                    } else {
                                        resynced.search_fixed_state_fact_transport(
                                            source,
                                            target,
                                            candidates
                                                .clone()
                                                .expect("smart transport gathered candidates"),
                                        )?
                                    };
                                    let added_facts = transported.added_facts().to_vec();
                                    let checked_facts = transported.checked_facts().to_vec();
                                    let certificate = transported.certificate_since(&before)?;
                                    outcome_proof = Some(transported);
                                    (added_facts, checked_facts, certificate)
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                let [checked_source, checked_target] = checked_facts.as_slice()
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked transport did not retain its source and target"
                                    )));
                                };
                                outcome_surface_propositions
                                    .record_lowering(source, checked_source)?;
                                outcome_surface_propositions
                                    .record_lowering(target, checked_target)?;
                                for fact in added_facts {
                                    if !path_requirements.contains(&fact) {
                                        path_requirements.push(fact.clone());
                                        if !surface_certificate_facts.contains(&fact) {
                                            surface_certificate_facts.push(fact);
                                        }
                                    }
                                }
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Choose(choice) => {
                                let (claim_index, surface_goal, proof) =
                                    match existence_proof.take() {
                                        Some(active) => active,
                                        None => begin_outcome_existence_proof(
                                            outcome_proof.as_ref().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for `choose` is unavailable"
                                                ))
                                            })?,
                                            &outcome,
                                            &path_requirements,
                                            claims,
                                            &closures,
                                            &rewrite_claim_equalities,
                                            &unfolded_predicates,
                                        )?,
                                    };
                                let proof = proof
                                    .with_outcome_snapshot(&outcome)?
                                    .apply_step(ProofStep::Choose(choice.clone()))?;
                                existence_proof = Some((claim_index, surface_goal, proof));
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::Choose(choice.clone()),
                                );
                            }
                            PostExecutionTactic::Witness(witness) => {
                                let (claim_index, surface_goal, proof) =
                                    match existence_proof.take() {
                                        Some(active) => active,
                                        None => begin_outcome_existence_proof(
                                            outcome_proof.as_ref().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for `witness` is unavailable"
                                                ))
                                            })?,
                                            &outcome,
                                            &path_requirements,
                                            claims,
                                            &closures,
                                            &rewrite_claim_equalities,
                                            &unfolded_predicates,
                                        )?,
                                    };
                                let proof = proof
                                    .with_outcome_snapshot(&outcome)?
                                    .apply_step(ProofStep::Witness(witness.clone()))?;
                                existence_proof = Some((claim_index, surface_goal, proof));
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::Witness(witness.clone()),
                                );
                            }
                            PostExecutionTactic::Assumption => {
                                let mut closed_any = false;
                                let transition_facts = path.execution_facts();
                                // Claim closers focus fresh obligation roots;
                                // the evolving outcome proof supplies them
                                // when this path derived a goal.
                                let fixed_state_root = match (outcome_proof.as_ref(), &outcome) {
                                    (Some(evolving), _) => Some(evolving.clone()),
                                    (
                                        None,
                                        CFunctionOutcome::Return {
                                            value: result,
                                            state: post_state,
                                        },
                                    ) => Some(Proof::for_fixed_state_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &proof_execution.recorded_snapshots,
                                        &outcome_surface_propositions,
                                        predicate_environment,
                                        click_function_environment,
                                        theorem_environment,
                                        &unfolded_predicates,
                                        &transition_facts,
                                    )),
                                    (
                                        None,
                                        CFunctionOutcome::VerificationDiverges
                                        | CFunctionOutcome::UndefinedBehavior(_)
                                        | CFunctionOutcome::RuntimeError(_),
                                    ) => None,
                                };
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                        continue;
                                    };
                                    if let Ensure::Resource(resource) = ensure_clause.ensure() {
                                        if prove_ensure_resource(
                                            &function_claim_label(
                                                function_block.signature().name(),
                                                claim,
                                            ),
                                            path_index,
                                            &path.execution_facts(),
                                            &path_requirements,
                                            resource,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                        )
                                        .is_ok()
                                        {
                                            closures[claim_index] = ClaimClosure::by_exact_check();
                                            closed_any = true;
                                            break;
                                        }
                                        continue;
                                    }
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        unreachable!("resource ensures were handled above")
                                    };
                                    let goal = match &rewritten_claim_goals[claim_index] {
                                        Some(goal) => goal.clone(),
                                        None => {
                                            if let Some(recorded) = outcome_surface_propositions
                                                .available_kernel(surface_goal, &path_requirements)
                                            {
                                                recorded.clone()
                                            } else {
                                                lower_ensure_proposition_goal(
                                            &path_requirements,
                                            surface_goal,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                            predicate_environment,
                                            click_function_environment,
                                            &proof_execution.recorded_snapshots,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` could not lower goal: {message}"
                                            ))
                                        })?
                                            }
                                        }
                                    };
                                    let Some(fixed_state_root) = &fixed_state_root else {
                                        continue;
                                    };
                                    match fixed_state_root
                                        .focus_fixed_state_goal(goal)?
                                        .apply_step(ProofStep::Assumption)
                                    {
                                        Ok(proof) => {
                                            retained_certificate = Some(proof.certificate());
                                            closures[claim_index] = ClaimClosure::by_exact_check();
                                            closed_any = true;
                                            break;
                                        }
                                        Err(_) => check_verification_deadline()?,
                                    }
                                }
                                if !closed_any {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` did not match any current proposition goal"
                                    )));
                                }
                                let tactics = retained_certificate
                                    .as_ref()
                                    .map(ProofCertificate::to_proof_tactics)
                                    .unwrap_or_else(|| vec![ProofTactic::Assumption]);
                                for tactic in tactics {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Normalize => {
                                let mut closed_any = false;
                                let transition_facts = path.execution_facts();
                                // Claim closers focus fresh obligation roots;
                                // the evolving outcome proof supplies them
                                // when this path derived a goal.
                                let fixed_state_root = match (outcome_proof.as_ref(), &outcome) {
                                    (Some(evolving), _) => Some(evolving.clone()),
                                    (
                                        None,
                                        CFunctionOutcome::Return {
                                            value: result,
                                            state: post_state,
                                        },
                                    ) => Some(Proof::for_fixed_state_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &proof_execution.recorded_snapshots,
                                        &outcome_surface_propositions,
                                        predicate_environment,
                                        click_function_environment,
                                        theorem_environment,
                                        &unfolded_predicates,
                                        &transition_facts,
                                    )),
                                    (
                                        None,
                                        CFunctionOutcome::VerificationDiverges
                                        | CFunctionOutcome::UndefinedBehavior(_)
                                        | CFunctionOutcome::RuntimeError(_),
                                    ) => None,
                                };
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                        continue;
                                    };
                                    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
                                        // Postconditions are conditional on return.
                                        // Normalization exposes that definitional
                                        // partial-correctness rule without requiring a
                                        // nonexistent return value or state.
                                        closures[claim_index] = ClaimClosure::by_exact_check();
                                        closed_any = true;
                                        continue;
                                    }
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        continue;
                                    };
                                    let goal = match &rewritten_claim_goals[claim_index] {
                                        Some(goal) => goal.clone(),
                                        None => lower_ensure_proposition_goal(
                                            &path_requirements,
                                            surface_goal,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                            predicate_environment,
                                            click_function_environment,
                                            &proof_execution.recorded_snapshots,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` could not lower goal: {message}"
                                            ))
                                        })?,
                                    };
                                    let Some(fixed_state_root) = &fixed_state_root else {
                                        continue;
                                    };
                                    match fixed_state_root
                                        .focus_fixed_state_goal(goal)?
                                        .apply_step(ProofStep::Normalize)
                                    {
                                        Ok(proof) => {
                                            retained_certificate
                                                .get_or_insert_with(|| proof.certificate());
                                            closures[claim_index] = ClaimClosure::by_exact_check();
                                            closed_any = true;
                                        }
                                        Err(_) => check_verification_deadline()?,
                                    }
                                }
                                if !closed_any {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` did not prove any current proposition goal"
                                    )));
                                }
                                let tactics = retained_certificate
                                    .as_ref()
                                    .map(ProofCertificate::to_proof_tactics)
                                    .unwrap_or_else(|| vec![ProofTactic::Normalize]);
                                for tactic in tactics {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Rewrite(surface_equality) => {
                                let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
                                } = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` requires a return outcome"
                                    )));
                                };
                                let transition_facts = path.execution_facts();
                                // Claim-goal rewrites focus fresh obligation
                                // roots; the evolving outcome proof supplies
                                // them when this path derived a goal, and the
                                // path lineage itself is not advanced.
                                let fixed_state_root = match outcome_proof.as_ref() {
                                    Some(evolving) => evolving.clone(),
                                    None => Proof::for_fixed_state_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &proof_execution.recorded_snapshots,
                                        &outcome_surface_propositions,
                                        predicate_environment,
                                        click_function_environment,
                                        theorem_environment,
                                        &unfolded_predicates,
                                        &transition_facts,
                                    ),
                                };
                                let mut rewrote_any = false;
                                let mut first_error = None;
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                        continue;
                                    };
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        continue;
                                    };
                                    let goal = match &rewritten_claim_goals[claim_index] {
                                        Some(goal) => goal.clone(),
                                        None => lower_ensure_proposition_goal(
                                            &path_requirements,
                                            surface_goal,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                            predicate_environment,
                                            click_function_environment,
                                            &proof_execution.recorded_snapshots,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` could not lower goal: {message}"
                                            ))
                                        })?,
                                    };
                                    match fixed_state_root
                                        .focus_fixed_state_goal(goal)?
                                        .apply_step(ProofStep::Rewrite(surface_equality.clone()))
                                    {
                                        Ok(proof) => {
                                            let rewritten = proof.goal().cloned().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked `rewrite` lost its proposition goal"
                                                ))
                                            })?;
                                            retained_certificate
                                                .get_or_insert_with(|| proof.certificate());
                                            rewritten_claim_goals[claim_index] = Some(rewritten);
                                            rewrite_claim_equalities[claim_index]
                                                .push(surface_equality.clone());
                                            rewrote_any = true;
                                        }
                                        Err(error) => {
                                            check_verification_deadline()?;
                                            first_error
                                                .get_or_insert_with(|| error.message().to_string());
                                        }
                                    }
                                }
                                if !rewrote_any {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` failed: {}",
                                        first_error.unwrap_or_else(|| {
                                            "there is no current proposition goal".to_string()
                                        })
                                    )));
                                }
                                for tactic in retained_certificate
                                    .expect("a successful rewrite retains its checked Proof")
                                    .to_proof_tactics()
                                {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::FrameRegion(_region) => {
                                for (claim_index, goal) in frame_certified_ensure_goals(
                                    claims,
                                    &path.execution_facts(),
                                    &path_requirements,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &proof_execution.recorded_snapshots,
                                    &unfolded_predicates,
                                ) {
                                    frame_certified_claim_goals[claim_index] = Some(goal.clone());
                                    if !path_requirements.contains(&goal) {
                                        path_requirements.push(goal.clone());
                                        if !surface_certificate_facts.contains(&goal) {
                                            surface_certificate_facts.push(goal);
                                        }
                                    }
                                }
                                // Install the certified region-frame goal on
                                // the retained outcome proof.
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving
                                            .with_outcome_snapshot(&outcome)?
                                            .with_checked_outcome_facts(&path_requirements)?,
                                    );
                                }
                            }
                            PostExecutionTactic::Frame => {
                                let mut closed_effect = false;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                        continue;
                                    }
                                    let claim_label = function_claim_label(
                                        function_block.signature().name(),
                                        claim,
                                    );
                                    check_effect_claim_exact(
                                        &claim_label,
                                        path_index,
                                        &path.execution_facts(),
                                        &path_requirements,
                                        claim,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        &outcome,
                                    )?;
                                    closures[claim_index] = ClaimClosure::by_exact_check();
                                    closed_effect = true;
                                }
                                if closed_effect
                                    || (!resource_transition_applied
                                        && !claims.iter().any(|claim| {
                                            matches!(claim, FunctionClaimRef::Effect(_, _))
                                        }))
                                {
                                    apply_checked_contract_resource_transition(
                                        &mut outcome,
                                        pre_state,
                                        function,
                                        arguments,
                                        &path_requirements,
                                        &path.execution_facts(),
                                        &proof_label,
                                        path_index,
                                    )?;
                                    resource_transition_applied = true;
                                    if let Some(evolving) = outcome_proof.take() {
                                        outcome_proof = Some(
                                            evolving
                                                .with_outcome_snapshot(&outcome)?
                                                .with_checked_outcome_facts(&path_requirements)?,
                                        );
                                    }
                                }
                                // The ambient frame checks against every available
                                // fact; its checkable surface form is exactly
                                // `frame()`. Form out one snapshot's surface facts
                                // here produced a premise list check could not
                                // re-establish.
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::FrameUsing {
                                        region: None,
                                        premises: Vec::new(),
                                    },
                                );
                            }
                            PostExecutionTactic::FrameUsing { region, premises } => {
                                let Some(evolving) = outcome_proof.take() else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: typed outcome `frame using` has no Proof goal"
                                    )));
                                };
                                let before = evolving.checkpoint();
                                let framed = evolving.apply_step_at(
                                    ProofStep::FrameUsing {
                                        region: region.clone(),
                                        premises: premises.clone(),
                                    },
                                    *tactic_index,
                                    *source_index,
                                )?;
                                let authority = framed.checked_outcome_frame_authority()?;
                                let mut matched = 0;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    let FunctionClaimRef::Effect(effect_index, _) = claim else {
                                        continue;
                                    };
                                    if !authority.contains(*effect_index) {
                                        continue;
                                    }
                                    closures[claim_index] = ClaimClosure::by_exact_check();
                                    matched += 1;
                                }
                                if matched != authority.len() {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome frame selected {} effect goals but ordered finalization owns {matched}",
                                        authority.len()
                                    )));
                                }
                                outcome = framed.focused_outcome_snapshot()?;
                                resource_transition_applied = true;
                                let certificate = framed.certificate_since(&before)?;
                                for tactic in certificate.to_proof_tactics() {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                                outcome_proof = Some(framed);
                                continue;
                            }
                            PostExecutionTactic::CheckedFrameUsing {
                                authority,
                                region,
                                premises,
                                surface_tactics,
                            } => {
                                if authority.is_empty() {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked frame authority contains no effect goals"
                                    )));
                                }
                                let mut matched = 0;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    let FunctionClaimRef::Effect(effect_index, _) = claim else {
                                        continue;
                                    };
                                    if !authority.contains(*effect_index) {
                                        continue;
                                    }
                                    closures[claim_index] = ClaimClosure::by_exact_check();
                                    matched += 1;
                                }
                                if matched != authority.len() {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: checked frame authority selected {} effect goals but ordered finalization owns {matched}",
                                        authority.len()
                                    )));
                                }
                                crate::instrumentation::measure_operation(
                                    function_block.signature().name(),
                                    &proof_label,
                                    "frame resource transition",
                                    || {
                                        apply_checked_contract_resource_transition(
                                            &mut outcome,
                                            pre_state,
                                            function,
                                            arguments,
                                            &path_requirements,
                                            &path.execution_facts(),
                                            &proof_label,
                                            path_index,
                                        )
                                    },
                                )?;
                                resource_transition_applied = true;
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving
                                            .with_outcome_snapshot(&outcome)?
                                            .with_checked_outcome_facts(&path_requirements)?,
                                    );
                                }
                                if let Some(surface_tactics) = surface_tactics {
                                    for tactic in surface_tactics {
                                        record_post_execution_surface_tactic(
                                            deferred.surface_recorded,
                                            &mut path_surface_post_tactics,
                                            &mut path_deferred_capture_tactics,
                                            proof_execution
                                                .expansion
                                                .deferred_tactic_capture
                                                .as_ref(),
                                            post_execution_index,
                                            *tactic_index,
                                            tactic.clone(),
                                        );
                                    }
                                } else {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution.expansion.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        ProofTactic::FrameUsing {
                                            region: region.clone(),
                                            premises: premises.clone(),
                                        },
                                    );
                                }
                            }
                            PostExecutionTactic::If { .. } => unreachable!(
                                "post-execution branch selection must flatten control nodes before checking leaf tactics"
                            ),
                            PostExecutionTactic::Simp => {
                                let capturing_this_tactic = proof_execution
                                    .expansion
                                    .deferred_tactic_capture
                                    .as_ref()
                                    .is_some_and(|capture| capture.tactic_index == *tactic_index);
                                if let Some((claim_index, surface_goal, proof)) =
                                    existence_proof.take()
                                {
                                    let proof = proof.with_outcome_snapshot(&outcome)?;
                                    let completed = if let Some(completed) =
                                        proof.try_direct_logical_closure()?
                                    {
                                        completed
                                    } else if let Some(completed) = proof.try_simp_closure()? {
                                        completed
                                    } else {
                                        let claim_label = function_claim_label(
                                            function_block.signature().name(),
                                            &claims[claim_index],
                                        );
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `simp` did not complete the retained existential Proof for `{claim_label}`"
                                        )));
                                    };
                                    if !completed.is_complete() {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: retained existential Proof remained incomplete after `simp`"
                                        )));
                                    }
                                    let certificate = outcome_existence_surface_certificate(
                                        surface_goal,
                                        &completed,
                                    );
                                    closures[claim_index] =
                                        ClaimClosure::by_checked_certificate(&certificate);
                                    if capturing_this_tactic {
                                        path_deferred_capture_tactics
                                            .extend(certificate.to_proof_tactics());
                                    }
                                    continue;
                                }
                                // A divergent path has no outcome to prove
                                // claims against; every open ensure closes
                                // with the same trivial Normalize certificate
                                // the legacy discharge emits for divergence.
                                if matches!(&outcome, CFunctionOutcome::VerificationDiverges) {
                                    let certificate = ProofCertificate::from_proof_tactics(&[
                                        ProofTactic::Normalize,
                                    ])
                                    .map_err(|error| {
                                        ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: divergence produced an invalid normalize certificate: {error:?}"
                                        ))
                                    })?;
                                    for (claim_index, claim) in claims.iter().enumerate() {
                                        if closures[claim_index].is_closed() {
                                            continue;
                                        }
                                        let FunctionClaimRef::Ensure(_, _) = claim else {
                                            continue;
                                        };
                                        closures[claim_index] =
                                            ClaimClosure::by_checked_certificate(&certificate);
                                        if proof_context.constants.grouped_contract {
                                            path_grouped_surface_closers
                                                .extend(certificate.to_proof_tactics());
                                        }
                                        if capturing_this_tactic {
                                            path_deferred_capture_tactics
                                                .extend(certificate.to_proof_tactics());
                                        }
                                    }
                                    continue;
                                }
                                // A trailing `simp` after execution may have
                                // no contract work left (for example, a
                                // resource-only release whose `frame` already
                                // discharged every obligation).  Treat that as
                                // the empty Proof transition instead of
                                // constructing a legacy exit context solely to
                                // discover an empty pending set.
                                if claims.iter().enumerate().all(|(claim_index, claim)| {
                                    closures[claim_index].is_closed()
                                        || !matches!(claim, FunctionClaimRef::Ensure(_, _))
                                }) {
                                    continue;
                                }
                                // Grouped proofs forbid top-level existence
                                // tactics, so the direct path admits every
                                // grouped claim without them and every
                                // ungrouped claim; unsupported or failed
                                // claims fall back unchanged, and the
                                // attempt's memo footprint rolls back with
                                // it.
                                if let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
                                } = &outcome
                                {
                                    // Try the already-migrated proposition
                                    // vocabulary as one immutable Proof before
                                    // entering the legacy exit certificate
                                    // planner. This is deliberately all-or-
                                    // nothing: an unsupported claim discards
                                    // the untouched search descendant and the
                                    // established path retains its existing
                                    // behavior. Grouped proofs forbid top-level
                                    // existence tactics; ungrouped proofs apply
                                    // them inside the checked obligation scope.
                                    let mut direct_claims = Vec::new();
                                    // Ungrouped resource ensures close on the
                                    // direct path with the same bounded
                                    // production check and Assumption
                                    // certificate the legacy closer uses;
                                    // grouped sets stay legacy until the
                                    // grouped transition builder migrates.
                                    let mut direct_resource_claims = Vec::new();
                                    let mut direct_supported = true;
                                    for (claim_index, claim) in claims.iter().enumerate() {
                                        if closures[claim_index].is_closed() {
                                            continue;
                                        }
                                        match claim {
                                            FunctionClaimRef::Ensure(_, ensure_clause) => {
                                                match ensure_clause.ensure() {
                                                    Ensure::Proposition(surface_goal) => {
                                                        // A rewritten claim proves the
                                                        // original form with its
                                                        // recorded rewrites proof_candidate
                                                        // inside the checked scope.
                                                        direct_claims.push((
                                                            claim_index,
                                                            surface_goal.clone(),
                                                            rewrite_claim_equalities[claim_index]
                                                                .clone(),
                                                        ));
                                                    }
                                                    Ensure::Resource(resource) => {
                                                        direct_resource_claims
                                                            .push((claim_index, resource.clone()));
                                                    }
                                                }
                                            }
                                            _ => {
                                                direct_supported = false;
                                                break;
                                            }
                                        }
                                    }
                                    if direct_supported && !direct_resource_claims.is_empty() {
                                        let CFunctionOutcome::Return { .. } = &outcome else {
                                            unreachable!("gated on a return outcome above");
                                        };
                                        for (claim_index, resource) in &direct_resource_claims {
                                            let claim_label = function_claim_label(
                                                function_block.signature().name(),
                                                &claims[*claim_index],
                                            );
                                            if let Err(error) =
                                                crate::lang::click::checking::prove_ensure_resource(
                                                    &claim_label,
                                                    path_index,
                                                    &path.execution_facts(),
                                                    &path_requirements,
                                                    resource,
                                                    parsed_function.parameters(),
                                                    arguments,
                                                    pre_state,
                                                    &outcome,
                                                )
                                            {
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index} left `{claim_label}` unproved; use `simp()` after establishing the facts and resources it needs (claim index {claim_index})\nlast closing attempt:\n{}",
                                                    error.message()
                                                )));
                                            }
                                        }
                                    }
                                    if direct_supported
                                        && direct_claims.is_empty()
                                        && !direct_resource_claims.is_empty()
                                    {
                                        // A claim set of checked resource
                                        // productions needs no proof attempt:
                                        // its certificate is the same
                                        // Assumption-per-claim stream the
                                        // legacy certifier emits when it has
                                        // no proposition goals.
                                        let tactics = vec![
                                            ProofTactic::Assumption;
                                            direct_resource_claims.len()
                                        ];
                                        let certificate =
                                            ProofCertificate::from_proof_tactics(&tactics)
                                                .map_err(|error| {
                                                    ClickError::new(format!(
                                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: resource `simp` produced an invalid surface certificate: {error:?}"
                                                    ))
                                                })?;
                                        if proof_context.constants.grouped_contract {
                                            for (claim_index, _) in &direct_resource_claims {
                                                closures[*claim_index] =
                                                    ClaimClosure::by_grouped_transition(
                                                        &certificate,
                                                    );
                                            }
                                            path_grouped_surface_closers
                                                .extend(certificate.to_proof_tactics());
                                        } else {
                                            for (claim_index, _) in &direct_resource_claims {
                                                closures[*claim_index] =
                                                    ClaimClosure::by_checked_certificate(
                                                        &certificate,
                                                    );
                                            }
                                        }
                                        if capturing_this_tactic {
                                            path_deferred_capture_tactics
                                                .extend(certificate.to_proof_tactics());
                                        }
                                        continue;
                                    }
                                    if direct_supported && !direct_claims.is_empty() {
                                        let direct_certificate =
                                            crate::kernel::with_search_attempt_rollback(|| {
                                                let attempt = || -> Result<
                                                        Option<ProofCertificate>,
                                                        ClickError,
                                                    > {
                                        let transition_facts = path.execution_facts();
                                        // The evolving outcome proof supplies
                                        // the grouped obligation root when the
                                        // path derived a goal; its outcome proof data
                                        // carries the statement-entry anchor.
                                        let mut direct_proof = match (true, outcome_proof.as_ref())
                                        {
                                            (true, Some(evolving)) => {
                                                evolving.clone()
                                            }
                                            _ => Proof::for_fixed_state_frontier_with_premise_anchor(
                                                &proof_label,
                                                *tactic_index,
                                                &path_requirements,
                                                parsed_function.parameters(),
                                                arguments,
                                                pre_state,
                                                post_state,
                                                Some(result),
                                                proof_execution.surface_record.last_step_entry
                                                    .as_ref(),
                                                &proof_execution.recorded_snapshots,
                                                &outcome_surface_propositions,
                                                predicate_environment,
                                                click_function_environment,
                                                theorem_environment,
                                                &unfolded_predicates,
                                                &transition_facts,
                                            ),
                                        };
                                        // The grouped closure exports only
                                        // work after this checkpoint; earlier
                                        // drained tactics on an evolving root
                                        // are recorded by their own tactics.
                                        let direct_base = direct_proof.checkpoint();
                                        let mut direct_available = path_requirements.clone();
                                        let mut selected = true;
                                        // A top-level predicate outcome is opaque until the
                                        // corresponding checked `unfold` transition refines
                                        // this evolving outcome Proof. Smart `simp` tries
                                        // those named operations before opening its claim
                                        // scopes; a rejected unfold is only a candidate miss
                                        // and leaves the persistent root unchanged.
                                        let mut tried_predicates = BTreeSet::new();
                                        for (_, surface_goal, _) in &direct_claims {
                                            let ClickProposition::PredicateCall { name, .. } =
                                                surface_goal
                                            else {
                                                continue;
                                            };
                                            if !tried_predicates.insert(name.clone()) {
                                                continue;
                                            }
                                            if unfolded_predicates.contains(name) {
                                                continue;
                                            }
                                            match direct_proof.apply_step(
                                                ProofStep::UnfoldPredicate(name.clone()),
                                            ) {
                                                Ok(unfolded) => direct_proof = unfolded,
                                                Err(_) => {
                                                    check_verification_deadline()?;
                                                }
                                            }
                                        }
                                        for (_, surface_goal, equalities) in &direct_claims {
                                            // In a grouped set with resource
                                            // padding, retained provenance
                                            // already carries pre-execution
                                            // predicate unfolds. Write the
                                            // nested have at that structural
                                            // level: a have identical to the
                                            // current proposition claim would
                                            // close it early and shift the
                                            // trailing resource closers.
                                            let scope_surface_goal = if proof_context.constants.grouped_contract
                                                && !direct_resource_claims.is_empty()
                                            {
                                                unfold_structural_invariant_proposition(
                                                    predicate_environment,
                                                    surface_goal,
                                                    &unfolded_predicates,
                                                )
                                                .map_err(ClickError::new)?
                                            } else {
                                                surface_goal.clone()
                                            };
                                            let Ok(mut scope) =
                                                direct_proof.begin_have(scope_surface_goal)
                                            else {
                                                check_verification_deadline()?;
                                                selected = false;
                                                break;
                                            };
                                            let mut rewrites_applied = true;
                                            for equality in equalities {
                                                match scope.apply_step(ProofStep::Rewrite(
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
                                            let selected_scope = if let Some(scope) =
                                                scope.try_direct_logical_closure()?
                                            {
                                                Some(scope)
                                            } else {
                                                scope.try_simp_closure()?
                                            };
                                            let Some(scope) = selected_scope else {
                                                check_verification_deadline()?;
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
                                                let claim_label = function_claim_label(
                                                    function_block.signature().name(),
                                                    &claims[claim_index],
                                                );
                                                if let Err(error) = check_function_claim_by_simp(
                                                    &claim_label,
                                                    path_index,
                                                    &path.execution_facts(),
                                                    &direct_available,
                                                    &claims[claim_index],
                                                    parsed_function.parameters(),
                                                    arguments,
                                                    pre_state,
                                                    &outcome,
                                                    predicate_environment,
                                                    click_function_environment,
                                                    &proof_execution.recorded_snapshots,
                                                    &unfolded_predicates,
                                                ) {
                                                    return Err(error);
                                                }
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `simp` search did not retain a complete proof for `{claim_label}`",
                                                )));
                                            };
                                            let joined = scope.join()?;
                                            for fact in joined.added_facts() {
                                                if !direct_available.contains(fact) {
                                                    direct_available.push(fact.clone());
                                                }
                                            }
                                            direct_proof = joined;
                                        }
                                        if !selected {
                                            return Ok(None);
                                        }
                                        let mut surface_goals = Vec::new();
                                        for (_, goal, _) in &direct_claims {
                                            surface_goals.push(
                                                if proof_context.constants.grouped_contract
                                                    && !direct_resource_claims.is_empty()
                                                {
                                                    unfold_structural_invariant_proposition(
                                                        predicate_environment,
                                                        goal,
                                                        &unfolded_predicates,
                                                    )
                                                    .map_err(ClickError::new)?
                                                } else {
                                                    goal.clone()
                                                },
                                            );
                                        }
                                        let completed = if surface_goals.is_empty() {
                                            direct_proof.certificate_since(&direct_base)?
                                        } else {
                                            direct_proof.complete_fixed_state_obligations_since(
                                                &direct_base,
                                                &surface_goals,
                                            )?
                                        };
                                        Ok(Some(completed))
                                                    };
                                                let outcome = attempt();
                                                let keep = matches!(&outcome, Ok(Some(_)));
                                                (outcome, keep)
                                            })?;
                                        if let Some(certificate) = direct_certificate {
                                            if proof_context.constants.grouped_contract {
                                                // The grouped transition's tactic
                                                // stream closes claims in order;
                                                // checked resource productions
                                                // contribute one Assumption each,
                                                // exactly as the legacy certifier
                                                // pads its transition to the full
                                                // claim count.
                                                let certificate = if direct_resource_claims
                                                    .is_empty()
                                                {
                                                    certificate
                                                } else {
                                                    let mut tactics =
                                                        certificate.to_proof_tactics();
                                                    tactics.extend(std::iter::repeat_n(
                                                        ProofTactic::Assumption,
                                                        direct_resource_claims.len(),
                                                    ));
                                                    ProofCertificate::from_proof_tactics(&tactics)
                                                        .map_err(|error| {
                                                            ClickError::new(format!(
                                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: resource-padded grouped transition was invalid: {error:?}"
                                                            ))
                                                        })?
                                                };
                                                for (claim_index, _, _) in direct_claims {
                                                    closures[claim_index] =
                                                        ClaimClosure::by_grouped_transition(
                                                            &certificate,
                                                        );
                                                }
                                                for (claim_index, _) in &direct_resource_claims {
                                                    closures[*claim_index] =
                                                        ClaimClosure::by_grouped_transition(
                                                            &certificate,
                                                        );
                                                }
                                                path_grouped_surface_closers
                                                    .extend(certificate.to_proof_tactics());
                                                if capturing_this_tactic {
                                                    path_deferred_capture_tactics
                                                        .extend(certificate.to_proof_tactics());
                                                }
                                            } else {
                                                for (claim_index, _, _) in direct_claims {
                                                    closures[claim_index] =
                                                        ClaimClosure::by_checked_certificate(
                                                            &certificate,
                                                        );
                                                }
                                                // Resource productions were checked
                                                // before the attempt; their surface
                                                // certificate is the same trivial
                                                // Assumption the legacy closer
                                                // records — kernel certification
                                                // remains the resource authority.
                                                if !direct_resource_claims.is_empty() {
                                                    let assumption_certificate =
                                                        ProofCertificate::from_proof_tactics(&[
                                                            ProofTactic::Assumption,
                                                        ])
                                                        .map_err(|error| {
                                                            ClickError::new(format!(
                                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: resource `simp` produced an invalid surface certificate: {error:?}"
                                                            ))
                                                        })?;
                                                    for (claim_index, _) in &direct_resource_claims
                                                    {
                                                        closures[*claim_index] =
                                                            ClaimClosure::by_checked_certificate(
                                                                &assumption_certificate,
                                                            );
                                                    }
                                                }
                                                if capturing_this_tactic {
                                                    path_deferred_capture_tactics
                                                        .extend(certificate.to_proof_tactics());
                                                }
                                            }
                                            continue;
                                        }
                                    }
                                }
                                // A per-claim proof does not require every
                                // source tactic to be a closer. If retained
                                // `simp` contributes no checked transition,
                                // leave the claim open for the ordinary
                                // path-end check below. This is not an empty
                                // proof authority: no closure is recorded and
                                // no certificate is constructed. Grouped and
                                // explicitly closed contracts still require a
                                // complete retained transition here.
                                if !require_explicit_closers {
                                    continue;
                                }
                                // Preserve the authoritative semantic
                                // diagnostic when the claim itself is
                                // invalid. This is a read-only check, not a
                                // certificate fallback: a semantically valid
                                // claim still fails below unless the retained
                                // Proof transition was complete.
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let claim_label = function_claim_label(
                                        function_block.signature().name(),
                                        claim,
                                    );
                                    if let Err(error) = check_function_claim_by_simp(
                                        &claim_label,
                                        path_index,
                                        &path.execution_facts(),
                                        &path_requirements,
                                        claim,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        &outcome,
                                        predicate_environment,
                                        click_function_environment,
                                        &proof_execution.recorded_snapshots,
                                        &unfolded_predicates,
                                    ) {
                                        return Err(error);
                                    }
                                }
                                return Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `simp` did not retain a complete transition for every pending claim",
                                )));
                            }
                        }
                        if crate::instrumentation::deadline_exceeded() {
                            return Err(ClickError::new(format!(
                                "verification budget exhausted inside {}",
                                crate::instrumentation::deadline_context()
                            )));
                        }
                    }
                    drop(_post_execution_timing);
                    let _path_certification_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "path closure and theorem assembly",
                    );

                    if let CFunctionOutcome::Return {
                        value,
                        state: post_state,
                    } = &outcome
                    {
                        let mut lifetime_facts = path_requirements.clone();
                        lifetime_facts.extend(
                            path.execution_facts()
                                .iter()
                                .map(|fact| fact.proposition().clone()),
                        );
                        let lifetime_assumptions = assumptions_from_propositions(&lifetime_facts);
                        let mut lifetime_budget = ExecutionBudget::default();
                        match crate::kernel::unreturned_allocation_at_function_exit(
                    post_state,
                    value,
                    function,
                    arguments,
                    &lifetime_assumptions,
                    &mut lifetime_budget,
                )
                .map_err(|limit| {
                    ClickError::new(format!(
                        "`{proof_label}` path {path_index}: allocation-lifetime check exceeded its execution budget: {limit:?}"
                    ))
                })? {
                    Ok(Some(allocation)) => {
                        return Err(ClickError::new(format!(
                            "`{proof_label}` path {path_index}: runtime error: {}",
                            describe_runtime_error(
                                &crate::kernel::CRuntimeError::LiveAllocationLeak { allocation },
                                parsed_function.parameters(),
                                arguments,
                            )
                        )));
                    }
                    Err(error) => {
                        return Err(ClickError::new(format!(
                            "`{proof_label}` path {path_index}: runtime error: {}",
                            describe_runtime_error(
                                &error,
                                parsed_function.parameters(),
                                arguments,
                            )
                        )));
                    }
                    Ok(None) => {}
                }
                    }

                    if !require_explicit_closers
                        && let Some((claim_index, _, proof)) = existence_proof.take()
                    {
                        let proof = proof.with_outcome_snapshot(&outcome)?;
                        match proof.try_direct_logical_closure()? {
                            Some(completed) if completed.is_complete() => {
                                // The source's choose/witness steps are already
                                // retained in the path surface stream. The
                                // ordinary implicit closer contributes no
                                // additional syntax.
                                closures[claim_index] = ClaimClosure::by_exact_check();
                            }
                            _ => closures[claim_index].record_failure(
                                "the retained existential Proof did not close by the implicit exact check"
                                    .to_string(),
                            ),
                        }
                    }

                    if !require_explicit_closers {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            let result = check_function_claim(
                                &claim_label,
                                path_index,
                                &path.execution_facts(),
                                &path_requirements,
                                claim,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                &outcome,
                                predicate_environment,
                                click_function_environment,
                                &proof_execution.recorded_snapshots,
                                &unfolded_predicates,
                            );
                            match result {
                                Ok(()) => closures[claim_index] = ClaimClosure::by_exact_check(),
                                Err(error) => closures[claim_index]
                                    .record_failure(error.message().to_string()),
                            }
                        }
                    }

                    if let Some((claim_index, claim)) = claims
                        .iter()
                        .enumerate()
                        .find(|(claim_index, _)| !closures[*claim_index].is_closed())
                    {
                        let claim_label =
                            function_claim_label(function_block.signature().name(), claim);
                        let closer = match claim {
                            FunctionClaimRef::Effect(_, _) => "`frame()`",
                            FunctionClaimRef::Ensure(_, _) => "`simp()`",
                        };
                        let detail = closures[claim_index]
                            .last_error()
                            .map(|message| format!("\nlast closing attempt:\n{message}"))
                            .unwrap_or_default();
                        return Err(ClickError::new(format!(
                            "`{proof_label}` path {path_index} left `{claim_label}` unproved; use {closer} after establishing the facts and resources it needs (claim index {claim_index}){detail}"
                        )));
                    }

                    let (certified_path, specification_outcome, specification_requirements) =
                        if proof_execution.core.execution_abstraction {
                            (
                                certified_path.clone(),
                                certified_outcomes_by_group[certified_path_index.0]
                                    [certified_path_index.1]
                                    .clone(),
                                certification_facts.clone(),
                            )
                        } else {
                            let certified_outcome = &certified_outcomes_by_group
                                [certified_path_index.0][certified_path_index.1];
                            let outcome_delta = describe_function_outcome_delta(
                                &outcome,
                                certified_outcome,
                                parsed_function.parameters(),
                                arguments,
                            );
                            let certified_path = crate::instrumentation::measure_operation(
                    function_block.signature().name(),
                    &proof_label,
                    "resource representation check",
                    || certify_c_function_execution_path_resource_representation(
                            certified_path,
                            outcome.clone(),
                            &path.execution_facts(),
                        ),
                    )
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "execution proof for `{proof_label}` path {path_index} changed more than the certified ghost resource representation\n  {outcome_delta}"
                            ))
                        })?;
                            (certified_path, outcome.clone(), path_requirements.clone())
                        };
                    let specification = c_function_specification(
                        pre_state.clone(),
                        arguments.to_vec(),
                        specification_requirements,
                        specification_outcome,
                    );
                    let theorem = crate::instrumentation::measure_operation(
                function_block.signature().name(),
                &proof_label,
                "specification certification",
                || prove_c_function_satisfies_specification_from_symbolic_path(
                function.clone(),
                specification.clone(),
                &certified_path,
            ),
            )
            .ok_or_else(|| {
                let certified_outcome =
                    &certified_outcomes_by_group[certified_path_index.0][certified_path_index.1];
                let outcome_delta = describe_function_outcome_delta(
                    specification.outcome(),
                    certified_outcome,
                    parsed_function.parameters(),
                    arguments,
                );
                ClickError::new(format!(
                    "execution proof for `{proof_label}` path {path_index} does not certify its exact function specification\n  requirements: {}\n  {outcome_delta}",
                    specification.requires().len()
                ))
            })?;
                    for claim in claims {
                        verified.push(VerifiedCTheorem {
                            source_path: source_path.to_string(),
                            function_block: function_block.clone(),
                            claim: claim.verified_claim(),
                            proof_kind: ProofKind::TacticScript,
                            proof_tactics: Some(certificate_tactics.to_vec()),
                            expanded_proof: retained_surface.blocker.is_none().then(|| {
                                ProofCertificate::from_steps(retained_surface.steps.clone())
                            }),
                            expansion_blocker: retained_surface.blocker.clone(),
                            specification: specification.clone(),
                            theorem: theorem.clone(),
                            concrete_loop_execution: proof_execution.core.concrete_loop_execution,
                            frontier_loop_clauses: proof_execution.frontier_loop_clauses.to_vec(),
                            frontier_loop_rules: proof_execution.core.frontier_loop_rules.to_vec(),
                            checked_execution: certified_executions[certified_path_index.0].clone(),
                        });
                    }
                    // Expansion prints what verification holds: the tactics come out
                    // of the closure that accepted the claim, not from a parallel
                    // record that could disagree with it.
                    for (claim_index, closure) in closures.iter().enumerate() {
                        surface_closers_by_claim[claim_index].push(
                            closure
                                .closed()
                                .map(ClosedClaim::claim_tactics)
                                .unwrap_or_default()
                                .to_vec(),
                        );
                    }
                    surface_grouped_closers_by_path.push(path_grouped_surface_closers);
                    surface_post_tactics_by_path.push(path_surface_post_tactics);
                    let implicitly_closable = path_deferred_capture_tactics.is_empty()
                        || (!require_explicit_closers
                            && claims.iter().all(|claim| match claim {
                                FunctionClaimRef::Ensure(_, ensure_clause)
                                    if matches!(ensure_clause.ensure(), Ensure::Proposition(_)) =>
                                {
                                    check_function_claim(
                                        &function_claim_label(
                                            function_block.signature().name(),
                                            claim,
                                        ),
                                        path_index,
                                        &path.execution_facts(),
                                        &path_requirements,
                                        claim,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        &outcome,
                                        predicate_environment,
                                        click_function_environment,
                                        &proof_execution.recorded_snapshots,
                                        &unfolded_predicates,
                                    )
                                    .is_ok()
                                }
                                _ => true,
                            }));
                    implicit_closure_by_path.push(implicitly_closable);
                    deferred_capture_tactics_by_path.push(path_deferred_capture_tactics);
                    deferred_capture_branches_by_path.push(deferred_capture_branch_path);
                    drop(_path_certification_timing);
                }
                Ok(())
            },
        )?;
        // A context that recorded a proof-branch choice appends its
        // post-execution tactics as a flat suffix after the choice point,
        // where cross-context synthesis will place the surface `if`.
        // Appending them by execution-branch leaf would graft one case's
        // closers onto execution paths the case excluded.
        let append_surface_tactics =
            |steps: &mut Vec<ProofStep>, path_tactics: &[Vec<ProofTactic>]| -> Result<(), String> {
                if retained_surface.path_choices.is_empty() {
                    append_surface_tactics_by_leaf(steps, path_tactics)
                } else {
                    append_surface_tactics_flat(steps, path_tactics)
                }
            };
        if proof_context.constants.grouped_contract {
            let mut expanded = retained_surface.clone();
            if surface_post_tactics_by_path
                .iter()
                .any(|tactics| !tactics.is_empty())
                && let Err(message) =
                    append_surface_tactics(&mut expanded.steps, &surface_post_tactics_by_path)
            {
                expanded.block(message);
            }
            if surface_grouped_closers_by_path
                .iter()
                .any(|tactics| !tactics.is_empty())
                && let Err(message) =
                    append_surface_tactics(&mut expanded.steps, &surface_grouped_closers_by_path)
            {
                expanded.block(message);
            }
            for theorem in &mut verified {
                theorem.expanded_proof = expanded
                    .blocker
                    .is_none()
                    .then(|| ProofCertificate::from_steps(expanded.steps.clone()));
                theorem.expansion_blocker = expanded.blocker.clone();
            }
            // Surface synthesis follows proof contexts, not the number of
            // semantic execution paths they contribute. A proof branch can
            // be vacuous after certified-path filtering while its checked
            // surface arm is still required to check the surrounding `if`.
            // Record exactly one builder per declared claim for this context;
            // tying builders to produced theorems silently dropped such arms
            // (and duplicated builders when a context certified many paths).
            for claim in claims {
                claim_surface_builders.push((claim.verified_claim(), expanded.clone()));
            }
        } else {
            for (claim_index, claim) in claims.iter().enumerate() {
                let mut expanded = retained_surface.clone();
                if surface_post_tactics_by_path
                    .iter()
                    .any(|tactics| !tactics.is_empty())
                    && let Err(message) =
                        append_surface_tactics(&mut expanded.steps, &surface_post_tactics_by_path)
                {
                    expanded.block(message);
                }
                if surface_closers_by_claim[claim_index]
                    .iter()
                    .any(|tactics| !tactics.is_empty())
                    && let Err(message) = append_surface_tactics(
                        &mut expanded.steps,
                        &surface_closers_by_claim[claim_index],
                    )
                {
                    expanded.block(message);
                }
                let verified_claim = claim.verified_claim();
                for theorem in &mut verified {
                    if theorem.claim == verified_claim {
                        theorem.expanded_proof = expanded
                            .blocker
                            .is_none()
                            .then(|| ProofCertificate::from_steps(expanded.steps.clone()));
                        theorem.expansion_blocker = expanded.blocker.clone();
                    }
                }
                claim_surface_builders.push((verified_claim, expanded));
            }
        }
        if tactic_expansion_capture_is_active(expansion_capture.as_deref()) {
            let Some(deferred) = proof_execution.expansion.deferred_tactic_capture.as_ref() else {
                // Structured proofs produce one check context per logical
                // case.  A selected deferred tactic activates the expansion
                // capture while those contexts are being built, but contexts
                // from sibling branches legitimately have no capture.  Let
                // them finish; the matching context records the expansion,
                // or the expansion entry reports that no result was seen.
                return Ok(verified);
            };
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
                    .all(|pair| pair[0] == pair[1])
                && deferred_capture_branches_by_path
                    .iter()
                    .all(Option::is_none);
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
                        .all(Option::is_none)
                    && implicit_closure_by_path.iter().all(|closable| *closable));
            if !contributes_no_tactics && path_independent_capture {
                // No path can decide the enclosing branch skeleton — the
                // tactic ran after the branches completed — and every path
                // produced the same expansion; it stands on its own and must
                // not be wrapped in that skeleton.
                match ProofCertificate::from_proof_tactics(&deferred_capture_tactics_by_path[0]) {
                    Ok(proof) => capture.steps = proof.steps().to_vec(),
                    Err(error) => capture.block(format!(
                        "deferred expansion produced a non-simple proof: {error:?}"
                    )),
                }
            } else if !contributes_no_tactics {
                let mut capture_tactics = deferred.branch_skeleton.clone();
                for (branch_path, path_tactics) in deferred_capture_branches_by_path
                    .iter()
                    .zip(&deferred_capture_tactics_by_path)
                {
                    let appended = match branch_path {
                        Some(branch_path) => append_surface_tactics_at_branch_path(
                            &mut capture_tactics,
                            branch_path,
                            path_tactics,
                        ),
                        None => {
                            append_surface_tactics_at_every_leaf(&mut capture_tactics, path_tactics)
                        }
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
                            "deferred expansion produced a non-simple proof: {error:?}"
                        )),
                    }
                }
            }
            finish_tactic_expansion_capture(
                expansion_capture.as_deref_mut(),
                &capture,
                contributes_no_tactics,
            );
        }
        Ok(verified)
    })();
    result.map_err(|error| add_proof_branch_path(error, branch_path))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inconsistent_context_is_not_sibling_path_evidence() {
        let left = Bitvector32Term::Variable(Variable(1));
        let right = Bitvector32Term::Variable(Variable(2));
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(left.clone()),
                    Box::new(right.clone()),
                ),
                true,
            ))
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(right), Box::new(left)),
                true,
            ));
        let unrelated = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(2))),
                Box::new(Bitvector32Term::Constant(10)),
            ),
            true,
        );

        assert_eq!(proof_case_fact_conflicts(&unrelated, &assumptions), Err(()));
    }

    #[test]
    fn consistent_exact_conflict_remains_sibling_path_evidence() {
        let condition = ConditionTerm::Bitvector32SignedLessThan(
            Box::new(Bitvector32Term::Variable(Variable(1))),
            Box::new(Bitvector32Term::Constant(10)),
        );
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::ConditionIs(condition.clone(), false));
        let fact = Proposition::ConditionIs(condition, true);

        assert_eq!(proof_case_fact_conflicts(&fact, &assumptions), Ok(true));
    }
}
