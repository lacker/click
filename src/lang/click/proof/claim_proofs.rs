use super::*;
use crate::kernel::apply_c_function_contract_resource_transition;
use std::sync::Arc;

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
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty explicit proof script"
        )));
    }
    let program = build_internal_proof_with_source(tactics, claim_label, tactic_source)?;
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
    let mut replay = TacticReplayState {
        proof_site: proof_site_for_claims(function_block, &proof_claims, false),
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        ordered_finalization: true,
        execution_start_facts: Arc::new(pure_facts.clone()),
        function_entry_state: Some(function_entry_state),
        surface_propositions,
        ..TacticReplayState::default()
    };
    record_current_statement_entry(
        &mut replay,
        &state,
        function_block,
        &function,
        &arguments,
        claim_label,
        0,
        "proof entry",
    )?;
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path: PersistentSequence::default(),
        },
        expansion_capture.as_deref_mut(),
        function_block,
        parsed_function,
        &proof_claims,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    )?;

    finish_ordered_proof_contexts(
        expansion_capture,
        contexts,
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
    )
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
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
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
    let program = build_internal_proof_with_source(tactics, &proof_label, tactic_source)?;
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
    let mut replay = TacticReplayState {
        proof_site: proof_site_for_claims(function_block, claims, true),
        source_layout: SourceExecutionLayout::new(parsed_function.body()),
        ordered_finalization: true,
        grouped_contract: true,
        execution_start_facts: Arc::new(pure_facts.clone()),
        function_entry_state: Some(function_entry_state),
        surface_propositions,
        ..TacticReplayState::default()
    };
    record_current_statement_entry(
        &mut replay,
        &state,
        function_block,
        &function,
        &arguments,
        &proof_label,
        0,
        "proof entry",
    )?;
    let contexts = crate::instrumentation::measure_operation(
        function_block.signature().name(),
        &proof_label,
        "grouped proof tactic replay",
        || {
            execute_internal_proof(
                &program,
                ProofReplayContext {
                    state,
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                expansion_capture.as_deref_mut(),
                function_block,
                parsed_function,
                claims,
                &proof_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                &function,
                &arguments,
            )
        },
    )?;

    crate::instrumentation::measure_operation(
        function_block.signature().name(),
        &proof_label,
        "grouped proof finishing",
        || {
            finish_ordered_proof_contexts(
                expansion_capture,
                contexts,
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
            )
        },
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn prove_claims_by_grouped_auto(
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

    let mut verified = prove_claims_by_grouped_tactics(
        expansion_capture.as_deref_mut(),
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
    certify_grouped_claims_result(
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
        &mut verified,
        "auto",
        &tactics,
    )?;
    Ok(verified)
}

/// An explicit grouped proof script, followed by the whole-contract
/// certificate gate: the script's stitched certificate must exist and replay
/// completely before the grouped claims are accepted.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn prove_claims_by_grouped_script(
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
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut verified = prove_claims_by_grouped_tactics(
        expansion_capture.as_deref_mut(),
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
    certify_grouped_claims_result(
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
        &mut verified,
        "explicit proof script",
        tactics,
    )?;
    Ok(verified)
}

/// The grouped form of the whole-claim certificate gate (see
/// `certify_claim_result`): the stitched contract-level certificate must
/// exist, replay completely, and reproduce the verified theorem count. When
/// the replayed tactics are themselves a simple proof, that proof is the
/// certificate by definition and the replay that just succeeded was the
/// certificate replay.
#[allow(clippy::too_many_arguments)]
fn certify_grouped_claims_result(
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
    verified: &mut [VerifiedCTheorem],
    proof_description: &str,
    replayed_tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    if let Ok(script) = ProofCertificate::from_proof_tactics(replayed_tactics) {
        for theorem in verified.iter_mut() {
            theorem.expanded_proof = Some(script.clone());
            theorem.expansion_blocker = None;
        }
        return Ok(());
    }
    let certificate = crate::instrumentation::measure_operation(
        function_block.signature().name(),
        &format!("{}.contract", function_block.signature().name()),
        "whole-contract certificate construction",
        || {
            verified
                .first()
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{proof_description}` proved no grouped claims for `{}.contract`",
                        function_block.signature().name()
                    ))
                })?
                .expanded_proof_certificate()
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{proof_description}` succeeded internally for `{}.contract` without a whole-contract surface certificate: {}",
                        function_block.signature().name(),
                        error.message()
                    ))
                })
        },
    )?;
    let certificate_tactics = certificate.to_proof_tactics();
    if certificate_tactics.is_empty() {
        return Err(ClickError::new(format!(
            "`{proof_description}` stitched an empty whole-contract surface certificate for `{}.contract`",
            function_block.signature().name()
        )));
    }
    let replayed = crate::instrumentation::measure_operation(
        function_block.signature().name(),
        &format!("{}.contract", function_block.signature().name()),
        "whole-contract certificate replay",
        || {
            prove_claims_by_grouped_tactics(
                expansion_capture.as_deref_mut(),
                source_path,
                function_block,
                parsed_function,
                claims,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                &certificate_tactics,
                ProofTacticSource::GeneratedBy { source_index: 0 },
            )
        },
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{proof_description}` surface certificate failed complete replay for `{}.contract`:\n{}\n{}",
            function_block.signature().name(),
            format_proof_certificate(&certificate),
            error.message()
        ))
    })?;
    // The certificate may legitimately refine an abstracted join into its
    // concrete paths, so the check is claim coverage: every verified claim
    // must be proved again by the certificate replay.
    for theorem in verified.iter() {
        if !replayed
            .iter()
            .any(|replayed| replayed.claim == theorem.claim)
        {
            return Err(ClickError::new(format!(
                "`{proof_description}` surface certificate replay did not prove every grouped claim of `{}.contract` again",
                function_block.signature().name()
            )));
        }
    }
    Ok(())
}

/// Exit-claim closure: the structural form of the settled invariant that a
/// smart success must replay through a surface-expressible certificate
/// before acceptance.
///
/// Mid-execution the invariant is already structural — a smart step can only
/// continue from the replay context `complete_smart_tactic` returns, and there is
/// no other way to obtain one, so "accepted without a certificate" is not
/// spellable. At function exit the per-claim drain used to spell it easily:
/// closure was `closed_claims[i] = true`, a bool any site could set, with the
/// certificates hanging off parallel arrays and the gate re-asserted by hand
/// at every closing site.
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
        /// implicit closer of a single-claim proof. Where the script spelled
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
        /// terminal output of the checked point-obligation Proof operation or
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

    /// What running the exit `simp` closer on one claim produced.
    pub(super) enum ExitSimpClosure {
        /// The claim closed, carrying the certificate that discharged it.
        Closed(ClaimClosure),
        /// The claim joins the path's grouped transition, which is certified
        /// and replayed as one unit once every claim has been offered. The
        /// goal is `None` for a resource ensure: it has no proposition to
        /// certify and is discharged by one of the transition's trailing
        /// `assumption`s.
        JoinsGroupedTransition(Option<GroupedOutcomeSimpGoal>),
    }

    /// What the exit drain holds when it reaches its `simp` closer.
    ///
    /// Gathered into one value so the closer can be a function instead of an
    /// inline block, which is what lets `ClosedClaim`'s certificate
    /// constructor be private to it.
    pub(super) struct ExitClaimContext<'a> {
        pub(super) replay: &'a TacticReplayState,
        pub(super) outcome_surface_propositions: &'a SurfacePropositionMap,
        pub(super) path_requirements: &'a [Proposition],
        pub(super) surface_certificate_facts: &'a [Proposition],
        pub(super) execution_facts: &'a [ExecutionPureFact],
        pub(super) unfolded_predicates: &'a [String],
        pub(super) existence_tactics: &'a [ProofTactic],
        pub(super) parameters: &'a [syntax::C0Parameter],
        pub(super) arguments: &'a [CExpression],
        pub(super) pre_state: &'a CState,
        pub(super) outcome: &'a CFunctionOutcome,
        pub(super) predicate_environment: &'a PredicateEnvironment,
        pub(super) click_function_environment: &'a ClickFunctionEnvironment,
        pub(super) theorem_environment: &'a TheoremEnvironment,
        pub(super) function_requires: &'a [Requirement],
        pub(super) path_index: usize,
        pub(super) tactic_index: usize,
    }

    impl ExitClaimContext<'_> {
        /// Lower a claim's surface goal under the drain's unfold set.
        fn lower_claim_goal(&self, surface_goal: &ClickProposition) -> Result<Proposition, String> {
            lower_ensure_proposition_goal(
                self.path_requirements,
                surface_goal,
                self.parameters,
                self.arguments,
                self.pre_state,
                self.outcome,
                self.predicate_environment,
                self.click_function_environment,
                &self.replay.program_point_states,
                self.unfolded_predicates,
            )
        }

        /// The fact set a per-claim exit certificate is generated against.
        ///
        /// `surface_certificate_facts` is the drain's running certificate
        /// context. The ambient effect facts (`CMemoryMutatesOnly` /
        /// `CMemoryEffectSummary`) join it because the closer replays with
        /// them in scope, and the drain's `unfold(...)` set is applied because
        /// the emitted `have` script carries that prefix: generation must plan
        /// against exactly the context replay will hold. The grouped
        /// transition emits no `unfold(...)` prefix and so plans against the
        /// raw snapshot instead.
        fn certificate_facts(&self) -> Result<Vec<Proposition>, String> {
            let mut certificate_facts = self.surface_certificate_facts.to_vec();
            certificate_facts.extend(
                self.execution_facts
                    .iter()
                    .filter(|fact| {
                        matches!(
                            fact.proposition(),
                            Proposition::CMemoryMutatesOnly { .. }
                                | Proposition::CMemoryEffectSummary { .. }
                                | Proposition::CHeapLifetimeRetired { .. }
                        )
                    })
                    .map(|fact| fact.proposition().clone()),
            );
            unfold_available_predicate_facts(
                self.predicate_environment,
                self.click_function_environment,
                self.unfolded_predicates,
                &certificate_facts,
            )
        }

        /// The replay state a per-claim exit certificate is generated in.
        fn certificate_replay(&self) -> TacticReplayState {
            let mut certificate_replay = self.replay.clone();
            certificate_replay.surface_propositions = self.outcome_surface_propositions.clone();
            // The goal was proved with the drain's unfold set active; the
            // certificate must re-lower the surface goal under the same
            // unfolds or the two spellings cannot match.
            certificate_replay.unfolded_predicates = self.unfolded_predicates.to_vec().into();
            certificate_replay
        }

        fn certificate_failure(&self, claim_label: &str, message: &str) -> ClickError {
            ClickError::new(format!(
                "`{claim_label}` path {}: smart `simp` closed the claim but its certificate did not lower or replay: {message}",
                self.path_index
            ))
        }
    }

    /// Discharge one exit claim whose ambient `simp` check just succeeded.
    ///
    /// This is the only place a claim can acquire a generated certificate.
    /// Every arm either returns a closure built from a certificate the
    /// generator already replayed, hands the claim to the path's grouped
    /// transition — which certifies and replays before anything closes — or
    /// fails verification. There is no arm that accepts without one, which is
    /// what makes the exit gate structural instead of a check to remember.
    pub(super) fn discharge_exit_simp_claim(
        context: &ExitClaimContext<'_>,
        claim_index: usize,
        claim_label: &str,
        ensure: &Ensure,
        rewritten_goal: Option<&Proposition>,
        frame_certified_goal: Option<&Proposition>,
    ) -> Result<ExitSimpClosure, ClickError> {
        let outcome = context.outcome;
        if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
            let certificate = ProofCertificate::from_proof_tactics(&[ProofTactic::Normalize])
                .map_err(|error| {
                    context.certificate_failure(
                        claim_label,
                        &format!("divergence produced an invalid normalize certificate: {error:?}"),
                    )
                })?;
            return Ok(ExitSimpClosure::Closed(
                ClaimClosure::by_checked_certificate(&certificate),
            ));
        }
        if !context.existence_tactics.is_empty() {
            let certificate = match (rewritten_goal, ensure, outcome) {
                (
                    None,
                    Ensure::Proposition(surface_goal),
                    CFunctionOutcome::Return {
                        value: result,
                        state: post_state,
                    },
                ) if !context.replay.grouped_contract => {
                    context.lower_claim_goal(surface_goal).and_then(|goal| {
                        let certificate_facts = context.certificate_facts()?;
                        certify_outcome_existential_simp(
                            &context.certificate_replay(),
                            surface_goal,
                            &goal,
                            &certificate_facts,
                            context.existence_tactics,
                            context.parameters,
                            context.arguments,
                            context.pre_state,
                            post_state,
                            result,
                            context.predicate_environment,
                            context.click_function_environment,
                            context.theorem_environment,
                            context.function_requires,
                            claim_label,
                            context.tactic_index,
                            context.path_index,
                        )
                        .map_err(|error| error.message().to_string())
                    })
                }
                _ => Err(
                    "surface `simp` lowering with existential tactics requires an ungrouped proposition return goal"
                        .to_string(),
                ),
            }
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {}: smart `simp` closed the claim with existential tactics, but its certificate did not lower or replay: {message}",
                    context.path_index
                ))
            })?;
            return Ok(ExitSimpClosure::Closed(
                ClaimClosure::by_checked_certificate(&certificate),
            ));
        }

        if context.replay.grouped_contract {
            // The grouped transition certificate is the proof-producing
            // authority for the whole claim set. The ambient check only
            // decides that this claim joins the transition; it closes once
            // that certificate has been built and replayed.
            return match (rewritten_goal, ensure, outcome) {
                (None, Ensure::Proposition(surface_goal), CFunctionOutcome::Return { .. }) => {
                    let goal = match frame_certified_goal {
                        Some(goal) => goal.clone(),
                        None => context.lower_claim_goal(surface_goal).map_err(|message| {
                            context.certificate_failure(claim_label, &message)
                        })?,
                    };
                    Ok(ExitSimpClosure::JoinsGroupedTransition(Some(
                        GroupedOutcomeSimpGoal {
                            claim_index,
                            claim_label: claim_label.to_string(),
                            surface_goal: surface_goal.clone(),
                            goal,
                        },
                    )))
                }
                (None, Ensure::Resource(_), _) => Ok(ExitSimpClosure::JoinsGroupedTransition(None)),
                (Some(_), _, _) => Err(context.certificate_failure(
                    claim_label,
                    "surface lowering after `rewrite` is not implemented",
                )),
                _ => Err(context.certificate_failure(
                    claim_label,
                    "surface `simp` lowering requires a proposition return goal",
                )),
            };
        }

        let certificate = match (rewritten_goal, ensure, outcome) {
            (
                None,
                Ensure::Proposition(surface_goal),
                CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                },
            ) => frame_certified_goal
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| context.lower_claim_goal(surface_goal))
                .and_then(|goal| {
                    let certificate_facts = context.certificate_facts()?;
                    certify_outcome_simp(
                        &context.certificate_replay(),
                        surface_goal,
                        &goal,
                        &certificate_facts,
                        context.parameters,
                        context.arguments,
                        context.pre_state,
                        post_state,
                        result,
                        context.predicate_environment,
                        context.click_function_environment,
                        context.theorem_environment,
                        context.function_requires,
                        claim_label,
                        context.tactic_index,
                        context.path_index,
                    )
                    .map_err(|error| error.message().to_string())
                }),
            (None, Ensure::Resource(_), _) => {
                ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption]).map_err(|error| {
                    format!("resource `simp` produced an invalid surface certificate: {error:?}")
                })
            }
            (Some(_), _, _) => {
                Err("surface lowering after `rewrite` is not implemented".to_string())
            }
            _ => Err("surface `simp` lowering requires a proposition return goal".to_string()),
        }
        .map_err(|message| context.certificate_failure(claim_label, &message))?;
        Ok(ExitSimpClosure::Closed(
            ClaimClosure::by_checked_certificate(&certificate),
        ))
    }
}

use exit_claim::{ClaimClosure, ClosedClaim, ExitClaimContext, ExitSimpClosure};

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

#[allow(clippy::too_many_arguments)]
/// Debug net for the drain's write-through invariant: between legacy
/// mutations, the evolving outcome goal's fact context must contain the
/// legacy working set. The goal may legitimately carry more — the transport
/// and `have` imports add checked store equations and memory-effect
/// summaries the legacy vector never held.
#[cfg(debug_assertions)]
fn assert_outcome_sync(
    proof: &Proof<'_>,
    requirements: &[Proposition],
    proof_label: &str,
    path_index: usize,
) {
    let goal_facts = proof
        .available_fact_vector()
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>();
    let legacy = requirements
        .iter()
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
    if !goal_facts.is_superset(&legacy) {
        let only_legacy = legacy.difference(&goal_facts).take(3).collect::<Vec<_>>();
        panic!(
            "`{proof_label}` path {path_index}: the outcome goal is missing drain working-set \
             facts: {only_legacy:?}"
        );
    }
}

pub(super) fn finish_ordered_proof_replay(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    context: ProofReplayContext,
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
    // typed outcome goals own each returning path's result, state, and fact
    // context. At this boundary the function frame has already been consumed
    // into deferred checked authority, so the reconstructed frontier carries
    // no effect selection. A context that is not at a returning function
    // exit derives no goals and drains through the legacy path unchanged.
    // Derivation is unconditional: every result-aware tactic kind consumes
    // goals now, and the working-set parity invariant below must hold for
    // every drain before the legacy vector retires.
    let outcome_substrate = {
        Proof::for_execution_frontier_with_effect_goals(
            &proof_label,
            0,
            ProofReplayContext {
                state: context.state.clone(),
                pure_facts: context.pure_facts.clone(),
                replay: context.replay.clone(),
                branch_path: context.branch_path.clone(),
            },
            EffectGoalSelection::None,
            function_block,
            function,
            parsed_function,
            arguments,
            function_environment,
            resource_environment,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        )
        .focus_function_outcomes(Arc::new(
            context.pure_facts[..function_block
                .requires()
                .len()
                .min(context.pure_facts.len())]
                .to_vec(),
        ))
        .ok()
    };
    let ProofReplayContext {
        state,
        pure_facts,
        replay,
        branch_path,
    } = context;
    let pre_state = replay.execution_start_state(&state);
    let frontier_function_block = (!replay.frontier_loop_clauses.is_empty()).then(|| {
        function_block.with_bound_frontier_loop_clauses(&replay.frontier_loop_clauses.to_vec())
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
    let frontier_function_environment = (!replay.frontier_loop_rules.is_empty()).then(|| {
        function_environment
            .clone()
            .with_verified_loop_rules(replay.frontier_loop_rules.to_vec())
    });
    let function = frontier_function.as_ref().unwrap_or(function);
    let function_environment = frontier_function_environment
        .as_ref()
        .unwrap_or(function_environment);
    let result = (|| {
        let execution = replay.execution().ok_or_else(|| {
            ClickError::new(format!(
                "`{proof_label}` execution proof must reach function exit with `step()`, `execute()`, or `execute()`"
            ))
        })?;
        if execution.paths().is_empty() {
            return Err(ClickError::new(format!(
                "execution proof could not prove any complete execution path for `{proof_label}`"
            )));
        }
        let mut certification_facts = replay.execution_start_facts.as_ref().clone();
        certification_facts.extend(
            replay
                .function_entry_execution_prerequisites
                .iter()
                .cloned(),
        );
        certification_facts.extend(
            replay
                .case_assumptions
                .iter()
                .filter(|case| case.at_function_entry)
                .filter_map(|case| case.fact.clone()),
        );
        // Frontier-local loop clauses are bound after the initial claim
        // context is built.  Their phase proofs can unfold predicates just
        // like legacy structural clauses, so fresh whole-function
        // certification must expose those definitions at function entry as
        // well.  Otherwise proof replay can initialize an invariant from an
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
        let certified_execution = crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &proof_label,
            "independent kernel certification",
            || {
                if replay.frontier_loop_rules.is_empty()
                    && let Some((_, _, _, execution)) = certification_cache.iter().find(
                        |(facts, cached_state, concrete_loop_execution, _)| {
                            facts == &certification_facts
                                && cached_state == pre_state
                                && *concrete_loop_execution == replay.concrete_loop_execution
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
                        replay.concrete_loop_execution,
                        || {
                            prove_checked_c_function_execution_with_environment(
                                pre_state.clone(),
                                function.clone(),
                                arguments.to_vec(),
                                execution_start_assumptions.clone(),
                                function_environment.clone(),
                                if replay.concrete_loop_execution
                                    || !replay.frontier_loop_rules.is_empty()
                                {
                                    CExecutionSemantics::APPLY_VERIFIED_RULES
                                } else {
                                    CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS
                                },
                                if replay.concrete_loop_execution {
                                    CFunctionContractExecutionMode::ExecuteLoops
                                } else {
                                    CFunctionContractExecutionMode::VerifyLoops
                                },
                            )
                        },
                    );
                    if replay.frontier_loop_rules.is_empty() {
                        certification_cache.push((
                            certification_facts.clone(),
                            pre_state.clone(),
                            replay.concrete_loop_execution,
                            execution.clone(),
                        ));
                    }
                    execution
                }
            },
        );
        let certified_execution = checked_c_function_execution_with_entry_derivations(
            certified_execution,
            replay.function_entry_derivations.to_vec(),
            replay.function_entry_execution_prerequisites.to_vec(),
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
        let replay_outcomes = execution
            .paths()
            .iter()
            .map(|path| path.outcome().clone())
            .collect::<Vec<_>>();
        let outcomes_match = |replayed: &crate::kernel::CFunctionExecutionCandidate,
                              certified_index: usize| {
            let certified = &certified_outcomes[certified_index];
            let certified_path = &certified_execution.paths()[certified_index];
            let certified_facts = certified_path
                .execution_facts()
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let replayed_facts = replayed
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
            let replayed_path_conditions = replayed_facts
                .iter()
                .chain(
                    replayed
                        .obligations()
                        .iter()
                        .map(ProofObligation::proposition),
                )
                .collect::<Vec<_>>();
            if certified_path_conditions.into_iter().any(|certified_fact| {
                replayed_path_conditions.iter().any(|replayed_fact| {
                    propositions_are_exact_negations(certified_fact, replayed_fact)
                })
            }) {
                return false;
            }
            // A proof-level branch can select an execution path even when a
            // simple statement certificate deliberately omitted the C branch
            // guard from its own fact list. Include that selected branch when
            // pairing the replay candidate with an independently certified
            // path, or a recursive return known to equal zero can be paired
            // with the unrelated base-case path merely because their final
            // observable values coincide.
            if !replay.case_assumptions.is_empty() {
                let CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                } = replayed.outcome()
                else {
                    return false;
                };
                let mut replayed_available = pure_facts.clone();
                replayed_available.extend(
                    replayed
                        .facts()
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                for case in &replay.case_assumptions {
                    let case_fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let Ok(condition) = lower_outcome_proposition_with_program_points(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replayed_available,
                            &case.condition,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
                        ) else {
                            return false;
                        };
                        if case.value {
                            condition
                        } else {
                            Proposition::Not(Box::new(condition))
                        }
                    };
                    if replayed_path_conditions.iter().any(|replayed_fact| {
                        propositions_are_exact_negations(replayed_fact, &case_fact)
                    }) {
                        // The replay execution still contains every C path;
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
            for fact in replayed_facts {
                path_assumptions = path_assumptions.assume_proposition(fact);
            }
            for equation in crate::kernel::certified_store_equations(&replayed.execution_facts())
                .into_iter()
                .chain(crate::kernel::certified_store_equations(
                    &certified_path.execution_facts(),
                ))
            {
                path_assumptions = path_assumptions.assume_proposition(equation);
            }
            if let CFunctionOutcome::Return { state, .. } = certified
                && let Ok(resource_facts) = state.resources().observable_facts(&path_assumptions)
            {
                for fact in resource_facts {
                    path_assumptions = path_assumptions.assume_proposition(fact);
                }
            }
            c_function_outcomes_program_state_definitionally_equal(
                replayed.outcome(),
                certified,
                &path_assumptions,
            ) || c_function_outcomes_program_state_equal_by_execution_provenance(
                replayed.outcome(),
                &replayed.execution_facts(),
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
            |replayed: &crate::kernel::CFunctionExecutionCandidate| -> Result<bool, ClickError> {
                if replay.case_assumptions.is_empty() {
                    return Ok(false);
                }
                let CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                } = replayed.outcome()
                else {
                    return Ok(false);
                };
                let mut available = pure_facts.clone();
                available.extend(
                    replayed
                        .facts()
                        .iter()
                        .map(|fact| fact.proposition().clone()),
                );
                for case in &replay.case_assumptions {
                    let fact = if let Some(fact) = &case.fact {
                        fact.clone()
                    } else {
                        let Ok(condition) = lower_outcome_proposition_with_program_points(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &available,
                            &case.condition,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
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
                                "execution replay for `{proof_label}` cannot attribute a path to a sibling proof branch: the routed assumptions are already inconsistent"
                            )));
                        }
                    }
                    available.push(fact);
                }
                Ok(false)
            };
        let certified_path_for_replay = crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &proof_label,
            "certified outcome pairing",
            || -> Result<Option<Vec<Option<usize>>>, ClickError> {
                if replay.execution_abstraction {
                    return Ok((!certified_outcomes.is_empty())
                        .then(|| vec![Some(0); execution.paths().len()]));
                }
                let mut pairing = Vec::with_capacity(execution.paths().len());
                for replayed in execution.paths() {
                    if let Some(certified_index) = (0..certified_outcomes.len())
                        .find(|certified_index| outcomes_match(replayed, *certified_index))
                    {
                        pairing.push(Some(certified_index));
                    } else if path_excluded_by_proof_branch(replayed)? {
                        pairing.push(None);
                    } else {
                        return Ok(None);
                    }
                }
                Ok(Some(pairing))
            },
        )?;
        let Some(certified_path_for_replay) = certified_path_for_replay else {
            // Outcome equality is a conservative kernel query: once the
            // ambient limit fires it returns `false`, which used to turn a
            // valid replay into a ghost-region or memory mismatch. Give the
            // limit priority over the semantic pairing diagnostic.
            check_verification_deadline()?;
            return Err(ClickError::new(format!(
                "execution replay for `{proof_label}` contains a path not reproduced by kernel certification\n  replay: {replay_outcomes:?}\n  certified: {certified_outcomes:?}"
            )));
        };
        let mut verified = Vec::new();
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_grouped_closers_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_branches_by_path = Vec::with_capacity(execution.paths().len());

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
                    let Some(certified_path_index) = certified_path_for_replay[path_index] else {
                        // This context's proof-branch case set excludes the path; a
                        // sibling context certifies it.
                        continue 'execution_path;
                    };
                    let certified_path = &certified_execution.paths()[certified_path_index];
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
                    // The parity invariant the drain migration consumes: the
                    // typed outcome goal's fact context equals this path's
                    // legacy working set (as a set — the persistent context
                    // deduplicates exact repeats the vector retains).
                    #[cfg(debug_assertions)]
                    if let Some((substrate, _)) = &outcome_substrate
                        && let Some(goal) = substrate.outcome_goal_for_path(path_index)
                    {
                        let focused = substrate
                            .focus(goal)
                            .expect("a derived outcome goal is open");
                        let goal_facts = focused
                            .available_fact_vector()
                            .into_iter()
                            .collect::<std::collections::BTreeSet<_>>();
                        let legacy_facts = path_requirements
                            .iter()
                            .cloned()
                            .collect::<std::collections::BTreeSet<_>>();
                        debug_assert!(
                            goal_facts == legacy_facts,
                            "`{proof_label}` path {path_index}: outcome goal facts diverged from the drain working set"
                        );
                    }

                    let _case_routing_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "proof case path routing",
                    );
                    if !replay.case_assumptions.is_empty() {
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
                        for case in &replay.case_assumptions {
                            let case_lowering_timing = crate::instrumentation::OperationTiming::new(
                                function_block.signature().name(),
                                &proof_label,
                                "proof case condition lowering",
                            );
                            let fact = if let Some(fact) = &case.fact {
                                fact.clone()
                            } else {
                                let condition = lower_outcome_proposition_with_program_points(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &path_requirements,
                            &case.condition,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
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
                                    // certifies this path; replaying this branch's exact
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
                        replay.deferred_tactic_capture.as_ref()
                    {
                        match &outcome {
                            CFunctionOutcome::Return {
                                value: result,
                                state: post_state,
                            } => surface_branch_path_for_outcome(
                                &deferred.branch_skeleton,
                                &path_requirements,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &replay.program_point_states,
                                predicate_environment,
                                click_function_environment,
                            )
                            // A post-join path carries no pre-join guard facts and
                            // cannot decide the pre-join surface branches; its tactic
                            // is path-independent. A genuinely misaligned placement
                            // still fails: every-leaf appending rejects conflicting
                            // leaves and the whole-claim gate replays the result.
                            .ok(),
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
                    let mut unfolded_predicates = replay.unfolded_predicates.clone();
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
                        mut existence_tactics,
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
                                Vec::<ProofTactic>::new(),
                                path_requirements.clone(),
                                replay.surface_propositions.clone(),
                            )
                        },
                    );
                    // Facts established after execution all describe this fixed
                    // outcome snapshot. Keep them separately so `fold` can reuse an
                    // exact lowering without accidentally selecting the same surface
                    // spelling from an earlier program point.
                    let mut current_outcome_surface_propositions = SurfacePropositionMap::default();
                    // This path's evolving result-aware proof: tactic kinds
                    // that have migrated onto the outcome goal advance this
                    // one lineage and retain their checked steps directly.
                    // One authoritative import of the prepared working set
                    // happens here; the tactic loop then writes through the
                    // goal, and only a legacy vector mutation re-imports.
                    // Transport and `have` keep their own imports because
                    // theirs are semantic supersets, not drift repairs.
                    let mut outcome_proof =
                        outcome_substrate.as_ref().and_then(|(substrate, _)| {
                            let goal = substrate.outcome_goal_for_path(path_index)?;
                            let focused = substrate.focus(goal).ok()?;
                            focused.with_drained_outcome_facts(&path_requirements).ok()
                        });
                    // Set by any arm that mutates the legacy working set
                    // without writing through the outcome goal; the end of
                    // the iteration re-imports once.
                    let mut working_set_dirty = false;
                    drop(_path_preparation_timing);
                    let _post_execution_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "post-execution claim tactics",
                    );
                    for (post_execution_index, deferred) in
                        replay.post_execution_tactics.iter().enumerate()
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
                                            statement_index: replay.frontier.next_statement_index,
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
                                statement_index: replay.frontier.next_statement_index,
                            };
                            push_timing_tactic(timing_context.clone());
                            TacticTiming {
                                claim_label: proof_label.clone(),
                                tactic_index: *tactic_index,
                                source_index: *source_index,
                                tactic_name: tactic_name.to_string(),
                                tactic_class,
                                statement_index: replay.frontier.next_statement_index,
                                start: std::time::Instant::now(),
                                context: timing_context,
                            }
                        });
                        match post_tactic {
                            PostExecutionTactic::Fold(resource) => {
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
                                    ResourceBodyClosure::Initialize,
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
                                // A legacy resource transition rewrote the
                                // working set; re-import immediately so the
                                // outcome goal stays authoritative.
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving.with_drained_outcome_facts(&path_requirements)?,
                                    );
                                }
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    replay.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::FoldResource(resource.clone()),
                                );
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
                                // A legacy resource transition rewrote the
                                // working set; re-import immediately so the
                                // outcome goal stays authoritative.
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving.with_drained_outcome_facts(&path_requirements)?,
                                    );
                                }
                            }
                            PostExecutionTactic::UnfoldPredicate(name) => {
                                let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
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
                                    #[cfg(debug_assertions)]
                                    assert_outcome_sync(
                                        &evolving,
                                        &path_requirements,
                                        &proof_label,
                                        path_index,
                                    );
                                    let before = evolving.checkpoint();
                                    let unfolded = evolving.apply_step(
                                        SimpleProofStep::UnfoldPredicate(name.clone()),
                                    )?;
                                    let added_facts = unfolded.added_facts().to_vec();
                                    let certificate = unfolded.certificate_since(&before)?;
                                    outcome_proof = Some(unfolded);
                                    (added_facts, certificate)
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy point root.
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
                                        replay.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Apply(application) => {
                                let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
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
                                    #[cfg(debug_assertions)]
                                    assert_outcome_sync(
                                        &evolving,
                                        &path_requirements,
                                        &proof_label,
                                        path_index,
                                    );
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
                                    // deleted legacy point root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
                                // The retained `apply using` step is prefixed to every
                                // claim certificate, so independent replay holds the
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
                                        replay.deferred_tactic_capture.as_ref(),
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
                                    value: result,
                                    state: post_state,
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
                                    #[cfg(debug_assertions)]
                                    assert_outcome_sync(
                                        &evolving,
                                        &path_requirements,
                                        &proof_label,
                                        path_index,
                                    );
                                    let applied = evolving.apply_step(
                                        SimpleProofStep::ApplyTheoremUsing {
                                            application: application.clone(),
                                            premises: premises.clone(),
                                        },
                                    )?;
                                    let added_facts = applied.added_facts().to_vec();
                                    outcome_proof = Some(applied);
                                    added_facts
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy point root.
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
                                    replay.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::ApplyTheoremUsing {
                                        application: application.clone(),
                                        premises: premises.clone(),
                                    },
                                );
                            }
                            PostExecutionTactic::Have(have) => {
                                let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
                                } = &outcome
                                else {
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
                                            for fact in &replay.effect_facts {
                                                if matches!(
                                                    fact.proposition(),
                                                    Proposition::CMemoryMutatesOnly { .. }
                                                        | Proposition::CMemoryEffectSummary { .. }
                                                        | Proposition::CHeapLifetimeRetired { .. }
                                                ) && !available.contains(fact.proposition())
                                                {
                                                    available.push(fact.proposition().clone());
                                                }
                                            }
                                            for equation in crate::kernel::certified_store_equations(
                                                &replay.effect_facts,
                                            ) {
                                                if !available.contains(&equation) {
                                                    available.push(equation);
                                                }
                                            }
                                            for fact in
                                                crate::kernel::certified_store_loadability_facts(
                                                    &replay.effect_facts,
                                                )
                                            {
                                                if !available.contains(&fact) {
                                                    available.push(fact);
                                                }
                                            }
                                            available
                                        },
                                    );
                                // Post-execution proof certificates replay against
                                // the same kernel-certified loadability consequences
                                // of stores that were available while planning them.
                                // Restricting these facts to hand-written `derive`
                                // scripts let smart `simp` search succeed and then
                                // fail when its generated certificate was replayed.
                                // The migrated path first: the `have` scope
                                // opens on this path's evolving outcome
                                // proof, its body searches through the shared
                                // scope drivers, and a miss restores the
                                // untouched evolving proof for the legacy
                                // checker.
                                let evolving_have = if let Some(evolving) = outcome_proof.take() {
                                    let attempt = (|| -> Result<
                                        Option<(Proof<'_>, Proposition, ProofCertificate)>,
                                        ClickError,
                                    > {
                                        let resynced = evolving
                                            .with_drained_outcome_facts(&certificate_available)?;
                                        let before = resynced.checkpoint();
                                        let Ok(scope) =
                                            resynced.begin_have(have.proposition.clone())
                                        else {
                                            return Ok(None);
                                        };
                                        let selected = match &have.proof {
                                            SourceProof::Default
                                            | SourceProof::Tactic(
                                                SmartTactic::Auto | SmartTactic::Simp,
                                            ) => scope.try_simp_closure()?,
                                            SourceProof::Script(tactics) => {
                                                scope.try_linear_smart_script(tactics)?
                                            }
                                            SourceProof::Tactic(SmartTactic::Frame) => None,
                                        };
                                        let Some(closed) = selected else {
                                            return Ok(None);
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
                                } else {
                                    None
                                };
                                if evolving_have.is_none() {
                                    working_set_dirty = true;
                                }
                                let checked_smart_have = if evolving_have.is_some() {
                                    evolving_have
                                } else if Proof::supports_linear_smart_source(&have.proof) {
                                    checked_have_with_proof(
                                        have,
                                        theorem_environment,
                                        &proof_label,
                                        *tactic_index,
                                        &certificate_available,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        replay.proof_certificate_builder.last_step_entry.as_ref(),
                                        &replay,
                                        &outcome_surface_propositions,
                                        predicate_environment,
                                        click_function_environment,
                                        function_block.requires(),
                                        function_block.requirement_label_indices(),
                                    )?
                                } else {
                                    None
                                };
                                let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                                let (surface_have, fact) = if let Some((fact, Some(certificate))) =
                                    checked_smart_have
                                {
                                    let tactics = certificate.to_proof_tactics();
                                    let [surface_have] = tactics.as_slice() else {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: checked smart `have` did not retain one `have` certificate"
                                        )));
                                    };
                                    (surface_have.clone(), fact)
                                } else if let Some(smart_unfolds) = smart_unfolds {
                                    let fact = lower_outcome_proposition_with_program_points(
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &certificate_available,
                                &have.proposition,
                                predicate_environment,
                                click_function_environment,
                                &replay.program_point_states,
                            )
                            .or_else(|_| {
                                lower_outcome_proposition_with_memory_resolution(
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    post_state,
                                    result,
                                    &certificate_available,
                                    &have.proposition,
                                    predicate_environment,
                                    click_function_environment,
                                    &replay.program_point_states,
                                )
                            })
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: could not lower smart `have` goal: {message}"
                                ))
                            })?;
                                    let planning_available = unfold_available_predicate_facts(
                                predicate_environment,
                                click_function_environment,
                                &smart_unfolds,
                                &path_requirements,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: could not unfold smart `have` context: {message}"
                                ))
                            })?;
                                    let unfolded_goal = unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                &smart_unfolds,
                                &fact,
                                &assumptions_from_propositions(&planning_available),
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: could not unfold smart `have` goal: {message}"
                                ))
                            })?;
                                    let surface_goal = if smart_unfolds.is_empty() {
                                        have.proposition.clone()
                                    } else {
                                        unfold_structural_invariant_proposition(
                                    predicate_environment,
                                    &have.proposition,
                                    &smart_unfolds,
                                )
                                .map_err(|message| {
                                    ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: could not express unfolded smart `have` goal: {message}"
                                    ))
                                })?
                                    };
                                    let mut certificate_replay = replay.clone();
                                    // This replay validates a certificate nested under
                                    // the selected post-execution tactic. Its local
                                    // tactic indices restart at zero and must not be
                                    // mistaken for the outer selected tactic's index.
                                    certificate_replay.deferred_tactic_capture = None;
                                    certificate_replay.surface_propositions =
                                        outcome_surface_propositions.clone();
                                    let restricted_simp_surfaces = match &have.proof {
                                        SourceProof::Script(tactics) => {
                                            tactics.last().and_then(|tactic| match tactic {
                                                ProofTactic::SimpUsing(simp) => {
                                                    Some(&simp.premises)
                                                }
                                                _ => None,
                                            })
                                        }
                                        _ => None,
                                    };
                                    let restricted_simp_pairs = restricted_simp_surfaces
                                .map(|surfaces| {
                                    surfaces
                                        .iter()
                                        .map(|surface| {
                                        certificate_replay
                                            .surface_propositions
                                            .available_kernel(surface, &certificate_available)
                                            .cloned()
                                            .map(Ok::<_, String>)
                                            .unwrap_or_else(|| {
                                                    lower_outcome_proposition_with_program_points(
                                                    parsed_function.parameters(),
                                                    arguments,
                                                    pre_state,
                                                    post_state,
                                                    result,
                                                    &certificate_available,
                                                    surface,
                                                    predicate_environment,
                                                    click_function_environment,
                                                    &replay.program_point_states,
                                                )
                                            })
                                            .and_then(|kernel| {
                                                // A premise spelled at another
                                                // program point carries other
                                                // snapshots in its load atoms;
                                                // the snapshot bridge decides
                                                // the pair with candidates
                                                // drawn only from the
                                                // certified context.
                                                (certificate_available.iter().any(|available| {
                                                    available == &kernel
                                                        || condition_polarity_equivalent(
                                                            available, &kernel,
                                                        )
                                                }) || snapshot_bridged_fact_is_available(
                                                    &kernel,
                                                    &certificate_available,
                                                    &[],
                                                )
                                                    // A separation premise is
                                                    // served by the compact
                                                    // carrier projection, not
                                                    // by a materialized pair
                                                    // proposition; ask the
                                                    // prover directly.
                                                    || matches!(
                                                        kernel,
                                                        Proposition::CResourceSeparate { .. }
                                                    ) && assumptions_from_propositions(
                                                        &certificate_available,
                                                    )
                                                    .proves(&kernel))
                                                .then_some((kernel, surface.clone()))
                                                .ok_or_else(|| {
                                                    format!(
                                                        "post-execution `simp() using` premise is not in the certified proof context: {}",
                                                        describe_click_proposition(surface)
                                                    )
                                                })
                                            })
                                        })
                                        .collect::<Result<Vec<_>, String>>()
                                })
                            .transpose()
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: {message}"
                                ))
                                })?;
                                    let is_restricted_simp = restricted_simp_pairs.is_some();
                                    let certificate_planning_available = restricted_simp_pairs
                                        .as_ref()
                                        .map(|pairs| {
                                            pairs
                                                .iter()
                                                .map(|(kernel, _)| kernel.clone())
                                                .collect::<Vec<_>>()
                                        })
                                        .unwrap_or_else(|| planning_available.clone());
                                    let compatibility_timing =
                                        crate::instrumentation::OperationTiming::new(
                                            function_block.signature().name(),
                                            &proof_label,
                                            "post-execution smart have compatibility construction",
                                        );
                                    let closing_tactics = if let Some(pairs) = &restricted_simp_pairs {
                                plan_restricted_simp_expansion(
                                    &unfolded_goal,
                                    Some(&surface_goal),
                                    pairs,
                                )
                            } else {
                                // Route through the structural certificate
                                // constructor so a conjunction goal splits
                                // into per-conjunct `have` certificates
                                // closed by `split()`, exactly as the other
                                // outcome `simp` sites construct it.
                                lower_outcome_simp_proof(
                                    &certificate_replay,
                                    &surface_goal,
                                    &unfolded_goal,
                                    &certificate_planning_available,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    post_state,
                                    result,
                                    predicate_environment,
                                    click_function_environment,
                                )
                                .and_then(|proof| match proof {
                                    SourceProof::Script(tactics) => Ok(tactics),
                                    _ => Err(ClickError::new(
                                        "smart `have` closer produced a non-script certificate",
                                    )),
                                })
                            }
                            .map_err(|error| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `have` failed: {}",
                                    error.message()
                                ))
                                })?;
                                    drop(compatibility_timing);
                                    let mut proof_tactics = smart_unfolds
                                        .iter()
                                        .cloned()
                                        .map(ProofTactic::UnfoldPredicate)
                                        .collect::<Vec<_>>();
                                    proof_tactics.extend(closing_tactics.iter().cloned());
                                    let surface_have = ProofHave {
                                        proposition: have.proposition.clone(),
                                        proof: SourceProof::Script(proof_tactics),
                                    };
                                    let replay_available = certificate_available.clone();
                                    let replay_have = |candidate: &ProofHave| {
                                        prove_pure_proposition_at_point(
                                            &candidate.proposition,
                                            Some(&fact),
                                            &candidate.proof,
                                            "have",
                                            theorem_environment,
                                            &proof_label,
                                            *tactic_index,
                                            &replay_available,
                                            &replay.effect_facts,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            post_state,
                                            Some(result),
                                            &replay.program_point_states,
                                            Some(&certificate_replay.surface_propositions),
                                            predicate_environment,
                                            click_function_environment,
                                            function_block.requires(),
                                            Some(path_index),
                                        )
                                    };
                                    let (surface_have, replayed_fact) = match replay_have(
                                        &surface_have,
                                    ) {
                                        Ok(replayed_fact) => (surface_have, replayed_fact),
                                        Err(initial_error) => {
                                            let failed_tactic = ProofTactic::Have(surface_have);
                                            let failed_certificate =
                                                ProofCertificate::from_proof_tactics(
                                                    std::slice::from_ref(&failed_tactic),
                                                )
                                                .expect("smart have must lower to simple tactics");
                                            let kind = if is_restricted_simp {
                                                "`simp() using`"
                                            } else {
                                                "post-execution smart `have`"
                                            };
                                            return Err(ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: {kind} explicit certificate failed replay:\n{}\n{}",
                                                format_proof_certificate(&failed_certificate),
                                                initial_error.message(),
                                            )));
                                        }
                                    };
                                    if replayed_fact != fact {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: smart `have` surface certificate replayed a different fact"
                                        )));
                                    }
                                    (ProofTactic::Have(surface_have), replayed_fact)
                                } else {
                                    // A script that validates as a certificate is its
                                    // own certificate: `prove_have_at_point` is
                                    // deterministic replay of surface tactics, which
                                    // is exactly what the gate requires.
                                    // `validate_certificate_tactics` is the settled
                                    // judgment for "surface-expressible" and already
                                    // descends through nested `have`/`if`
                                    // bodies, so use it rather than a flat scan that
                                    // mistakes any structured script for a smart one.
                                    //
                                    // Replay runs first so a script rejected on its
                                    // own terms still reports that, and the
                                    // expressibility gate only decides whether a
                                    // *successful* smart closure may stand.
                                    let replay_have = |available: &[Proposition]| {
                                        let prelowered_goal = current_outcome_surface_propositions
                                            .available_kernel(&have.proposition, available);
                                        prove_pure_proposition_at_point(
                                            &have.proposition,
                                            prelowered_goal,
                                            &have.proof,
                                            "have",
                                            theorem_environment,
                                            &proof_label,
                                            *tactic_index,
                                            available,
                                            &replay.effect_facts,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            post_state,
                                            Some(result),
                                            &replay.program_point_states,
                                            Some(&outcome_surface_propositions),
                                            predicate_environment,
                                            click_function_environment,
                                            function_block.requires(),
                                            Some(path_index),
                                        )
                                    };
                                    let have_replay_operation = format!(
                                        "post-execution simple have replay (source tactic {tactic_index}: {})",
                                        describe_click_proposition(&have.proposition),
                                    );
                                    let fact = crate::instrumentation::measure_operation(
                                        function_block.signature().name(),
                                        &proof_label,
                                        &have_replay_operation,
                                        || match replay_have(&certificate_available) {
                                            Ok(fact) => Ok(fact),
                                            Err(error) => {
                                                if !error
                                                    .message()
                                                    .contains("missing pure fact: loadable(")
                                                {
                                                    return Err(error);
                                                }
                                                let mut loadable_available =
                                                    certificate_available.clone();
                                                for fact in
                                                    crate::kernel::certified_store_loadability_facts(
                                                        &replay.effect_facts,
                                                    )
                                                {
                                                    if !loadable_available.contains(&fact) {
                                                        loadable_available.push(fact);
                                                    }
                                                }
                                                if loadable_available == certificate_available {
                                                    return Err(error);
                                                }
                                                replay_have(&loadable_available)
                                            }
                                        },
                                    )?;
                                    let mut surface_tactic = ProofTactic::Have(have.clone());
                                    if let Err(error) = ProofCertificate::from_proof_tactics(
                                        std::slice::from_ref(&surface_tactic),
                                    ) {
                                        match lower_smart_simp_suffix_have(
                                            have,
                                            &fact,
                                            theorem_environment,
                                            &proof_label,
                                            *tactic_index,
                                            &path_requirements,
                                            &replay.effect_facts,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            post_state,
                                            result,
                                            &replay.program_point_states,
                                            Some(&outcome_surface_propositions),
                                            predicate_environment,
                                            click_function_environment,
                                            function_block.requires(),
                                            path_index,
                                        ) {
                                            Some(lowered) => {
                                                surface_tactic = ProofTactic::Have(lowered);
                                            }
                                            None => {
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: post-execution `have` script is not expressible as a certificate: {error:?}"
                                                )));
                                            }
                                        }
                                    }
                                    (surface_tactic, fact)
                                };
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
                                    replay.deferred_tactic_capture.as_ref(),
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
                                let candidates = if premises.is_none() {
                                    Some(fact_transport_candidates_at_outcome(
                                        &transport_available,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        result,
                                        &replay,
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
                                        .with_drained_outcome_facts(&transport_available)?;
                                    let before = resynced.checkpoint();
                                    let transported = if let Some(premises) = premises {
                                        resynced.apply_step(SimpleProofStep::TransportUsing {
                                            source: source.clone(),
                                            target: target.clone(),
                                            premises: premises.clone(),
                                        })?
                                    } else {
                                        resynced.search_point_fact_transport(
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
                                    // deleted legacy point root.
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
                                        replay.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Choose(choice) => {
                                existence_tactics.push(ProofTactic::Choose(choice.clone()));
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    replay.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::Choose(choice.clone()),
                                );
                            }
                            PostExecutionTactic::Witness(witness) => {
                                existence_tactics.push(ProofTactic::Witness(witness.clone()));
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    replay.deferred_tactic_capture.as_ref(),
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
                                let point_root = match (outcome_proof.as_ref(), &outcome) {
                                    (Some(evolving), _) => {
                                        #[cfg(debug_assertions)]
                                        assert_outcome_sync(
                                            evolving,
                                            &path_requirements,
                                            &proof_label,
                                            path_index,
                                        );
                                        Some(evolving.clone())
                                    }
                                    (
                                        None,
                                        CFunctionOutcome::Return {
                                            value: result,
                                            state: post_state,
                                        },
                                    ) => Some(Proof::for_point_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &replay.program_point_states,
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
                                            &replay.program_point_states,
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
                                    let Some(point_root) = &point_root else {
                                        continue;
                                    };
                                    match point_root
                                        .focus_point_goal(goal)?
                                        .apply_step(SimpleProofStep::Assumption)
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
                                        replay.deferred_tactic_capture.as_ref(),
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
                                let point_root = match (outcome_proof.as_ref(), &outcome) {
                                    (Some(evolving), _) => {
                                        #[cfg(debug_assertions)]
                                        assert_outcome_sync(
                                            evolving,
                                            &path_requirements,
                                            &proof_label,
                                            path_index,
                                        );
                                        Some(evolving.clone())
                                    }
                                    (
                                        None,
                                        CFunctionOutcome::Return {
                                            value: result,
                                            state: post_state,
                                        },
                                    ) => Some(Proof::for_point_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &replay.program_point_states,
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
                                            &replay.program_point_states,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` could not lower goal: {message}"
                                            ))
                                        })?,
                                    };
                                    let Some(point_root) = &point_root else {
                                        continue;
                                    };
                                    match point_root
                                        .focus_point_goal(goal)?
                                        .apply_step(SimpleProofStep::Normalize)
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
                                        replay.deferred_tactic_capture.as_ref(),
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
                                let point_root = match outcome_proof.as_ref() {
                                    Some(evolving) => {
                                        #[cfg(debug_assertions)]
                                        assert_outcome_sync(
                                            evolving,
                                            &path_requirements,
                                            &proof_label,
                                            path_index,
                                        );
                                        evolving.clone()
                                    }
                                    None => Proof::for_point_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &replay.program_point_states,
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
                                            &replay.program_point_states,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` could not lower goal: {message}"
                                            ))
                                        })?,
                                    };
                                    match point_root.focus_point_goal(goal)?.apply_step(
                                        SimpleProofStep::Rewrite(surface_equality.clone()),
                                    ) {
                                        Ok(proof) => {
                                            let rewritten = proof.goal().cloned().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked `rewrite` lost its proposition goal"
                                                ))
                                            })?;
                                            retained_certificate
                                                .get_or_insert_with(|| proof.certificate());
                                            rewritten_claim_goals[claim_index] = Some(rewritten);
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
                                        replay.deferred_tactic_capture.as_ref(),
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
                                    &replay.program_point_states,
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
                                // The certified region-frame goal entered the
                                // working set; re-import immediately so the
                                // outcome goal stays authoritative.
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving.with_drained_outcome_facts(&path_requirements)?,
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
                                if closed_effect {
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
                                }
                                // The ambient frame checks against every available
                                // fact; its replayable surface spelling is exactly
                                // `frame()`. Spelling out one snapshot's surface facts
                                // here produced a premise list replay could not
                                // re-establish.
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    replay.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::FrameUsing {
                                        region: None,
                                        premises: Vec::new(),
                                    },
                                );
                            }
                            PostExecutionTactic::FrameUsing { region, premises } => {
                                let CFunctionOutcome::Return {
                                    value: result,
                                    state: post_state,
                                } = &outcome
                                else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `frame using` requires a return outcome"
                                    )));
                                };
                                // Ordered finalization initially visits every exit
                                // tactic before any of them changes the certified
                                // outcome context. Re-lower explicit frame premises
                                // here, at their actual deferred position, so a fact
                                // established by a preceding `have` keeps that
                                // current-outcome meaning instead of the spelling's
                                // obsolete pre-`have` lowering.
                                let facts = crate::instrumentation::measure_operation(
                                    function_block.signature().name(),
                                    &proof_label,
                                    "frame premise lowering and validation",
                                    || -> Result<Vec<Proposition>, ClickError> {
                                        let indexed_requirements =
                                            ExactReplayFactIndex::new(&path_requirements);
                                        let mut facts = Vec::with_capacity(premises.len());
                                        for premise in premises {
                                            let fact = current_outcome_surface_propositions
                                                .available_kernel_matching(premise, |kernel| {
                                                    indexed_requirements.contains_exact(kernel)
                                                })
                                                .or_else(|| {
                                                    outcome_surface_propositions
                                                        .available_kernel_matching(
                                                            premise,
                                                            |kernel| {
                                                                indexed_requirements
                                                                    .contains_exact(kernel)
                                                            },
                                                        )
                                                })
                                                .cloned()
                                                .map(Ok)
                                                .unwrap_or_else(|| {
                                                    lower_outcome_proposition_with_program_points(
                                                        parsed_function.parameters(),
                                                        arguments,
                                                        pre_state,
                                                        post_state,
                                                        result,
                                                        &path_requirements,
                                                        premise,
                                                        predicate_environment,
                                                        click_function_environment,
                                                        &replay.program_point_states,
                                                    )
                                                    .or_else(|_| {
                                                        lower_outcome_proposition_with_memory_resolution(
                                                            parsed_function.parameters(),
                                                            arguments,
                                                            pre_state,
                                                            post_state,
                                                            result,
                                                            &path_requirements,
                                                            premise,
                                                            predicate_environment,
                                                            click_function_environment,
                                                            &replay.program_point_states,
                                                        )
                                                    })
                                                })
                                                .map_err(|message| {
                                                    ClickError::new(format!(
                                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: could not lower `frame using` premise `{}`: {message}",
                                                        describe_click_proposition(premise)
                                                    ))
                                                })?;
                                            facts.push(fact);
                                        }
                                        for (premise_index, fact) in facts.iter().enumerate() {
                                            if !indexed_requirements.contains(fact)
                                                && !exact_fact_is_available(
                                                    fact,
                                                    &path_requirements,
                                                )
                                                && materialization_equivalent_available_fact(
                                                    fact,
                                                    &path_requirements,
                                                )
                                                .is_none()
                                            {
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `frame using` requires an exact premise that has not been established: {}{}",
                                                    describe_pure_fact(
                                                        fact,
                                                        parsed_function.parameters(),
                                                        arguments,
                                                    ),
                                                    premises
                                                        .get(premise_index)
                                                        .map(|surface| format!(
                                                            "\n  surface premise: {}",
                                                            describe_click_proposition(surface)
                                                        ))
                                                        .unwrap_or_default(),
                                                )));
                                            }
                                        }
                                        Ok(facts)
                                    },
                                )?;
                                let mut closed_effect = false;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                        continue;
                                    }
                                    let claim_label = function_claim_label(
                                        function_block.signature().name(),
                                        claim,
                                    );
                                    crate::instrumentation::measure_operation(
                                        function_block.signature().name(),
                                        &proof_label,
                                        "frame exact effect check",
                                        || {
                                            check_effect_claim_exact(
                                                &claim_label,
                                                path_index,
                                                &path.execution_facts(),
                                                &facts,
                                                claim,
                                                parsed_function.parameters(),
                                                arguments,
                                                pre_state,
                                                &outcome,
                                            )
                                        },
                                    )?;
                                    closures[claim_index] = ClaimClosure::by_exact_check();
                                    closed_effect = true;
                                }
                                if closed_effect {
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
                                }
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    replay.deferred_tactic_capture.as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::FrameUsing {
                                        region: region.clone(),
                                        premises: premises.clone(),
                                    },
                                );
                            }
                            PostExecutionTactic::CheckedFrameUsing {
                                authority,
                                region,
                                premises,
                                surface_certificate,
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
                                if let Some(certificate) = surface_certificate {
                                    for tactic in certificate.to_proof_tactics() {
                                        record_post_execution_surface_tactic(
                                            deferred.surface_recorded,
                                            &mut path_surface_post_tactics,
                                            &mut path_deferred_capture_tactics,
                                            replay.deferred_tactic_capture.as_ref(),
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
                                        replay.deferred_tactic_capture.as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        ProofTactic::FrameUsing {
                                            region: region.clone(),
                                            premises: premises.clone(),
                                        },
                                    );
                                }
                            }
                            PostExecutionTactic::Simp => {
                                // The legacy exit planner behind the direct
                                // path may mutate the working set; re-import
                                // at the end of the iteration.
                                working_set_dirty = true;
                                let capturing_this_tactic = replay
                                    .deferred_tactic_capture
                                    .as_ref()
                                    .is_some_and(|capture| capture.tactic_index == *tactic_index);
                                if ((replay.grouped_contract && existence_tactics.is_empty())
                                    || (!replay.grouped_contract && !existence_tactics.is_empty()))
                                    && let CFunctionOutcome::Return {
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
                                    let mut direct_supported = true;
                                    for (claim_index, claim) in claims.iter().enumerate() {
                                        if closures[claim_index].is_closed() {
                                            continue;
                                        }
                                        match claim {
                                            FunctionClaimRef::Ensure(_, ensure_clause)
                                                if rewritten_claim_goals[claim_index].is_none()
                                                    && frame_certified_claim_goals[claim_index]
                                                        .is_none() =>
                                            {
                                                match ensure_clause.ensure() {
                                                    Ensure::Proposition(surface_goal) => {
                                                        direct_claims.push((
                                                            claim_index,
                                                            surface_goal.clone(),
                                                        ));
                                                    }
                                                    Ensure::Resource(_) => {
                                                        direct_supported = false;
                                                        break;
                                                    }
                                                }
                                            }
                                            _ => {
                                                direct_supported = false;
                                                break;
                                            }
                                        }
                                    }
                                    let existence_candidate = if existence_tactics.is_empty() {
                                        None
                                    } else {
                                        match ProofCertificate::from_proof_tactics(
                                            &existence_tactics,
                                        ) {
                                            Ok(candidate) => Some(candidate),
                                            Err(_) => {
                                                direct_supported = false;
                                                None
                                            }
                                        }
                                    };
                                    if direct_supported && !direct_claims.is_empty() {
                                        let transition_facts = path.execution_facts();
                                        // The evolving outcome proof supplies
                                        // the grouped obligation root when the
                                        // path derived a goal; its point data
                                        // carries the statement-entry anchor.
                                        let mut direct_proof = match (true, outcome_proof.as_ref())
                                        {
                                            (true, Some(evolving)) => {
                                                #[cfg(debug_assertions)]
                                                assert_outcome_sync(
                                                    evolving,
                                                    &path_requirements,
                                                    &proof_label,
                                                    path_index,
                                                );
                                                evolving.clone()
                                            }
                                            _ => Proof::for_point_frontier_with_premise_anchor(
                                                &proof_label,
                                                *tactic_index,
                                                &path_requirements,
                                                parsed_function.parameters(),
                                                arguments,
                                                pre_state,
                                                post_state,
                                                Some(result),
                                                replay
                                                    .proof_certificate_builder
                                                    .last_step_entry
                                                    .as_ref(),
                                                &replay.program_point_states,
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
                                        for (_, surface_goal) in &direct_claims {
                                            let Ok(scope) =
                                                direct_proof.begin_have(surface_goal.clone())
                                            else {
                                                check_verification_deadline()?;
                                                selected = false;
                                                break;
                                            };
                                            let scope =
                                                if let Some(candidate) = &existence_candidate {
                                                    // Re-record the active
                                                    // unfolds inside the scope:
                                                    // the retained body must
                                                    // verify independently of
                                                    // the enclosing goal's
                                                    // inherited unfold delta.
                                                    let mut scope = scope;
                                                    for name in &unfolded_predicates {
                                                        match scope.apply_step(
                                                            SimpleProofStep::UnfoldPredicate(
                                                                name.clone(),
                                                            ),
                                                        ) {
                                                            Ok(next) => scope = next,
                                                            Err(_) => {
                                                                check_verification_deadline()?;
                                                            }
                                                        }
                                                    }
                                                    let Ok(scope) = scope
                                                        .apply_candidate_certificate(candidate)
                                                    else {
                                                        check_verification_deadline()?;
                                                        selected = false;
                                                        break;
                                                    };
                                                    scope
                                                } else {
                                                    scope
                                                };
                                            let selected_scope = if let Some(scope) =
                                                scope.try_direct_logical_closure()?
                                            {
                                                Some(scope)
                                            } else if existence_candidate.is_none()
                                                && let Some(scope) = scope.try_simp_closure()?
                                            {
                                                Some(scope)
                                            } else if existence_candidate.is_none() {
                                                let Some(goal) = scope.goal().cloned() else {
                                                    selected = false;
                                                    break;
                                                };
                                                let compatibility_timing =
                                                    crate::instrumentation::OperationTiming::new(
                                                        function_block.signature().name(),
                                                        &proof_label,
                                                        "outcome simp compatibility construction",
                                                    );
                                                let compatibility = lower_outcome_simp_proof(
                                                    &replay,
                                                    surface_goal,
                                                    &goal,
                                                    &direct_available,
                                                    parsed_function.parameters(),
                                                    arguments,
                                                    pre_state,
                                                    post_state,
                                                    result,
                                                    predicate_environment,
                                                    click_function_environment,
                                                );
                                                drop(compatibility_timing);
                                                match compatibility {
                                                    Ok(SourceProof::Script(tactics)) => {
                                                        match ProofCertificate::from_proof_tactics(
                                                            &tactics,
                                                        ) {
                                                            Ok(candidate) => scope
                                                                .apply_candidate_certificate(
                                                                    &candidate,
                                                                )
                                                                .ok(),
                                                            Err(_) => None,
                                                        }
                                                    }
                                                    Ok(SourceProof::Default)
                                                    | Ok(SourceProof::Tactic(_))
                                                    | Err(_) => None,
                                                }
                                            } else {
                                                None
                                            };
                                            let Some(scope) = selected_scope else {
                                                check_verification_deadline()?;
                                                selected = false;
                                                break;
                                            };
                                            let joined = scope.join()?;
                                            for fact in joined.added_facts() {
                                                if !direct_available.contains(fact) {
                                                    direct_available.push(fact.clone());
                                                }
                                            }
                                            direct_proof = joined;
                                        }
                                        if selected {
                                            let surface_goals = direct_claims
                                                .iter()
                                                .map(|(_, goal)| goal.clone())
                                                .collect::<Vec<_>>();
                                            let certificate = direct_proof
                                                .complete_point_obligations_since(
                                                    &direct_base,
                                                    &surface_goals,
                                                )?;
                                            if replay.grouped_contract {
                                                for (claim_index, _) in direct_claims {
                                                    closures[claim_index] =
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
                                                for (claim_index, _) in direct_claims {
                                                    closures[claim_index] =
                                                        ClaimClosure::by_checked_certificate(
                                                            &certificate,
                                                        );
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
                                // Claims this `simp` discharges. A grouped contract
                                // certifies all of them with one transition, so they
                                // stay pending until it is built and replayed;
                                // `grouped_contract` picks which iteration builds the
                                // certificate, never what closure is allowed to mean.
                                let mut newly_closed: Vec<usize> = Vec::new();
                                let mut grouped_pending: Vec<usize> = Vec::new();
                                let mut grouped_transition_goals = Vec::new();
                                let path_execution_facts = path.execution_facts();
                                let closer_context = ExitClaimContext {
                                    replay: &replay,
                                    outcome_surface_propositions: &outcome_surface_propositions,
                                    path_requirements: &path_requirements,
                                    surface_certificate_facts: &surface_certificate_facts,
                                    execution_facts: &path_execution_facts,
                                    unfolded_predicates: &unfolded_predicates,
                                    existence_tactics: &existence_tactics,
                                    parameters: parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    outcome: &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    theorem_environment,
                                    function_requires: function_block.requires(),
                                    path_index,
                                    tactic_index: *tactic_index,
                                };
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                        continue;
                                    };
                                    let claim_label = function_claim_label(
                                        function_block.signature().name(),
                                        claim,
                                    );
                                    let result = if let Some(goal) =
                                        &rewritten_claim_goals[claim_index]
                                    {
                                        if !existence_tactics.is_empty() {
                                            return Err(ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: rewritten existential goals are not yet supported"
                                            )));
                                        }
                                        let mut reasoning_facts = path_requirements.clone();
                                        reasoning_facts.extend(
                                                    path.execution_facts()
                                                        .iter()
                                                        .filter(|fact| {
                                                            matches!(
                                                fact.proposition(),
                                                Proposition::CMemoryMutatesOnly { .. }
                                                    | Proposition::CMemoryEffectSummary { .. }
                                                    | Proposition::CHeapLifetimeRetired { .. }
                                            )
                                                        })
                                                        .map(|fact| fact.proposition().clone()),
                                                );
                                        let assumptions =
                                            assumptions_from_propositions(&reasoning_facts);
                                        match simp_proposition(goal, &assumptions) {
                                            SimpProposition::True => Ok(()),
                                            simplified => Err(ClickError::new(format!(
                                                "`simp` failed for `{claim_label}` path {path_index}: simplified rewritten proposition was not true: {simplified:?}"
                                            ))),
                                        }
                                    } else if frame_certified_claim_goals[claim_index].is_some() {
                                        Ok(())
                                    } else if existence_tactics.is_empty() {
                                        check_function_claim_by_simp(
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
                                            &replay.program_point_states,
                                            &unfolded_predicates,
                                        )
                                    } else {
                                        let mut available = path_requirements.clone();
                                        check_function_claim_with_existence_tactics(
                                            &claim_label,
                                            path_index,
                                            &path.execution_facts(),
                                            &mut available,
                                            claim,
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                            predicate_environment,
                                            click_function_environment,
                                            &unfolded_predicates,
                                            &existence_tactics,
                                            function_block.requires(),
                                            &replay.program_point_states,
                                            true,
                                        )
                                    };
                                    match result {
                                        Ok(()) => {
                                            match exit_claim::discharge_exit_simp_claim(
                                                &closer_context,
                                                claim_index,
                                                &claim_label,
                                                ensure_clause.ensure(),
                                                rewritten_claim_goals[claim_index].as_ref(),
                                                frame_certified_claim_goals[claim_index].as_ref(),
                                            )? {
                                                ExitSimpClosure::Closed(closure) => {
                                                    closures[claim_index] = closure;
                                                    newly_closed.push(claim_index);
                                                }
                                                ExitSimpClosure::JoinsGroupedTransition(goal) => {
                                                    grouped_transition_goals.extend(goal);
                                                    grouped_pending.push(claim_index);
                                                }
                                            }
                                        }
                                        Err(error) => {
                                            closures[claim_index]
                                                .record_failure(error.message().to_string());
                                            // The grouped certificate is the
                                            // proof-producing authority for proposition
                                            // claims. The ambient `simp` check above is
                                            // only a fast path and can miss a valid
                                            // source-site derivation, so retain the
                                            // lowered goal for exact certificate
                                            // construction below.
                                            if replay.grouped_contract
                                                && existence_tactics.is_empty()
                                                && rewritten_claim_goals[claim_index].is_none()
                                                && let Ensure::Proposition(surface_goal) =
                                                    ensure_clause.ensure()
                                                && let CFunctionOutcome::Return { .. } = &outcome
                                                && let Ok(goal) = lower_ensure_proposition_goal(
                                                    &path_requirements,
                                                    surface_goal,
                                                    parsed_function.parameters(),
                                                    arguments,
                                                    pre_state,
                                                    &outcome,
                                                    predicate_environment,
                                                    click_function_environment,
                                                    &replay.program_point_states,
                                                    &unfolded_predicates,
                                                )
                                            {
                                                grouped_transition_goals.push(
                                                    GroupedOutcomeSimpGoal {
                                                        claim_index,
                                                        claim_label,
                                                        surface_goal: surface_goal.clone(),
                                                        goal,
                                                    },
                                                );
                                                grouped_pending.push(claim_index);
                                            }
                                        }
                                    }
                                }
                                if replay.grouped_contract {
                                    if grouped_pending.is_empty() {
                                        // A divergent path has no return outcome to
                                        // transport through, but `simp` may still
                                        // close claims such as context-free tautologies
                                        // directly. Those closures need no grouped
                                        // outcome-transition certificate.
                                        for claim_index in newly_closed {
                                            let tactics = closures[claim_index]
                                                .closed()
                                                .expect("a newly closed claim has a certificate")
                                                .claim_tactics();
                                            path_grouped_surface_closers.extend_from_slice(tactics);
                                            if capturing_this_tactic {
                                                path_deferred_capture_tactics
                                                    .extend_from_slice(tactics);
                                            }
                                        }
                                        continue;
                                    }
                                    let grouped_claim_count = grouped_pending.len();
                                    let certificate = match &outcome {
                                        CFunctionOutcome::Return {
                                            value: result,
                                            state: post_state,
                                        } if existence_tactics.is_empty() => {
                                            let mut certificate_replay = replay.clone();
                                            certificate_replay.deferred_tactic_capture = None;
                                            certificate_replay.surface_propositions =
                                                outcome_surface_propositions.clone();
                                            certificate_replay.unfolded_predicates =
                                                unfolded_predicates.clone();
                                            certify_grouped_outcome_simp_transition(
                                                &certificate_replay,
                                                grouped_transition_goals,
                                                grouped_claim_count,
                                                &surface_certificate_facts,
                                                parsed_function.parameters(),
                                                arguments,
                                                pre_state,
                                                post_state,
                                                result,
                                                predicate_environment,
                                                click_function_environment,
                                                theorem_environment,
                                                function_block.requires(),
                                                &proof_label,
                                                *tactic_index,
                                                path_index,
                                            )
                                        }
                                        _ => Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped `simp` transition is not surface-certifiable"
                                        ))),
                                    }?;
                                    // Only now may the claims close: this transition is
                                    // the certificate every one of them carries.
                                    for claim_index in grouped_pending {
                                        closures[claim_index] =
                                            ClaimClosure::by_grouped_transition(&certificate);
                                    }
                                    path_grouped_surface_closers
                                        .extend(certificate.to_proof_tactics());
                                    if capturing_this_tactic {
                                        path_deferred_capture_tactics
                                            .extend(certificate.to_proof_tactics());
                                    }
                                } else if capturing_this_tactic {
                                    for claim_index in newly_closed {
                                        path_deferred_capture_tactics.extend_from_slice(
                                    closures[claim_index]
                                        .closed()
                                        .expect("a claim this `simp` closed holds its certificate")
                                        .claim_tactics(),
                                );
                                    }
                                }
                            }
                        }
                        if working_set_dirty {
                            // A legacy arm mutated the working set without
                            // writing through the outcome goal; one
                            // re-import restores the write-through invariant
                            // for the next tactic.
                            if let Some(evolving) = outcome_proof.take() {
                                outcome_proof =
                                    Some(evolving.with_drained_outcome_facts(&path_requirements)?);
                            }
                            working_set_dirty = false;
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

                    if !require_explicit_closers {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            let result = if !existence_tactics.is_empty() {
                                let mut available = path_requirements.clone();
                                check_function_claim_with_existence_tactics(
                                    &claim_label,
                                    path_index,
                                    &path.execution_facts(),
                                    &mut available,
                                    claim,
                                    parsed_function.parameters(),
                                    arguments,
                                    pre_state,
                                    &outcome,
                                    predicate_environment,
                                    click_function_environment,
                                    &unfolded_predicates,
                                    &existence_tactics,
                                    function_block.requires(),
                                    &replay.program_point_states,
                                    false,
                                )
                            } else {
                                check_function_claim(
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
                                    &replay.program_point_states,
                                    &unfolded_predicates,
                                )
                            };
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
                        if replay.execution_abstraction {
                            (
                                certified_path.clone(),
                                certified_outcomes[certified_path_index].clone(),
                                certification_facts.clone(),
                            )
                        } else {
                            let certified_outcome = &certified_outcomes[certified_path_index];
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
                    &certified_outcomes[certified_path_index];
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
                            expanded_proof: replay
                                .proof_certificate_builder
                                .blocker
                                .is_none()
                                .then(|| {
                                    ProofCertificate::from_steps(
                                        replay.proof_certificate_builder.steps.clone(),
                                    )
                                }),
                            expansion_blocker: replay.proof_certificate_builder.blocker.clone(),
                            specification: specification.clone(),
                            theorem: theorem.clone(),
                            concrete_loop_execution: replay.concrete_loop_execution,
                            frontier_loop_clauses: replay.frontier_loop_clauses.to_vec(),
                            frontier_loop_rules: replay.frontier_loop_rules.to_vec(),
                            checked_execution: certified_execution.clone(),
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
        let append_surface_tactics = |steps: &mut Vec<SimpleProofStep>,
                                      path_tactics: &[Vec<ProofTactic>]|
         -> Result<(), String> {
            if replay.proof_certificate_builder.path_choices.is_empty() {
                append_surface_tactics_by_leaf(steps, path_tactics)
            } else {
                append_surface_tactics_flat(steps, path_tactics)
            }
        };
        if replay.grouped_contract {
            let mut expanded = replay.proof_certificate_builder.clone();
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
            // surface arm is still required to replay the surrounding `if`.
            // Record exactly one builder per declared claim for this context;
            // tying builders to produced theorems silently dropped such arms
            // (and duplicated builders when a context certified many paths).
            for claim in claims {
                claim_surface_builders
                    .push((claim.verified_claim(), expanded.clone().into_value()));
            }
        } else {
            for (claim_index, claim) in claims.iter().enumerate() {
                let mut expanded = replay.proof_certificate_builder.clone();
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
                claim_surface_builders.push((verified_claim, expanded.into_value()));
            }
        }
        if tactic_expansion_capture_is_active(expansion_capture.as_deref()) {
            let Some(deferred) = replay.deferred_tactic_capture.as_ref() else {
                // Structured proofs produce one replay context per logical
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
            // execution-path/branch-trace pairing certificate replay keeps —
            // proof-level `if` conditions lower at each path's own outcome, so
            // an alien path meets another path's branch conditions as
            // contradictory facts it cannot use.
            let contributes_no_tactics = deferred_capture_tactics_by_path
                .iter()
                .all(|tactics| tactics.is_empty());
            let mut capture = ProofCertificateBuilder::default();
            let path_independent_capture = !deferred_capture_tactics_by_path.is_empty()
                && deferred_capture_tactics_by_path
                    .windows(2)
                    .all(|pair| pair[0] == pair[1])
                && deferred_capture_branches_by_path
                    .iter()
                    .all(Option::is_none);
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
    result.map_err(|error| add_proof_branch_path(error, &branch_path))
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
