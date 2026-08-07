use super::*;

pub(in crate::lang::click) fn prove_claim_by_tactics(
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
        execution_start_facts: pure_facts.clone(),
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
            branch_path: Vec::new(),
        },
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
        execution_start_facts: pure_facts.clone(),
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
    let contexts = execute_internal_proof(
        &program,
        ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path: Vec::new(),
        },
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
    )?;

    finish_ordered_proof_contexts(
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
}

#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click) fn prove_claims_by_grouped_auto(
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
    let certificate = verified
        .first()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`auto` proved no grouped claims for `{}.contract`",
                function_block.signature().name()
            ))
        })?
        .expanded_proof_certificate()
        .map_err(|error| {
            ClickError::new(format!(
                "`auto` succeeded internally for `{}.contract` without a surface certificate: {}",
                function_block.signature().name(),
                error.message()
            ))
        })?;
    let replayed = prove_claims_by_grouped_tactics(
        source_path,
        function_block,
        parsed_function,
        claims,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        certificate.tactics(),
        ProofTacticSource::GeneratedBy { source_index: 0 },
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`auto` surface certificate failed complete replay for `{}.contract`:\n{}\n{}",
            function_block.signature().name(),
            format_tactic_certificate(&certificate),
            error.message()
        ))
    })?;
    if replayed.len() != verified.len() {
        return Err(ClickError::new(format!(
            "`auto` surface certificate replayed {} grouped theorems for `{}.contract`, expected {}",
            replayed.len(),
            function_block.signature().name(),
            verified.len()
        )));
    }
    Ok(verified)
}

/// Exit-claim closure: the structural form of the settled invariant that a
/// smart success must replay through a surface-expressible certificate
/// before acceptance.
///
/// Mid-execution the invariant is already structural — a smart step can only
/// continue from the replay context `replay_smart_plan` returns, and there is
/// no other way to obtain one, so "accepted without a certificate" is not
/// spellable. At function exit the per-claim drain used to spell it easily:
/// closure was `closed_claims[i] = true`, a bool any site could set, with the
/// certificates hanging off parallel arrays and the gate re-asserted by hand
/// at every closing site.
///
/// `ClosedClaim` restores the mid-execution shape. Its field is private to
/// this module, so no site outside can build one, and the variant that carries
/// a generated certificate has exactly one constructor:
/// `discharge_exit_simp_claim`, which builds the certificate and replays it
/// before it can hand back a closure. The other constructors each take the
/// evidence that discharged the claim.
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

        /// Close a claim with the certificate a smart exit `simp` generated
        /// for it. Private to this module, and inside it reachable only from
        /// `discharge_exit_simp_claim`: the `TacticCertificate` is the
        /// evidence, and it exists only once the generator replayed the
        /// tactics through the replay judgment and got the claim's kernel
        /// goal back.
        fn by_replayed_certificate(certificate: &TacticCertificate) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::Claim(certificate.tactics().to_vec()),
            })
        }

        /// Close a claim covered by the path's grouped transition
        /// certificate. Taking the certificate is the point: the only way to
        /// hold one is to have run `certify_grouped_outcome_simp_transition`,
        /// which builds every claim's `have` and replays it.
        pub(super) fn by_grouped_transition(_certificate: &TacticCertificate) -> Self {
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
            certificate_replay.unfolded_predicates = self.unfolded_predicates.to_vec();
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
            let certificate = TacticCertificate::from_proof_tactics(&[ProofTactic::Normalize])
                .map_err(|error| {
                    context.certificate_failure(
                        claim_label,
                        &format!("divergence produced an invalid normalize certificate: {error:?}"),
                    )
                })?;
            return Ok(ExitSimpClosure::Closed(
                ClaimClosure::by_replayed_certificate(&certificate),
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
                ClaimClosure::by_replayed_certificate(&certificate),
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
                TacticCertificate::from_proof_tactics(&[ProofTactic::Assumption]).map_err(|error| {
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
            ClaimClosure::by_replayed_certificate(&certificate),
        ))
    }
}

use exit_claim::{ClaimClosure, ClosedClaim, ExitClaimContext, ExitSimpClosure};

#[allow(clippy::too_many_arguments)]
pub(super) fn finish_ordered_proof_replay(
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
    certification_cache: &mut Vec<(Vec<Proposition>, CState, bool, SymbolicCExecution)>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let ProofReplayContext {
        state,
        pure_facts,
        replay,
        branch_path,
    } = context;
    let proof_label = if require_explicit_closers {
        format!("{}.contract", function_block.signature().name())
    } else {
        function_claim_label(function_block.signature().name(), &claims[0])
    };
    let pre_state = replay.execution_start_state(&state);
    let frontier_function_block = (!replay.frontier_loop_clauses.is_empty())
        .then(|| function_block.with_bound_frontier_loop_clauses(&replay.frontier_loop_clauses));
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
            .with_verified_loop_rules(replay.frontier_loop_rules.clone())
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
        let mut certification_facts = replay.execution_start_facts.clone();
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
        let certified_execution = if replay.frontier_loop_rules.is_empty()
            && let Some((_, _, _, execution)) = certification_cache.iter().find(
                |(facts, cached_state, concrete_loop_execution, _)| {
                    facts == &certification_facts
                        && cached_state == pre_state
                        && *concrete_loop_execution == replay.concrete_loop_execution
                },
            ) {
            execution.clone()
        } else {
            let execution_start_assumptions = assumptions_from_propositions(&certification_facts);
            let execution = if replay.concrete_loop_execution {
                prove_symbolic_c_function_execution_paths_with_environment(
                    pre_state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    execution_start_assumptions,
                    function_environment.clone(),
                    CExecutionSemantics::APPLY_VERIFIED_RULES,
                )
            } else {
                prove_symbolic_c_function_contract_verification_paths_with_environment(
                    pre_state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    execution_start_assumptions,
                    function_environment.clone(),
                    CExecutionSemantics::APPLY_VERIFIED_RULES,
                )
            };
            if replay.frontier_loop_rules.is_empty() {
                certification_cache.push((
                    certification_facts.clone(),
                    pre_state.clone(),
                    replay.concrete_loop_execution,
                    execution.clone(),
                ));
            }
            execution
        };
        if let Some(limit) = certified_execution.limit() {
            if matches!(limit, crate::kernel::ExecutionLimit::Deadline) {
                return Err(ClickError::new(format!(
                    "verification time limit exceeded inside {}",
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
        let certified_path_for_replay = if replay.execution_abstraction {
            (!certified_outcomes.is_empty()).then(|| vec![0; execution.paths().len()])
        } else {
            execution
                .paths()
                .iter()
                .map(|replayed| {
                    (0..certified_outcomes.len())
                        .find(|certified_index| outcomes_match(replayed, *certified_index))
                })
                .collect::<Option<Vec<_>>>()
        };
        let Some(certified_path_for_replay) = certified_path_for_replay else {
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

        'execution_path: for (path_index, path) in execution.paths().iter().enumerate() {
            let certified_path =
                &certified_execution.paths()[certified_path_for_replay[path_index]];
            let mut path_grouped_surface_closers = Vec::new();
            let mut path_surface_post_tactics = Vec::new();
            let mut path_deferred_capture_tactics = Vec::new();
            let missing_obligations = path
                .obligations()
                .iter()
                .filter(|obligation| {
                    !exact_fact_is_available(obligation.proposition(), &pure_facts)
                })
                .cloned()
                .collect::<Vec<_>>();
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
            let mut outcome = path.outcome().clone();
            let mut path_requirements = pure_facts.clone();
            path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));

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
                for case in &replay.case_assumptions {
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
                    if path_requirements
                        .iter()
                        .any(|available| propositions_are_exact_negations(available, &fact))
                    {
                        continue 'execution_path;
                    }
                    let mut case_context = path_requirements.clone();
                    case_context.push(fact.clone());
                    if assumptions_from_propositions(&case_context)
                        .derive_proposition(&false_proposition())
                        .is_some()
                    {
                        // A proof-level branch only owns execution outcomes
                        // compatible with its assumption.  The sibling branch
                        // certifies this path; replaying this branch's exact
                        // per-outcome certificate against a contradictory
                        // path would require it to list an unrelated
                        // contradiction instead of the premises it was
                        // generated from.
                        continue 'execution_path;
                    }
                    path_requirements.push(fact);
                }
            }
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
                    .map_err(|message| {
                        ClickError::new(format!(
                            "execution proof failed for `{proof_label}` path {path_index}: could not align selected tactic with its execution branch: {message}"
                        ))
                    })?,
                    _ if deferred.branch_skeleton.is_empty() => Vec::new(),
                    _ => {
                        return Err(ClickError::new(format!(
                            "execution proof failed for `{proof_label}` path {path_index}: selected post-execution tactic has no return outcome for its proof branch"
                        )));
                    }
                }
            } else {
                Vec::new()
            };
            let mut unfolded_predicates = replay.unfolded_predicates.clone();
            path_requirements = unfold_available_predicate_facts(
                predicate_environment,
                click_function_environment,
                &unfolded_predicates,
                &path_requirements,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "execution proof failed for `{proof_label}` path {path_index}: {message}"
                ))
            })?;
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

            let mut closures = vec![ClaimClosure::default(); claims.len()];
            let mut rewritten_claim_goals: Vec<Option<Proposition>> = vec![None; claims.len()];
            let mut frame_certified_claim_goals: Vec<Option<Proposition>> =
                vec![None; claims.len()];
            let mut existence_tactics = Vec::new();
            let mut surface_certificate_facts = path_requirements.clone();
            let mut outcome_surface_propositions = replay.surface_propositions.clone();
            // Facts established after execution all describe this fixed
            // outcome snapshot. Keep them separately so `fold` can reuse an
            // exact lowering without accidentally selecting the same surface
            // spelling from an earlier program point.
            let mut current_outcome_surface_propositions = SurfacePropositionMap::default();
            for (post_execution_index, deferred) in replay.post_execution_tactics.iter().enumerate()
            {
                let tactic_index = &deferred.tactic_index;
                let source_index = &deferred.source_index;
                let post_tactic = &deferred.tactic;
                let _timing = crate::instrumentation::enabled().then(|| {
                    let (tactic_name, tactic_class) = post_execution_tactic_timing(post_tactic);
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
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            ProofTactic::FoldResource(resource.clone()),
                        );
                    }
                    PostExecutionTactic::UnfoldPredicate(name) => {
                        if !unfolded_predicates.contains(name) {
                            unfolded_predicates.push(name.clone());
                        }
                        path_requirements = unfold_available_predicate_facts(
                            predicate_environment,
                            click_function_environment,
                            std::slice::from_ref(name),
                            &path_requirements,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: {message}"
                            ))
                        })?;
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            ProofTactic::UnfoldPredicate(name.clone()),
                        );
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
                        let premises = plan_explicit_theorem_application_at_outcome(
                            theorem_environment,
                            application,
                            &proof_label,
                            path_index,
                            *tactic_index,
                            &path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        let surface_tactic = ProofTactic::ApplyTheoremUsing {
                            application: application.clone(),
                            premises,
                        };
                        let certificate = TacticCertificate::from_proof_tactics(
                            std::slice::from_ref(&surface_tactic),
                        )
                        .expect("post-execution smart apply must lower to a simple tactic");
                        let requirements_before = path_requirements.clone();
                        path_requirements = replay_outcome_apply_certificate(
                            &certificate,
                            theorem_environment,
                            &proof_label,
                            path_index,
                            *tactic_index,
                            path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        // The recorded `apply` tactic is prefixed to every
                        // claim certificate, so replay holds the theorem's
                        // conclusions when the closer runs. These facts were
                        // produced by replaying that very certificate, so
                        // planning the closer against them is planning
                        // against exactly the replay context.
                        record_certificate_facts_from_replay(
                            &requirements_before,
                            &path_requirements,
                            &mut surface_certificate_facts,
                        );
                        for tactic in certificate.tactics() {
                            record_post_execution_surface_tactic(
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
                        let requirements_before = path_requirements.clone();
                        path_requirements = apply_theorem_using_at_outcome(
                            theorem_environment,
                            application,
                            premises,
                            &proof_label,
                            path_index,
                            *tactic_index,
                            path_requirements,
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                            &unfolded_predicates,
                        )?;
                        record_certificate_facts_from_replay(
                            &requirements_before,
                            &path_requirements,
                            &mut surface_certificate_facts,
                        );
                        record_post_execution_surface_tactic(
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
                        let mut certificate_available = path_requirements.clone();
                        for fact in &replay.effect_facts {
                            if matches!(
                                fact.proposition(),
                                Proposition::CMemoryMutatesOnly { .. }
                                    | Proposition::CMemoryEffectSummary { .. }
                                    | Proposition::CHeapLifetimeRetired { .. }
                            ) && !certificate_available.contains(fact.proposition())
                            {
                                certificate_available.push(fact.proposition().clone());
                            }
                        }
                        for equation in
                            crate::kernel::certified_store_equations(&replay.effect_facts)
                        {
                            if !certificate_available.contains(&equation) {
                                certificate_available.push(equation);
                            }
                        }
                        // Post-execution proof certificates replay against
                        // the same kernel-certified loadability consequences
                        // of stores that were available while planning them.
                        // Restricting these facts to hand-written `derive`
                        // scripts let smart `simp` search succeed and then
                        // fail when its generated certificate was replayed.
                        for fact in
                            crate::kernel::certified_store_loadability_facts(&replay.effect_facts)
                        {
                            if !certificate_available.contains(&fact) {
                                certificate_available.push(fact);
                            }
                        }
                        let smart_unfolds = smart_simp_unfold_prefix(&have.proof);
                        let (surface_have, fact) = if let Some(smart_unfolds) = smart_unfolds {
                            let fact = lower_outcome_proposition_with_program_points(
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &path_requirements,
                                &have.proposition,
                                predicate_environment,
                                click_function_environment,
                                &replay.program_point_states,
                            )
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
                            let proof_tactic = lower_outcome_simp_tactic(
                                &certificate_replay,
                                &surface_goal,
                                &unfolded_goal,
                                &planning_available,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|error| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `have` failed: {}",
                                    error.message()
                                ))
                            })?;
                            let mut proof_tactics = smart_unfolds
                                .iter()
                                .cloned()
                                .map(ProofTactic::UnfoldPredicate)
                                .collect::<Vec<_>>();
                            proof_tactics.push(proof_tactic.clone());
                            let surface_have = ProofHave {
                                proposition: have.proposition.clone(),
                                proof: Proof::Script(proof_tactics),
                            };
                            let uses_store_spelling = matches!(
                                &proof_tactic,
                                ProofTactic::Derive(derive)
                                    if derive.premises.iter().any(|premise| matches!(
                                        premise,
                                        ClickProposition::Comparison {
                                            left: ContractExpression::At { .. },
                                            ..
                                        }
                                    ))
                            );
                            let mut replay_available = certificate_available.clone();
                            if uses_store_spelling {
                                for effect in &replay.effect_facts {
                                    if matches!(
                                        effect.proposition(),
                                        Proposition::CMemoryMutatesOnly { .. }
                                            | Proposition::CMemoryEffectSummary { .. }
                                            | Proposition::CHeapLifetimeRetired { .. }
                                    ) && !replay_available.contains(effect.proposition())
                                    {
                                        replay_available.push(effect.proposition().clone());
                                    }
                                }
                            }
                            let replay_have = |candidate: &ProofHave| {
                                prove_have_at_point(
                                    candidate,
                                    theorem_environment,
                                    &proof_label,
                                    *tactic_index,
                                    &replay_available,
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
                            let (surface_have, replayed_fact) = match replay_have(&surface_have) {
                                Ok(replayed_fact) => (surface_have, replayed_fact),
                                Err(initial_error) => {
                                    let Some(fallback) = surface_outcome_smart_have_derivation(
                                        &certificate_replay,
                                        &replay_available,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        result,
                                        predicate_environment,
                                        click_function_environment,
                                        have,
                                        &smart_unfolds,
                                    ) else {
                                        let failed_tactic = ProofTactic::Have(surface_have);
                                        let failed_certificate =
                                            TacticCertificate::from_proof_tactics(
                                                std::slice::from_ref(&failed_tactic),
                                            )
                                            .expect("post-execution smart have must lower to a simple tactic");
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: post-execution smart `have` certificate failed replay:\n{}\n{}",
                                            format_tactic_certificate(&failed_certificate),
                                            initial_error.message(),
                                        )));
                                    };
                                    match replay_have(&fallback) {
                                        Ok(replayed_fact) => (fallback, replayed_fact),
                                        Err(fallback_error) => {
                                            let failed_tactic = ProofTactic::Have(fallback);
                                            let failed_certificate =
                                                TacticCertificate::from_proof_tactics(
                                                    std::slice::from_ref(&failed_tactic),
                                                )
                                                .expect("post-execution smart have fallback must be a simple tactic");
                                            return Err(ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: post-execution smart `have` fallback certificate failed replay:\n{}\n{}",
                                                format_tactic_certificate(&failed_certificate),
                                                fallback_error.message(),
                                            )));
                                        }
                                    }
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
                            let fact = match replay_have(&certificate_available) {
                                Ok(fact) => fact,
                                Err(error) => {
                                    if !error.message().contains("missing pure fact: loadable(") {
                                        return Err(error);
                                    }
                                    let mut loadable_available = certificate_available.clone();
                                    for fact in crate::kernel::certified_store_loadability_facts(
                                        &replay.effect_facts,
                                    ) {
                                        if !loadable_available.contains(&fact) {
                                            loadable_available.push(fact);
                                        }
                                    }
                                    if loadable_available == certificate_available {
                                        return Err(error);
                                    }
                                    replay_have(&loadable_available)?
                                }
                            };
                            let mut surface_tactic = ProofTactic::Have(have.clone());
                            if let Err(error) = TacticCertificate::from_proof_tactics(
                                std::slice::from_ref(&surface_tactic),
                            ) {
                                match lower_smart_simp_suffix_have(
                                    have,
                                    &fact,
                                    theorem_environment,
                                    &proof_label,
                                    *tactic_index,
                                    &path_requirements,
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
                        outcome_surface_propositions.record_lowering(&have.proposition, &fact)?;
                        current_outcome_surface_propositions
                            .record_lowering(&have.proposition, &fact)?;
                        if !path_requirements.contains(&fact) {
                            path_requirements.push(fact);
                        }
                        record_post_execution_surface_tactic(
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
                        let certificate_context = premises.is_none().then(|| {
                            (
                                path_requirements.clone(),
                                outcome_surface_propositions.clone(),
                            )
                        });
                        let surface_tactic = replay_fact_transport_at_outcome(
                            source,
                            target,
                            premises.as_deref(),
                            &proof_label,
                            path_index,
                            *tactic_index,
                            &mut path_requirements,
                            &mut outcome_surface_propositions,
                            &path.execution_facts(),
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &replay,
                            predicate_environment,
                            click_function_environment,
                        )?;
                        if let Some((mut certificate_facts, mut certificate_surfaces)) =
                            certificate_context
                        {
                            let ProofTactic::TransportUsing {
                                source,
                                target,
                                premises,
                            } = &surface_tactic
                            else {
                                unreachable!(
                                    "smart post-execution transport must emit explicit premises"
                                )
                            };
                            TacticCertificate::from_proof_tactics(std::slice::from_ref(
                                &surface_tactic,
                            ))
                            .expect("explicit fact transport must be a simple certificate");
                            replay_fact_transport_at_outcome(
                                source,
                                target,
                                Some(premises),
                                &proof_label,
                                path_index,
                                *tactic_index,
                                &mut certificate_facts,
                                &mut certificate_surfaces,
                                &path.execution_facts(),
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                post_state,
                                result,
                                &replay,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|error| {
                                ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: post-execution `transport` certificate failed replay: {}",
                                    error.message()
                                ))
                            })?;
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            surface_tactic,
                        );
                    }
                    PostExecutionTactic::Choose(choice) => {
                        existence_tactics.push(ProofTactic::Choose(choice.clone()));
                        record_post_execution_surface_tactic(
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
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                continue;
                            };
                            if let Ensure::Resource(resource) = ensure_clause.ensure() {
                                if prove_ensure_resource(
                                    &function_claim_label(function_block.signature().name(), claim),
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
                            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
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
                            if path_requirements.contains(&goal)
                                || materialization_equivalent_available_fact(
                                    &goal,
                                    &path_requirements,
                                )
                                .is_some()
                                || quantified_replay_equivalent_available_fact(
                                    &goal,
                                    &path_requirements,
                                )
                                .is_some()
                            {
                                closures[claim_index] = ClaimClosure::by_exact_check();
                                closed_any = true;
                                break;
                            }
                        }
                        if !closed_any {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` did not match any current proposition goal"
                            )));
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            ProofTactic::Assumption,
                        );
                    }
                    PostExecutionTactic::Normalize => {
                        let mut closed_any = false;
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
                            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
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
                            if matches!(normalize_proposition(&goal), SimpProposition::True) {
                                closures[claim_index] = ClaimClosure::by_exact_check();
                                closed_any = true;
                            }
                        }
                        if !closed_any {
                            return Err(ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` did not prove any current proposition goal"
                            )));
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            ProofTactic::Normalize,
                        );
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
                        let equality = lower_outcome_proposition_with_program_points(
                            parsed_function.parameters(),
                            arguments,
                            pre_state,
                            post_state,
                            result,
                            &path_requirements,
                            surface_equality,
                            predicate_environment,
                            click_function_environment,
                            &replay.program_point_states,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` could not lower equality: {message}"
                            ))
                        })?;
                        let mut rewrote_any = false;
                        let mut first_error = None;
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                                continue;
                            };
                            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
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
                            match rewrite_proposition_by_exact_equality(
                                &goal,
                                &equality,
                                &path_requirements,
                            ) {
                                Ok(rewritten) => {
                                    rewritten_claim_goals[claim_index] = Some(rewritten);
                                    rewrote_any = true;
                                }
                                Err(message) => {
                                    first_error.get_or_insert(message);
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
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            ProofTactic::Rewrite(surface_equality.clone()),
                        );
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
                    }
                    PostExecutionTactic::Frame => {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
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
                        }
                        let mut premises = Vec::new();
                        for fact in &path_requirements {
                            if let Some(surface) =
                                replay.surface_propositions.surfaces(fact).next().cloned()
                                && !premises.contains(&surface)
                            {
                                premises.push(surface);
                            }
                        }
                        record_post_execution_surface_tactic(
                            &mut path_surface_post_tactics,
                            &mut path_deferred_capture_tactics,
                            replay.deferred_tactic_capture.as_ref(),
                            post_execution_index,
                            *tactic_index,
                            ProofTactic::FrameUsing {
                                region: None,
                                premises,
                            },
                        );
                    }
                    PostExecutionTactic::FrameUsing {
                        region,
                        premises,
                        facts,
                    } => {
                        let indexed_requirements = ExactReplayFactIndex::new(&path_requirements);
                        for fact in facts {
                            if !indexed_requirements.contains(fact)
                                && !exact_fact_is_available(fact, &path_requirements)
                                && materialization_equivalent_available_fact(
                                    fact,
                                    &path_requirements,
                                )
                                .is_none()
                            {
                                return Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `frame using` requires an exact premise that has not been established: {}",
                                    describe_pure_fact(
                                        fact,
                                        parsed_function.parameters(),
                                        arguments,
                                    )
                                )));
                            }
                        }
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            check_effect_claim_exact(
                                &claim_label,
                                path_index,
                                &path.execution_facts(),
                                facts,
                                claim,
                                parsed_function.parameters(),
                                arguments,
                                pre_state,
                                &outcome,
                            )?;
                            closures[claim_index] = ClaimClosure::by_exact_check();
                        }
                        record_post_execution_surface_tactic(
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
                    PostExecutionTactic::CertifiedFrame(path_derivations) => {
                        let derivations = path_derivations.get(path_index).ok_or_else(|| {
                            ClickError::new(format!(
                                "`{proof_label}` path {path_index}, tactic {tactic_index}: certified frame has no derivations for this execution path"
                            ))
                        })?;
                        let mut frame_facts = path_requirements.clone();
                        frame_facts.extend(
                            path.execution_facts()
                                .iter()
                                .map(|fact| fact.proposition().clone()),
                        );
                        let assumptions = assumptions_from_propositions(&frame_facts);
                        for derivation in derivations {
                            if !derivation.replay(&assumptions) {
                                return Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: certified frame derivation did not replay for {:?}",
                                    derivation.conclusion()
                                )));
                            }
                            if !path_requirements.contains(derivation.conclusion()) {
                                path_requirements.push(derivation.conclusion().clone());
                            }
                        }
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if !matches!(claim, FunctionClaimRef::Effect(_, _)) {
                                continue;
                            }
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
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
                        }
                    }
                    PostExecutionTactic::Simp => {
                        let capturing_this_tactic = replay
                            .deferred_tactic_capture
                            .as_ref()
                            .is_some_and(|capture| capture.tactic_index == *tactic_index);
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
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            let result = if let Some(goal) = &rewritten_claim_goals[claim_index] {
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
                                let assumptions = assumptions_from_propositions(&reasoning_facts);
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
                                        grouped_transition_goals.push(GroupedOutcomeSimpGoal {
                                            claim_index,
                                            claim_label,
                                            surface_goal: surface_goal.clone(),
                                            goal,
                                        });
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
                                        path_deferred_capture_tactics.extend_from_slice(tactics);
                                    }
                                }
                                continue;
                            }
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
                                        grouped_pending.len(),
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
                            path_grouped_surface_closers.extend_from_slice(certificate.tactics());
                            if capturing_this_tactic {
                                path_deferred_capture_tactics
                                    .extend_from_slice(certificate.tactics());
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
                if crate::instrumentation::deadline_exceeded() {
                    return Err(ClickError::new(format!(
                        "verification time limit exceeded inside {}",
                        crate::instrumentation::deadline_context()
                    )));
                }
            }

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
                        Err(error) => {
                            closures[claim_index].record_failure(error.message().to_string())
                        }
                    }
                }
            }

            if let Some((claim_index, claim)) = claims
                .iter()
                .enumerate()
                .find(|(claim_index, _)| !closures[*claim_index].is_closed())
            {
                let claim_label = function_claim_label(function_block.signature().name(), claim);
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

            let (certified_path, specification_outcome, specification_requirements) = if replay
                .execution_abstraction
            {
                (
                    certified_path.clone(),
                    certified_outcomes[certified_path_for_replay[path_index]].clone(),
                    certification_facts.clone(),
                )
            } else {
                let certified_outcome = &certified_outcomes[certified_path_for_replay[path_index]];
                let outcome_delta = describe_function_outcome_delta(
                    &outcome,
                    certified_outcome,
                    parsed_function.parameters(),
                    arguments,
                );
                let certified_path =
                        certify_c_function_execution_path_resource_representation(
                            certified_path,
                            outcome.clone(),
                            &path.execution_facts(),
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
            let theorem = prove_c_function_satisfies_specification_from_symbolic_path(
                function.clone(),
                specification.clone(),
                &certified_path,
            )
            .ok_or_else(|| {
                let certified_outcome =
                    &certified_outcomes[certified_path_for_replay[path_index]];
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
                    expanded_proof_tactics: replay
                        .surface_replay
                        .blocker
                        .is_none()
                        .then(|| replay.surface_replay.tactics.clone()),
                    expansion_blocker: replay.surface_replay.blocker.clone(),
                    specification: specification.clone(),
                    theorem: theorem.clone(),
                    concrete_loop_execution: replay.concrete_loop_execution,
                    frontier_loop_clauses: replay.frontier_loop_clauses.clone(),
                    frontier_loop_rules: replay.frontier_loop_rules.clone(),
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
        }
        if replay.grouped_contract {
            let mut expanded = replay.surface_replay.clone();
            if surface_post_tactics_by_path
                .iter()
                .any(|tactics| !tactics.is_empty())
                && let Err(message) = append_surface_tactics_by_leaf(
                    &mut expanded.tactics,
                    &surface_post_tactics_by_path,
                )
            {
                expanded.block(message);
            }
            if surface_grouped_closers_by_path
                .iter()
                .any(|tactics| !tactics.is_empty())
                && let Err(message) = append_surface_tactics_by_leaf(
                    &mut expanded.tactics,
                    &surface_grouped_closers_by_path,
                )
            {
                expanded.block(message);
            }
            for theorem in &mut verified {
                theorem.expanded_proof_tactics =
                    expanded.blocker.is_none().then(|| expanded.tactics.clone());
                theorem.expansion_blocker = expanded.blocker.clone();
            }
        } else {
            for (claim_index, claim) in claims.iter().enumerate() {
                let mut expanded = replay.surface_replay.clone();
                if surface_post_tactics_by_path
                    .iter()
                    .any(|tactics| !tactics.is_empty())
                    && let Err(message) = append_surface_tactics_by_leaf(
                        &mut expanded.tactics,
                        &surface_post_tactics_by_path,
                    )
                {
                    expanded.block(message);
                }
                if surface_closers_by_claim[claim_index]
                    .iter()
                    .any(|tactics| !tactics.is_empty())
                    && let Err(message) = append_surface_tactics_by_leaf(
                        &mut expanded.tactics,
                        &surface_closers_by_claim[claim_index],
                    )
                {
                    expanded.block(message);
                }
                let verified_claim = claim.verified_claim();
                for theorem in &mut verified {
                    if theorem.claim == verified_claim {
                        theorem.expanded_proof_tactics =
                            expanded.blocker.is_none().then(|| expanded.tactics.clone());
                        theorem.expansion_blocker = expanded.blocker.clone();
                    }
                }
            }
        }
        if tactic_expansion_capture_is_active() {
            let Some(deferred) = replay.deferred_tactic_capture.as_ref() else {
                // Structured proofs produce one replay context per logical
                // case.  A selected deferred tactic activates the shared
                // probe while those contexts are being built, but contexts
                // from sibling branches legitimately have no capture.  Let
                // them finish; the matching context records the expansion,
                // or the outer probe reports that no result was ever seen.
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
            let mut capture = SurfaceReplay::default();
            if !contributes_no_tactics {
                capture.tactics = deferred.branch_skeleton.clone();
                for (branch_path, path_tactics) in deferred_capture_branches_by_path
                    .iter()
                    .zip(&deferred_capture_tactics_by_path)
                {
                    if let Err(message) = append_surface_tactics_at_branch_path(
                        &mut capture.tactics,
                        branch_path,
                        path_tactics,
                    ) {
                        capture.block(message);
                        break;
                    }
                }
            }
            return Err(finish_tactic_expansion_capture(
                &capture,
                contributes_no_tactics,
            ));
        }
        Ok(verified)
    })();
    result.map_err(|error| add_proof_branch_path(error, &branch_path))
}
