use super::proof_object::ProofCheckpoint;
use super::*;
use crate::kernel::apply_c_function_contract_resource_transition;
use std::sync::Arc;

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
    pub(in crate::surface) theorems: Vec<VerifiedCTheorem>,
}

fn select_checked_post_execution_tactics<'a>(
    proof: &Proof<'_>,
    tactics: impl IntoIterator<Item = &'a DeferredPostExecutionTactic>,
    selected: &mut Vec<&'a DeferredPostExecutionTactic>,
    choices: &mut Vec<SurfacePathChoice>,
) -> Result<(), ClickError> {
    for deferred in tactics {
        match &deferred.tactic {
            PostExecutionTactic::If {
                condition,
                then_tactics,
                else_tactics,
            } => {
                let scoped = deferred
                    .lexical_bindings
                    .as_ref()
                    .map(|bindings| proof.with_surface_local_scope(bindings));
                let value = scoped
                    .as_ref()
                    .unwrap_or(proof)
                    .checked_outcome_if_value(condition)?;
                choices.push(SurfacePathChoice {
                    occurrence: deferred.source_index,
                    condition: condition.clone(),
                    value,
                    tactic_offset: selected.len(),
                });
                let arm = if value { then_tactics } else { else_tactics };
                select_checked_post_execution_tactics(proof, arm, selected, choices)?;
            }
            _ => selected.push(deferred),
        }
    }
    Ok(())
}

/// Serialize deferred proof cases at their checked operation offsets. Their
/// outcome paths need not have branches in the earlier C execution prefix.
fn synthesize_post_execution_paths(
    tactics: &[Vec<ProofTactic>],
    closers: &[Vec<ProofTactic>],
    choices: &[Vec<SurfacePathChoice>],
) -> Result<Vec<ProofStep>, String> {
    let paths = tactics
        .iter()
        .zip(closers)
        .zip(choices)
        .map(|((tactics, closers), choices)| {
            let mut steps = ProofCertificate::from_proof_tactics(tactics)
                .map_err(|error| format!("post-execution path is not simple: {error:?}"))?
                .steps;
            steps.extend(
                ProofCertificate::from_proof_tactics(closers)
                    .map_err(|error| format!("post-execution closer is not simple: {error:?}"))?
                    .steps,
            );
            Ok(ProofCertificateBuilder {
                steps,
                path_choices: choices.clone(),
                ..ProofCertificateBuilder::default()
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    synthesize_surface_alternatives(paths)
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
/// owned by the typed scope driver. Unsupported logical structures retain
/// their separately audited compatibility paths. Sequential nested scopes,
/// quantified contract resources, and counted populations use the same
/// checked resource entry and close operations as ordinary composite scopes.
/// The terminal diagnostic for a proof no checked driver accepts. The
/// drivers are the single verification engine; a shape they decline is a
/// gap to close in a driver, never a reason to run a second engine.
fn proof_shape_hint(tactics: &[ProofTactic]) -> Option<(usize, &'static str)> {
    tactics.iter().enumerate().find_map(|(index, tactic)| {
        let shape = match tactic {
            ProofTactic::Have(_) => "nested `have`",
            ProofTactic::Open(_) => "resource scope",
            ProofTactic::If(_) => "proof-level `if`",
            ProofTactic::Cases(_) => "proof-level `cases`",
            ProofTactic::Branch(_) => "proof-level `branch`",
            ProofTactic::Loop(_) => "loop proof",
            ProofTactic::ConstructResource(_) => "resource construction",
            ProofTactic::Witness(_) => "`witness`",
            ProofTactic::Choose(_) => "`choose`",
            ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::ApplyInductionUsing { .. } => "induction",
            _ => return None,
        };
        Some((index, shape))
    })
}

fn unsupported_proof_shape(
    proof_label: &str,
    grouped: bool,
    tactics: &[ProofTactic],
) -> ClickError {
    let route = if grouped {
        "grouped contract"
    } else {
        "single-claim"
    };
    let shape = proof_shape_hint(tactics)
        .map(|(index, shape)| format!("tactic {index} (`{shape}`)"))
        .unwrap_or_else(|| "the supplied tactic sequence".to_string());
    let rewrite = if grouped {
        "For proposition-only work, move the operation into `have proposition by { ... }`; grouped execution must still form one transition covering all claims."
    } else {
        "Keep execution scopes at supported structural boundaries, and move proposition-only work into `have proposition by { ... }`."
    };
    let decline_count = take_driver_declines().len();
    let attempts = if decline_count == 0 {
        "No checked route accepted it."
    } else {
        "All checked routes declined it."
    };
    ClickError::new(format!(
        "`{proof_label}`: the {route} proof driver declined {shape}. {attempts} This is a proof-shape limitation, not a failed proposition check. {rewrite}"
    ))
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

pub(in crate::surface) fn prove_claim_by_tactics(
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
        invariant_body_context: None,
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
    let mut initial = ExecutionProofState::at_entry(
        state,
        frontier,
        recorded_snapshots,
        surface_propositions,
        PersistentSequence::default(),
    );
    assert!(
        initial.core.record_checked_function_entry(
            &function,
            &arguments,
            constants
                .function_entry_state
                .as_ref()
                .expect("a function proof has a checked entry state"),
            assumptions_from_propositions(&pure_facts),
        )
    );
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
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        &function,
        &arguments,
    )?;
    let direct_proof = if structural.is_some() {
        structural
    } else {
        try_check_flat_function_proof(
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
        )?
    };
    if let Some(proof) = direct_proof {
        match finish_ordered_proof_units(
            expansion_capture,
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
    Err(unsupported_proof_shape(claim_label, false, tactics))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn prove_claims_by_grouped_tactics(
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
        invariant_body_context: None,
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
    let mut initial = ExecutionProofState::at_entry(
        state,
        frontier,
        recorded_snapshots,
        surface_propositions,
        PersistentSequence::default(),
    );
    assert!(
        initial.core.record_checked_function_entry(
            &function,
            &arguments,
            constants
                .function_entry_state
                .as_ref()
                .expect("a function proof has a checked entry state"),
            assumptions_from_propositions(&pure_facts),
        )
    );
    // Same order as the single-claim route: structural, then flat.
    let structural = try_check_structural_function_proof(
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
    )?;
    let direct_proof = if structural.is_some() {
        structural
    } else {
        try_check_flat_function_proof(
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
        )?
    };
    if let Some(proof) = direct_proof {
        match finish_ordered_proof_units(
            expansion_capture,
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
    Err(unsupported_proof_shape(&proof_label, true, tactics))
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn prove_claims_by_grouped_auto(
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
pub(in crate::surface) fn prove_claims_by_grouped_script(
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
    #[derive(Clone)]
    pub(super) struct ClosedClaim {
        certificate: ClaimCertificate,
        checked_proposition: Option<crate::kernel::proof::CheckedProposition>,
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

        pub(super) fn checked_proposition(
            &self,
        ) -> Option<&crate::kernel::proof::CheckedProposition> {
            self.checked_proposition.as_ref()
        }
    }

    /// A claim's state in the per-path exit drain.
    #[derive(Clone)]
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
                checked_proposition: None,
            })
        }

        /// Close a proposition claim with the exact completed kernel
        /// judgment that the checked certificate discharged.
        pub(super) fn by_checked_proposition(
            certificate: &ProofCertificate,
            checked_proposition: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::Claim(certificate.to_proof_tactics().to_vec()),
                checked_proposition: Some(checked_proposition),
            })
        }

        /// Close a claim covered by the path's grouped transition
        /// certificate. Taking the certificate is the point: it is either the
        /// terminal output of the checked fixed-state-obligation Proof operation or
        /// the output of the remaining grouped legacy certifier.
        pub(super) fn by_grouped_transition(_certificate: &ProofCertificate) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::GroupedTransition,
                checked_proposition: None,
            })
        }

        pub(super) fn by_grouped_proposition(
            _certificate: &ProofCertificate,
            checked_proposition: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::GroupedTransition,
                checked_proposition: Some(checked_proposition),
            })
        }

        /// Close a claim that an exact kernel check discharged.
        pub(super) fn by_exact_check() -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::ExactCheck,
                checked_proposition: None,
            })
        }

        /// Close a proposition claim that an exact kernel check discharged,
        /// retaining the completed kernel judgment so certification can
        /// match the claim instead of proving it again.
        pub(super) fn by_exact_check_completing(
            checked_proposition: Option<crate::kernel::proof::CheckedProposition>,
        ) -> Self {
            Self::Closed(ClosedClaim {
                certificate: ClaimCertificate::ExactCheck,
                checked_proposition,
            })
        }
    }
}

use exit_claim::{ClaimClosure, ClosedClaim};

/// The kernel's lowering of a claim's ensure at this path's outcome, with
/// the facts its loads introduced: the goal a claim proof closes is what
/// claim certification lowers, so the completion matches by construction.
/// A lowering with several paths is not yet closed as several goals.
fn kernel_claim_goal(
    function: &CFunction,
    claim: &FunctionClaimRef<'_>,
    pre_state: &CState,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
    unfolded_predicates: &[String],
) -> Option<(Proposition, Vec<Proposition>)> {
    let FunctionClaimRef::Ensure(source_index, _) = claim;
    let contract_index = function
        .contract_claims()
        .iter()
        .find_map(
            |contract_claim| match (contract_claim.key(), contract_claim.target()) {
                (
                    CFunctionContractClaimKey::Ensure(index),
                    CFunctionContractClaimTarget::EnsureProposition(contract_index),
                ) if index == source_index => Some(*contract_index),
                _ => None,
            },
        )?;
    let mut goals = crate::kernel::c_function_ensure_goals(
        function,
        contract_index,
        pre_state,
        arguments,
        outcome,
        assumptions,
        unfolded_predicates,
    )?;
    if goals.len() != 1 {
        return None;
    }
    goals.pop()
}

/// The forms an explicit closer may find a claim's goal in: the identity of
/// a registered predicate ensure first, then the body when the proof has
/// unfolded that predicate. A closer step is exact, so the closer tries each
/// form; two forms at most.
fn kernel_claim_goal_forms(
    function: &CFunction,
    claim: &FunctionClaimRef<'_>,
    pre_state: &CState,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
    unfolded_predicates: &[String],
) -> Vec<(Proposition, Vec<Proposition>)> {
    let mut forms = Vec::new();
    for unfolds in [&[][..], unfolded_predicates] {
        if let Some(form) = kernel_claim_goal(
            function,
            claim,
            pre_state,
            arguments,
            outcome,
            assumptions,
            unfolds,
        ) && !forms.contains(&form)
        {
            forms.push(form);
        }
    }
    forms
}

/// Focuses a claim goal from an outcome Proof that carries the path's
/// requirements: the kernel's lowering with the facts its loads introduced
/// when there is one, else the surface's lowering of the surface goal.
fn focus_claim_goal<'a>(
    root: &Proof<'a>,
    path_requirements: &[Proposition],
    kernel_goal: Option<(Proposition, Vec<Proposition>)>,
    surface_goal: &ClickProposition,
) -> Result<Proof<'a>, ClickError> {
    match kernel_goal {
        Some((goal, facts)) => root
            .with_checked_outcome_facts(&[path_requirements, facts.as_slice()].concat())?
            .focus_fixed_state_goal_with_surface(goal, Some(surface_goal.clone())),
        None => root.focus_fixed_state_surface_goal(surface_goal),
    }
}

/// Selects the one ungrouped proposition claim refined by top-level
/// `choose`/`witness` operations and starts its result-aware judgment from the
/// current outcome Proof. Rewrites and active unfolds are re-applied inside
/// this independently serializable claim body exactly as expansion requires,
/// but every operation advances this retained Proof directly.
fn begin_outcome_existence_proof<'a>(
    outcome_root: &Proof<'a>,
    function: &CFunction,
    pre_state: &CState,
    arguments: &[CExpression],
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
            let FunctionClaimRef::Ensure(_, ensure_clause) = claim;
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
    let kernel_goal = kernel_claim_goal(
        function,
        &claims[claim_index],
        pre_state,
        arguments,
        outcome,
        root.facts().assumptions(),
        &[],
    );
    let mut proof = focus_claim_goal(&root, path_requirements, kernel_goal, &surface_goal)?;
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

/// Closes one proposition claim from the outcome Proof by the direct logical
/// closure: the implicit closer of a claim with no `by` block. Rewrites and
/// active unfolds are applied as an explicit claim body would apply them. A
/// goal the fixed-state lowering cannot express, or that the closure does not
/// reach, is a miss; only a deadline is an error.
/// The implicit closer of a proposition claim: the claim goal is the
/// kernel's lowering of the contract ensure at the outcome, closed by the
/// direct logical closure or, when that does not apply, by the smart `simp`
/// search whose certificate is checked like an explicit one. Either way the
/// completion is what claim certification matches. When neither closes the
/// claim the reason names what stood in the way: the goal's lowering, a
/// rewrite that did not apply, or the goal left unclosed with the sides it
/// evaluated to.
#[allow(clippy::too_many_arguments)]
fn close_claim_directly_from_outcome<'a>(
    outcome_root: &Proof<'a>,
    function: &CFunction,
    claim: &FunctionClaimRef<'_>,
    pre_state: &CState,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    path_requirements: &[Proposition],
    surface_goal: &ClickProposition,
    rewrite_equalities: &[ClickProposition],
    unfolded_predicates: &[String],
    claim_label: &str,
    path_index: usize,
    parameters: &[syntax::C0Parameter],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Result<Proof<'a>, String>, ClickError> {
    let surface = describe_click_proposition(surface_goal);
    let failure = |reason: String| {
        Ok(Err(format!(
            "`ensures {surface}` failed for `{claim_label}` path {path_index}: {reason}"
        )))
    };
    if !matches!(outcome, CFunctionOutcome::Return { .. }) {
        return failure(describe_function_outcome(outcome, parameters, arguments));
    }
    let root = outcome_root
        .with_outcome_snapshot(outcome)?
        .with_checked_outcome_facts(path_requirements)?;
    let kernel_goal = kernel_claim_goal(
        function,
        claim,
        pre_state,
        arguments,
        outcome,
        root.facts().assumptions(),
        &[],
    );
    let mut proof = match focus_claim_goal(&root, path_requirements, kernel_goal, surface_goal) {
        Ok(proof) => proof,
        Err(error) => {
            check_verification_deadline()?;
            return failure(format!(
                "could not lower the claim goal: {}",
                error.message()
            ));
        }
    };
    for equality in rewrite_equalities {
        proof = match proof.apply_step(ProofStep::Rewrite(equality.clone())) {
            Ok(next) => next,
            Err(error) => {
                check_verification_deadline()?;
                return failure(format!(
                    "rewrite `{}` did not apply: {}",
                    describe_click_proposition(equality),
                    error.message()
                ));
            }
        };
    }
    for name in unfolded_predicates {
        match proof.apply_step(ProofStep::UnfoldPredicate(name.clone())) {
            Ok(next) => proof = next,
            Err(_) => check_verification_deadline()?,
        }
    }
    if let Some(completed) = proof.try_direct_logical_closure()?
        && completed.is_complete()
    {
        return Ok(Ok(completed));
    }
    if let Some(completed) = proof.try_simp_closure()?
        && completed.is_complete()
    {
        return Ok(Ok(completed));
    }
    check_verification_deadline()?;
    // A comparison reports what each side evaluates to at the outcome, by
    // the same kernel evaluation every proof-side expression gets.
    let evaluated_sides = match (surface_goal, outcome) {
        (
            ClickProposition::Comparison { left, right, .. },
            CFunctionOutcome::Return { value, state },
        ) => {
            let values = parameter_values(parameters, arguments).unwrap_or_default();
            let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
            let evaluate = |expression: &ContractExpression| {
                evaluate_fixed_state_expression_through_kernel(
                    expression,
                    root.facts().assumptions(),
                    &values,
                    &array_refs,
                    pre_state,
                    state,
                    Some(value),
                    &RecordedSnapshots::new(),
                    predicate_environment,
                    click_function_environment,
                    &BTreeSet::new(),
                )
                .ok()
            };
            match (evaluate(left), evaluate(right)) {
                (Some(left), Some(right)) => format!(
                    "; left side evaluated to {}, right side evaluated to {}",
                    describe_c_value(&left, parameters, arguments),
                    describe_c_value(&right, parameters, arguments)
                ),
                _ => String::new(),
            }
        }
        _ => String::new(),
    };
    let resource_facts = match outcome {
        CFunctionOutcome::Return { state, .. } => state.resources().facts().to_vec(),
        _ => Vec::new(),
    };
    let pure_facts = root.facts().assumptions().pure_facts();
    failure(format!(
        "unclosed goal: {surface}{evaluated_sides}
  {}",
        describe_available_facts(&pure_facts, &resource_facts, parameters, arguments, &[])
    ))
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

/// Serializes retained checked Proof provenance as surface steps. This is a
/// structural serialization, not a semantic search or reconstruction.
fn surface_steps_from_checked_proof(proof: &Proof<'_>) -> Result<Vec<ProofStep>, ClickError> {
    let tactics = proof.certificate().to_proof_tactics();
    ProofCertificate::from_proof_tactics(&tactics)
        .map(|certificate| certificate.steps().to_vec())
        .map_err(|error| {
            ClickError::new(format!(
                "checked Proof provenance is not surface-expressible: {error:?}"
            ))
        })
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
    let mut authoritative_outcome_haves = BTreeSet::new();
    collect_post_execution_if_have_indices(
        direct_view
            .execution
            .presentation
            .post_execution_tactics
            .iter(),
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
    proof_execution
        .core
        .validate_execution_evidence_shapes()
        .map_err(|message| ClickError::new(format!("{proof_label}: {message}")))?;
    let retained_surface = {
        let record = &proof_execution.presentation.surface_record;
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
            annotated_function(
                frontier_function_block,
                parsed_function,
                pre_state,
                arguments,
                predicate_environment,
                click_function_environment,
                resource_environment,
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
        // Facts the proof derived at function entry stay where the proof
        // object retained them: in the fact context of every later checked
        // step, which completion reads per path. They are not entry
        // assumptions of the whole function; inside a proof-level `if` arm
        // they hold only under that arm's case.
        certification_facts.extend(
            proof_execution
                .presentation
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
        let base_certification_facts = certification_facts;
        let execution_semantics = if proof_execution.core.concrete_loop_execution
            || !proof_execution.core.frontier_loop_rules.is_empty()
        {
            CExecutionSemantics::APPLY_VERIFIED_RULES
        } else {
            CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS
        };
        let execution_mode = if proof_execution.core.concrete_loop_execution {
            CFunctionContractExecutionMode::ExecuteLoops
        } else {
            CFunctionContractExecutionMode::VerifyLoops
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
                        assumptions_from_propositions(&base_certification_facts),
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
        let certified_outcomes = completed_execution
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
                    "completion for `{proof_label}` produced an inexact theorem body {proposition:?}"
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        // The completed paths are the proof's candidates in order, so each
        // candidate's certified path is its own index. A candidate the
        // Proof-owned outcome derivation rejected under an exact
        // contradictory path fact owns no goal and is not finished.
        let certified_path_for_proof: Vec<Option<usize>> = (0..execution.paths().len())
            .map(|path_index| {
                let rejected = outcome_substrate.as_ref().is_some_and(|(substrate, _)| {
                    substrate.outcome_branch_for_path(path_index).is_none()
                });
                (!rejected).then_some(path_index)
            })
            .collect();
        let mut verified = Vec::new();
        let mut returned_core = proof_execution.core.clone();
        let mut any_return_instance_rewrite = false;
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_grouped_closers_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_choices_by_path = Vec::with_capacity(execution.paths().len());
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
                    let Some(certified_path_index) = certified_path_for_proof[path_index] else {
                        // The outcome derivation rejected this candidate under
                        // an exact contradictory path fact; it owns no goal.
                        continue 'execution_path;
                    };
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
                    if !proof_execution.presentation.case_assumptions.is_empty() {
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
                        for case in &proof_execution.presentation.case_assumptions {
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
                            &proof_execution.presentation.recorded_snapshots,
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
                    let deferred_capture_branch_path = if let Some(deferred) = proof_execution
                        .presentation
                        .expansion
                        .deferred_tactic_capture
                        .as_ref()
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
                                        &proof_execution.presentation.recorded_snapshots,
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

                    // Interpret post-return counts using the checked exit, but
                    // retain the body's ownership until its open resources have
                    // been closed. Entry/body facts above were projected before
                    // this change; the new invariant remains a proof obligation.
                    outcome = crate::kernel::function_body_with_return_counts(
                        &outcome,
                        &certified_outcomes[certified_path_index],
                    );

                    let (
                        mut closures,
                        mut rewritten_claim_goals,
                        _frame_certified_claim_goals,
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
                                proof_execution.presentation.surface_propositions.clone(),
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
                    // A claim goal rewritten on the retained outcome proof
                    // stays that proof, with the position after the rewrite:
                    // the closers after it continue the same derivation, so
                    // the completion they record is the claim goal the proof
                    // was rooted at, not the rewritten form.
                    let mut rewritten_claim_proofs: Vec<Option<(Proof<'_>, ProofCheckpoint<'_>)>> =
                        (0..claims.len()).map(|_| None).collect();
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
                    let mut has_return_instance_rewrite = false;
                    // Legacy frame proofs also reconstruct the returned
                    // resource context. Track that ownership transition
                    // separately from the return-count interpretation above:
                    // closing an open body must retain its owned resources
                    // until its invariant has been proved.
                    let mut resource_transition_applied = false;
                    // Why the contract's resource transition did not apply at
                    // the closing `simp`, reported when a claim then stays open.
                    let mut pending_resource_transition_error: Option<String> = None;
                    drop(_path_preparation_timing);
                    let _post_execution_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "post-execution claim tactics",
                    );
                    let mut selected_post_execution_tactics = Vec::new();
                    let mut selected_post_choices = Vec::new();
                    if let Some(branch_proof) = outcome_proof.as_ref() {
                        select_checked_post_execution_tactics(
                            branch_proof,
                            proof_execution.presentation.post_execution_tactics.iter(),
                            &mut selected_post_execution_tactics,
                            &mut selected_post_choices,
                        )?;
                    } else {
                        if proof_execution
                            .presentation
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
                            .extend(proof_execution.presentation.post_execution_tactics.iter());
                    }
                    // Only an ordered drain that has no closing `simp` and no
                    // further resource operation of its own needs the
                    // transition up front: an expanded proof closes its
                    // resource ensures with `assumption()` and never re-folds.
                    if !selected_post_execution_tactics.iter().any(|deferred| {
                        matches!(
                            deferred.tactic,
                            PostExecutionTactic::Simp
                                | PostExecutionTactic::Fold(_)
                                | PostExecutionTactic::Unfold(_)
                                | PostExecutionTactic::Construct(_)
                                | PostExecutionTactic::CloseOpen { .. }
                        )
                    }) {
                        // Read the outcome's resources through the contract's
                        // checked transition as soon as the body returns what the
                        // contract returns. Ownership, not a framing tactic, is what
                        // hands a produced or returned resource to a resource
                        // ensure, so every ordered closer sees the same transitioned
                        // context. A body that still has to fold an open composite
                        // does not satisfy the guard here; the closing `simp` runs
                        // the same transition once that fold has happened.
                        if matches!(outcome, CFunctionOutcome::Return { .. })
                            && crate::kernel::c_function_return_resources_definitionally_established(
                                pre_state,
                                function,
                                arguments,
                                &outcome,
                                &assumptions_from_propositions(&path_requirements),
                            )
                        {
                            let mut transitioned = outcome.clone();
                            if apply_checked_contract_resource_transition(
                                &mut transitioned,
                                pre_state,
                                function,
                                arguments,
                                &path_requirements,
                                &path.execution_facts(),
                                &proof_label,
                                path_index,
                            )
                            .is_ok()
                            {
                                outcome = transitioned;
                                resource_transition_applied = true;
                                if let Some(evolving) = outcome_proof.take() {
                                    outcome_proof = Some(
                                        evolving
                                            .with_outcome_snapshot(&outcome)?
                                            .with_checked_outcome_facts(&path_requirements)?,
                                    );
                                }
                            }
                        }
                    }
                    let mut selected_post_choices = selected_post_choices.into_iter().peekable();
                    // An expansion replaces one source occurrence. Outcomes
                    // that never reach it must not contribute empty sibling
                    // certificates or reintroduce their enclosing C guard.
                    let visits_selected_capture = proof_execution
                        .presentation
                        .expansion
                        .deferred_tactic_capture
                        .as_ref()
                        .is_some_and(|capture| {
                            selected_post_execution_tactics.iter().any(|tactic| {
                                tactic.tactic_index == capture.tactic_index
                                    && tactic.source_index == capture.source_index
                            })
                        });
                    let mut surface_post_choices = Vec::new();
                    for (post_execution_index, deferred) in
                        selected_post_execution_tactics.into_iter().enumerate()
                    {
                        if let Some(bindings) = &deferred.lexical_bindings {
                            outcome_proof =
                                outcome_proof.map(|proof| proof.with_surface_local_scope(bindings));
                        }
                        while selected_post_choices
                            .peek()
                            .is_some_and(|choice| choice.tactic_offset == post_execution_index)
                        {
                            let mut choice = selected_post_choices.next().unwrap();
                            choice.tactic_offset = path_surface_post_tactics.len();
                            surface_post_choices.push(choice);
                        }
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
                            PostExecutionTactic::Fold(resource)
                            | PostExecutionTactic::Unfold(resource) => {
                                let Some(evolving) = outcome_proof.take() else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: typed outcome resource operation has no Proof goal"
                                    )));
                                };
                                let before = evolving.checkpoint();
                                let step = if matches!(post_tactic, PostExecutionTactic::Unfold(_))
                                {
                                    ProofStep::UnfoldResource(resource.clone())
                                } else {
                                    ProofStep::FoldResource(resource.clone())
                                };
                                let folded = evolving.apply_step(step)?;
                                has_return_instance_rewrite |=
                                    matches!(resource, ResourceClause::Named { .. });
                                outcome = folded.focused_outcome_snapshot()?;
                                let surface_tactics =
                                    folded.certificate_since(&before)?.to_proof_tactics();
                                outcome_proof = Some(folded);
                                for tactic in surface_tactics {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::Construct(resource) => {
                                let Some(evolving) = outcome_proof.take() else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: typed outcome `construct` has no Proof goal"
                                    )));
                                };
                                let before = evolving.checkpoint();
                                let constructed = evolving
                                    .apply_step(ProofStep::ConstructResource(resource.clone()))?;
                                outcome = constructed.focused_outcome_snapshot()?;
                                let surface_tactics =
                                    constructed.certificate_since(&before)?.to_proof_tactics();
                                outcome_proof = Some(constructed);
                                for tactic in surface_tactics {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
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
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
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
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
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
                                    proof_execution
                                        .presentation
                                        .expansion
                                        .deferred_tactic_capture
                                        .as_ref(),
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
                                    proof_execution
                                        .presentation
                                        .expansion
                                        .deferred_tactic_capture
                                        .as_ref(),
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
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
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
                                            function,
                                            pre_state,
                                            arguments,
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
                                    proof_execution
                                        .presentation
                                        .expansion
                                        .deferred_tactic_capture
                                        .as_ref(),
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
                                            function,
                                            pre_state,
                                            arguments,
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
                                    proof_execution
                                        .presentation
                                        .expansion
                                        .deferred_tactic_capture
                                        .as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::Witness(witness.clone()),
                                );
                            }
                            PostExecutionTactic::Intro => {
                                let (claim_index, surface_goal, proof) =
                                    match existence_proof.take() {
                                        Some(active) => active,
                                        None => begin_outcome_existence_proof(
                                            outcome_proof.as_ref().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for `intro` is unavailable"
                                                ))
                                            })?,
                                            function,
                                            pre_state,
                                            arguments,
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
                                    .apply_step(ProofStep::Intro)?;
                                existence_proof = Some((claim_index, surface_goal, proof));
                                record_post_execution_surface_tactic(
                                    deferred.surface_recorded,
                                    &mut path_surface_post_tactics,
                                    &mut path_deferred_capture_tactics,
                                    proof_execution
                                        .presentation
                                        .expansion
                                        .deferred_tactic_capture
                                        .as_ref(),
                                    post_execution_index,
                                    *tactic_index,
                                    ProofTactic::Intro,
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
                                        &proof_execution.presentation.recorded_snapshots,
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
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim;
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
                                            ensure_clause.borrowed(),
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
                                    let kernel_goals = kernel_claim_goal_forms(
                                        function,
                                        claim,
                                        contract_pre_state,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                        &unfolded_predicates,
                                    );
                                    // Expansion can emit a checked `have` of
                                    // the original claim after rewriting it.
                                    // Independently prove that exact original
                                    // claim on the current root; never treat a
                                    // failed rewritten proof as a success.
                                    if rewritten_claim_proofs[claim_index].is_some() {
                                        if let Some(root) = &fixed_state_root {
                                            for (original, _) in &kernel_goals {
                                                let candidate = root
                                                    .focus_fixed_state_goal_with_surface(
                                                        original.clone(),
                                                        Some(surface_goal.clone()),
                                                    )?
                                                    .apply_step(ProofStep::Assumption);
                                                if let Ok(proof) = candidate {
                                                    retained_certificate =
                                                        Some(proof.certificate());
                                                    closures[claim_index] =
                                                        ClaimClosure::by_exact_check_completing(
                                                            proof.completed_proposition().ok(),
                                                        );
                                                    closed_any = true;
                                                    break;
                                                }
                                            }
                                        }
                                        if closed_any {
                                            break;
                                        }
                                    }
                                    let goal_candidates = match (
                                        &rewritten_claim_goals[claim_index],
                                        kernel_goals.is_empty(),
                                    ) {
                                        (Some(goal), _) => vec![(goal.clone(), Vec::new())],
                                        (None, false) => kernel_goals,
                                        (None, true) => vec![(
                                            {
                                                if let Some(recorded) = outcome_surface_propositions
                                                    .available_kernel(
                                                        surface_goal,
                                                        &path_requirements,
                                                    )
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
                                            &proof_execution.presentation.recorded_snapshots,
                                            &unfolded_predicates,
                                        )
                                        .map_err(|message| {
                                            ClickError::new(format!(
                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: `assumption` could not lower goal: {message}"
                                            ))
                                        })?
                                                }
                                            },
                                            Vec::new(),
                                        )],
                                    };
                                    // A goal rewritten on the retained outcome
                                    // proof is closed on that proof.
                                    if let Some((rewritten, checkpoint)) =
                                        &rewritten_claim_proofs[claim_index]
                                    {
                                        match rewritten.apply_step(ProofStep::Assumption) {
                                            Ok(proof) => {
                                                retained_certificate =
                                                    Some(proof.certificate_since(checkpoint)?);
                                                closures[claim_index] =
                                                    ClaimClosure::by_exact_check_completing(
                                                        proof.completed_proposition().ok(),
                                                    );
                                                closed_any = true;
                                                break;
                                            }
                                            Err(_) => {
                                                check_verification_deadline()?;
                                                continue;
                                            }
                                        }
                                    }
                                    let Some(fixed_state_root) = &fixed_state_root else {
                                        continue;
                                    };
                                    let mut closed = None;
                                    let mut last_error = None;
                                    for (goal, goal_facts) in goal_candidates {
                                        match fixed_state_root
                                            .with_checked_outcome_facts(
                                                &[
                                                    path_requirements.as_slice(),
                                                    goal_facts.as_slice(),
                                                ]
                                                .concat(),
                                            )?
                                            .focus_fixed_state_goal_with_surface(
                                                goal,
                                                Some(surface_goal.clone()),
                                            )?
                                            .apply_step(ProofStep::Assumption)
                                        {
                                            Ok(proof) => {
                                                closed = Some(proof);
                                                break;
                                            }
                                            Err(error) => last_error = Some(error),
                                        }
                                    }
                                    match closed {
                                        Some(proof) => {
                                            retained_certificate = Some(proof.certificate());
                                            closures[claim_index] =
                                                ClaimClosure::by_exact_check_completing(
                                                    proof.completed_proposition().ok(),
                                                );
                                            closed_any = true;
                                            break;
                                        }
                                        None => {
                                            drop(last_error);
                                            check_verification_deadline()?;
                                        }
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
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic.clone(),
                                    );
                                }
                            }
                            PostExecutionTactic::Normalize
                            | PostExecutionTactic::NormalizeUsing(_)
                            | PostExecutionTactic::Both(_) => {
                                let closer_name =
                                    if matches!(post_tactic, PostExecutionTactic::Both(_)) {
                                        "both"
                                    } else {
                                        "normalize"
                                    };
                                let normalization_step = match post_tactic {
                                    PostExecutionTactic::NormalizeUsing(premises) => {
                                        ProofStep::NormalizeUsing(premises.clone())
                                    }
                                    _ => ProofStep::Normalize,
                                };
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
                                        &proof_execution.presentation.recorded_snapshots,
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
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim;
                                    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
                                        if matches!(post_tactic, PostExecutionTactic::Both(_)) {
                                            return Err(ClickError::new(
                                                "`both` requires a return-state conjunction",
                                            ));
                                        }
                                        // Postconditions are conditional on return.
                                        // Normalization exposes that definitional
                                        // partial-correctness rule without requiring a
                                        // nonexistent return value or state.
                                        if matches!(
                                            normalization_step,
                                            ProofStep::NormalizeUsing(_)
                                        ) {
                                            return Err(ClickError::new(
                                                "`normalize using` requires a return-state proposition; use context-free `normalize()` for a divergent path",
                                            ));
                                        }
                                        closures[claim_index] = ClaimClosure::by_exact_check();
                                        closed_any = true;
                                        continue;
                                    }
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        continue;
                                    };
                                    let kernel_goals = kernel_claim_goal_forms(
                                        function,
                                        claim,
                                        contract_pre_state,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                        &unfolded_predicates,
                                    );
                                    let goal_candidates = match (
                                        &rewritten_claim_goals[claim_index],
                                        kernel_goals.is_empty(),
                                    ) {
                                        (Some(goal), _) => vec![(goal.clone(), Vec::new())],
                                        (None, false) => kernel_goals,
                                        (None, true) => vec![(
                                            lower_ensure_proposition_goal(
                                                &path_requirements,
                                                surface_goal,
                                                parsed_function.parameters(),
                                                arguments,
                                                pre_state,
                                                &outcome,
                                                predicate_environment,
                                                click_function_environment,
                                                &proof_execution.presentation.recorded_snapshots,
                                                &unfolded_predicates,
                                            )
                                            .map_err(|message| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `normalize` could not lower goal: {message}"
                                                ))
                                            })?,
                                            Vec::new(),
                                        )],
                                    };
                                    // A goal rewritten on the retained outcome
                                    // proof is closed on that proof.
                                    if let Some((rewritten, checkpoint)) =
                                        &rewritten_claim_proofs[claim_index]
                                    {
                                        match if let PostExecutionTactic::Both(both) = post_tactic {
                                            rewritten.apply_both_source(both)
                                        } else {
                                            rewritten.apply_step(normalization_step.clone())
                                        } {
                                            Ok(proof) => {
                                                let certificate =
                                                    proof.certificate_since(checkpoint)?;
                                                retained_certificate.get_or_insert(certificate);
                                                closures[claim_index] =
                                                    ClaimClosure::by_exact_check_completing(
                                                        proof.completed_proposition().ok(),
                                                    );
                                                closed_any = true;
                                            }
                                            Err(_) => check_verification_deadline()?,
                                        }
                                        continue;
                                    }
                                    let Some(fixed_state_root) = &fixed_state_root else {
                                        continue;
                                    };
                                    let mut closed = None;
                                    let mut last_error = None;
                                    for (goal, goal_facts) in goal_candidates {
                                        let focused = fixed_state_root
                                            .with_checked_outcome_facts(
                                                &[
                                                    path_requirements.as_slice(),
                                                    goal_facts.as_slice(),
                                                ]
                                                .concat(),
                                            )?
                                            .focus_fixed_state_goal_with_surface(
                                                goal,
                                                Some(surface_goal.clone()),
                                            )?;
                                        match if let PostExecutionTactic::Both(both) = post_tactic {
                                            focused.apply_both_source(both)
                                        } else {
                                            focused.apply_step(normalization_step.clone())
                                        } {
                                            Ok(proof) => {
                                                closed = Some(proof);
                                                break;
                                            }
                                            Err(error) => last_error = Some(error),
                                        }
                                    }
                                    match closed {
                                        Some(proof) => {
                                            retained_certificate
                                                .get_or_insert_with(|| proof.certificate());
                                            closures[claim_index] =
                                                ClaimClosure::by_exact_check_completing(
                                                    proof.completed_proposition().ok(),
                                                );
                                            closed_any = true;
                                        }
                                        None => {
                                            drop(last_error);
                                            check_verification_deadline()?;
                                        }
                                    }
                                }
                                if !closed_any {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `{closer_name}` did not prove any current proposition goal"
                                    )));
                                }
                                let tactics = retained_certificate
                                    .as_ref()
                                    .map(ProofCertificate::to_proof_tactics)
                                    .unwrap_or_else(|| vec![normalization_step.to_proof_tactic()]);
                                for tactic in tactics {
                                    record_post_execution_surface_tactic(
                                        deferred.surface_recorded,
                                        &mut path_surface_post_tactics,
                                        &mut path_deferred_capture_tactics,
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
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
                                    Some(_) => None,
                                    None => Some(Proof::for_fixed_state_frontier(
                                        &proof_label,
                                        *tactic_index,
                                        &path_requirements,
                                        parsed_function.parameters(),
                                        arguments,
                                        pre_state,
                                        post_state,
                                        Some(result),
                                        &proof_execution.presentation.recorded_snapshots,
                                        &outcome_surface_propositions,
                                        predicate_environment,
                                        click_function_environment,
                                        theorem_environment,
                                        &unfolded_predicates,
                                        &transition_facts,
                                    )),
                                };
                                let mut rewrote_any = false;
                                let mut first_error = None;
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let FunctionClaimRef::Ensure(_, ensure_clause) = claim;
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        continue;
                                    };
                                    let kernel_goals = kernel_claim_goal_forms(
                                        function,
                                        claim,
                                        contract_pre_state,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                        &unfolded_predicates,
                                    );
                                    let goal_candidates = match (
                                        &rewritten_claim_goals[claim_index],
                                        kernel_goals.is_empty(),
                                    ) {
                                        (Some(goal), _) => vec![(goal.clone(), Vec::new())],
                                        (None, false) => kernel_goals,
                                        (None, true) => vec![(
                                            lower_ensure_proposition_goal(
                                                &path_requirements,
                                                surface_goal,
                                                parsed_function.parameters(),
                                                arguments,
                                                pre_state,
                                                &outcome,
                                                predicate_environment,
                                                click_function_environment,
                                                &proof_execution.presentation.recorded_snapshots,
                                                &unfolded_predicates,
                                            )
                                            .map_err(|message| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` could not lower goal: {message}"
                                                ))
                                            })?,
                                            Vec::new(),
                                        )],
                                    };
                                    // The rewrite continues a goal already
                                    // rewritten on the retained outcome proof,
                                    // or opens the claim goal on that proof;
                                    // only without one does it use a fresh
                                    // fixed-state proof, as the closers after
                                    // it then will.
                                    let mut rewritten_result = None;
                                    let mut last_error = None;
                                    if let Some((rewritten, checkpoint)) =
                                        &rewritten_claim_proofs[claim_index]
                                    {
                                        match rewritten.apply_step(ProofStep::Rewrite(
                                            surface_equality.clone(),
                                        )) {
                                            Ok(proof) => {
                                                let certificate =
                                                    proof.certificate_since(checkpoint)?;
                                                rewritten_result = Some((
                                                    proof.goal().cloned(),
                                                    certificate,
                                                    Some(proof),
                                                ));
                                            }
                                            Err(error) => last_error = Some(error),
                                        }
                                    } else if let Some(evolving) = outcome_proof.as_ref() {
                                        for (goal, goal_facts) in &goal_candidates {
                                            match evolving
                                                .with_checked_outcome_facts(
                                                    &[
                                                        path_requirements.as_slice(),
                                                        goal_facts.as_slice(),
                                                    ]
                                                    .concat(),
                                                )?
                                                .focus_fixed_state_goal_with_surface(
                                                    goal.clone(),
                                                    Some(surface_goal.clone()),
                                                )?
                                                .apply_step(ProofStep::Rewrite(
                                                    surface_equality.clone(),
                                                )) {
                                                Ok(proof) => {
                                                    let certificate = proof.certificate();
                                                    rewritten_result = Some((
                                                        proof.goal().cloned(),
                                                        certificate,
                                                        Some(proof),
                                                    ));
                                                    break;
                                                }
                                                Err(error) => last_error = Some(error),
                                            }
                                        }
                                    } else if let Some(fixed_state_root) = &fixed_state_root {
                                        for (goal, goal_facts) in &goal_candidates {
                                            match fixed_state_root
                                                .with_checked_outcome_facts(
                                                    &[
                                                        path_requirements.as_slice(),
                                                        goal_facts.as_slice(),
                                                    ]
                                                    .concat(),
                                                )?
                                                .focus_fixed_state_goal_with_surface(
                                                    goal.clone(),
                                                    Some(surface_goal.clone()),
                                                )?
                                                .apply_step(ProofStep::Rewrite(
                                                    surface_equality.clone(),
                                                )) {
                                                Ok(proof) => {
                                                    rewritten_result = Some((
                                                        proof.goal().cloned(),
                                                        proof.certificate(),
                                                        None,
                                                    ));
                                                    break;
                                                }
                                                Err(error) => last_error = Some(error),
                                            }
                                        }
                                    }
                                    match rewritten_result {
                                        Some((rewritten, certificate, chained)) => {
                                            let rewritten = rewritten.ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked `rewrite` lost its proposition goal"
                                                ))
                                            })?;
                                            retained_certificate.get_or_insert(certificate);
                                            rewritten_claim_goals[claim_index] = Some(rewritten);
                                            if let Some(proof) = chained {
                                                let checkpoint = proof.checkpoint();
                                                rewritten_claim_proofs[claim_index] =
                                                    Some((proof, checkpoint));
                                            }
                                            rewrite_claim_equalities[claim_index]
                                                .push(surface_equality.clone());
                                            rewrote_any = true;
                                        }
                                        None => {
                                            check_verification_deadline()?;
                                            if let Some(error) = last_error {
                                                first_error.get_or_insert_with(|| {
                                                    error.message().to_string()
                                                });
                                            }
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
                                        proof_execution
                                            .presentation
                                            .expansion
                                            .deferred_tactic_capture
                                            .as_ref(),
                                        post_execution_index,
                                        *tactic_index,
                                        tactic,
                                    );
                                }
                            }
                            PostExecutionTactic::If { .. } => unreachable!(
                                "post-execution branch selection must flatten control nodes before checking leaf tactics"
                            ),
                            PostExecutionTactic::Simp => {
                                let capturing_this_tactic = proof_execution
                                    .presentation
                                    .expansion
                                    .deferred_tactic_capture
                                    .as_ref()
                                    .is_some_and(|capture| capture.tactic_index == *tactic_index);
                                // Read the outcome's resources through the
                                // contract's checked transition before closing
                                // claims against it, so a produced or returned
                                // resource is visible to a resource ensure with
                                // no `frame`. The kernel certified this exit
                                // already; a transition that does not apply yet
                                // (an open composite still to fold) leaves the
                                // body's own context in place.
                                if !resource_transition_applied
                                    && matches!(outcome, CFunctionOutcome::Return { .. })
                                    && !crate::kernel::c_function_return_resources_definitionally_established(
                                        pre_state,
                                        function,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                    )
                                {
                                    // The body does not hold what the contract
                                    // returns; the resource ensures report the
                                    // missing fact against the body's context.
                                    pending_resource_transition_error = Some(
                                        "the body outcome does not establish the contract's returned resources"
                                            .to_string(),
                                    );
                                } else if !resource_transition_applied
                                    && matches!(outcome, CFunctionOutcome::Return { .. })
                                {
                                    let mut transitioned = outcome.clone();
                                    match apply_checked_contract_resource_transition(
                                        &mut transitioned,
                                        pre_state,
                                        function,
                                        arguments,
                                        &path_requirements,
                                        &path.execution_facts(),
                                        &proof_label,
                                        path_index,
                                    ) {
                                        Ok(()) => {
                                            outcome = transitioned;
                                            resource_transition_applied = true;
                                            if let Some(evolving) = outcome_proof.take() {
                                                outcome_proof = Some(
                                                    evolving
                                                        .with_outcome_snapshot(&outcome)?
                                                        .with_checked_outcome_facts(
                                                            &path_requirements,
                                                        )?,
                                                );
                                            }
                                        }
                                        Err(error) => {
                                            pending_resource_transition_error =
                                                Some(error.message().to_string());
                                        }
                                    }
                                }
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
                                    closures[claim_index] = match completed.completed_proposition()
                                    {
                                        Ok(checked) => ClaimClosure::by_checked_proposition(
                                            &certificate,
                                            checked,
                                        ),
                                        Err(_) => {
                                            ClaimClosure::by_checked_certificate(&certificate)
                                        }
                                    };
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
                                    for closure in closures.iter_mut().take(claims.len()) {
                                        if closure.is_closed() {
                                            continue;
                                        }
                                        *closure =
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
                                    let direct_supported = true;
                                    for (claim_index, claim) in claims.iter().enumerate() {
                                        if closures[claim_index].is_closed() {
                                            continue;
                                        }
                                        {
                                            let FunctionClaimRef::Ensure(_, ensure_clause) = claim;
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
                                                            rewrite_claim_equalities[claim_index]
                                                                .clone(),
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
                                    if direct_supported && !direct_resource_claims.is_empty() {
                                        let CFunctionOutcome::Return { .. } = &outcome else {
                                            unreachable!("gated on a return outcome above");
                                        };
                                        for (claim_index, resource, borrowed) in
                                            &direct_resource_claims
                                        {
                                            let claim_label = function_claim_label(
                                                function_block.signature().name(),
                                                &claims[*claim_index],
                                            );
                                            if let Err(error) =
                                                crate::surface::checking::prove_ensure_resource(
                                                    &claim_label,
                                                    path_index,
                                                    &path.execution_facts(),
                                                    &path_requirements,
                                                    resource,
                                                    *borrowed,
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
                                            for (claim_index, _, _) in &direct_resource_claims {
                                                closures[*claim_index] =
                                                    ClaimClosure::by_grouped_transition(
                                                        &certificate,
                                                    );
                                            }
                                            path_grouped_surface_closers
                                                .extend(certificate.to_proof_tactics());
                                        } else {
                                            for (claim_index, _, _) in &direct_resource_claims {
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
                                                        Option<(
                                                            ProofCertificate,
                                                            Vec<crate::kernel::proof::CheckedProposition>,
                                                        )>,
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
                                                proof_execution.presentation.surface_record.last_step_entry
                                                    .as_ref(),
                                                &proof_execution.presentation.recorded_snapshots,
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
                                                let detail = match outcome_proof.as_ref() {
                                                    Some(root) => close_claim_directly_from_outcome(
                                                        root,
                                                        function,
                                                        &claims[claim_index],
                                                        pre_state,
                                                        arguments,
                                                        &outcome,
                                                        &path_requirements,
                                                        surface_goal,
                                                        equalities,
                                                        &unfolded_predicates,
                                                        &claim_label,
                                                        path_index,
                                                        parsed_function.parameters(),
                                                        predicate_environment,
                                                        click_function_environment,
                                                    )?
                                                    .err()
                                                    .map(|reason| format!("\n{reason}"))
                                                    .unwrap_or_default(),
                                                    None => String::new(),
                                                };
                                                let transition_detail = pending_resource_transition_error
                                                    .as_ref()
                                                    .map(|error| {
                                                        format!(
                                                            "\nthe contract resource transition did not apply to this outcome: {error}"
                                                        )
                                                    })
                                                    .unwrap_or_default();
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `simp` search did not retain a complete proof for `{claim_label}`{detail}{transition_detail}",
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
                                            (
                                                direct_proof.certificate_since(&direct_base)?,
                                                Vec::new(),
                                            )
                                        } else {
                                            direct_proof.complete_fixed_state_obligations_since(
                                                &direct_base,
                                                &surface_goals,
                                            )?
                                        };
                                        // Keep the checked authority for the original claims,
                                        // but close the rewritten goals in the expanded proof.
                                        // Reflexive residuals need normalization, not assumption.
                                        if proof_context.constants.grouped_contract
                                            && !direct_claims.is_empty()
                                            && direct_claims.iter().all(|(index, _, _)| {
                                                rewritten_claim_proofs[*index]
                                                    .as_ref()
                                                    .is_some_and(|(proof, _)| {
                                                        proof.apply_step(ProofStep::Normalize).is_ok()
                                                    })
                                            })
                                        {
                                            let mut tactics = direct_proof
                                                .certificate_since(&direct_base)?
                                                .to_proof_tactics();
                                            tactics.push(ProofTactic::Normalize);
                                            let certificate = ProofCertificate::from_proof_tactics(&tactics)
                                                .map_err(|error| ClickError::new(format!(
                                                    "checked normalization closure is not simple: {error:?}"
                                                )))?;
                                            return Ok(Some((certificate, completed.1)));
                                        }
                                        Ok(Some(completed))
                                                    };
                                                let outcome = attempt();
                                                let keep = matches!(&outcome, Ok(Some(_)));
                                                (outcome, keep)
                                            })?;
                                        if let Some((certificate, checked_propositions)) =
                                            direct_certificate
                                        {
                                            if checked_propositions.len() != direct_claims.len() {
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: completed proposition authority did not match the checked claim set"
                                                )));
                                            }
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
                                                for ((claim_index, _, _), checked_proposition) in
                                                    direct_claims
                                                        .into_iter()
                                                        .zip(checked_propositions)
                                                {
                                                    closures[claim_index] =
                                                        ClaimClosure::by_grouped_proposition(
                                                            &certificate,
                                                            checked_proposition,
                                                        );
                                                }
                                                for (claim_index, _, _) in &direct_resource_claims {
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
                                                for ((claim_index, _, _), checked_proposition) in
                                                    direct_claims
                                                        .into_iter()
                                                        .zip(checked_propositions)
                                                {
                                                    closures[claim_index] =
                                                        ClaimClosure::by_checked_proposition(
                                                            &certificate,
                                                            checked_proposition,
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
                                                    for (claim_index, _, _) in
                                                        &direct_resource_claims
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
                                let mut reasons = Vec::new();
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let (Some(root), FunctionClaimRef::Ensure(_, ensure_clause)) =
                                        (outcome_proof.as_ref(), claim)
                                    else {
                                        continue;
                                    };
                                    let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                                    else {
                                        continue;
                                    };
                                    let claim_label = function_claim_label(
                                        function_block.signature().name(),
                                        claim,
                                    );
                                    if let Err(reason) = close_claim_directly_from_outcome(
                                        root,
                                        function,
                                        claim,
                                        pre_state,
                                        arguments,
                                        &outcome,
                                        &path_requirements,
                                        surface_goal,
                                        &rewrite_claim_equalities[claim_index],
                                        &unfolded_predicates,
                                        &claim_label,
                                        path_index,
                                        parsed_function.parameters(),
                                        predicate_environment,
                                        click_function_environment,
                                    )? {
                                        reasons.push(reason);
                                    }
                                }
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
                                return Err(ClickError::new(format!(
                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: checked outcome `simp` did not retain a complete transition for every pending claim{detail}",
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
                                closures[claim_index] = ClaimClosure::by_exact_check_completing(
                                    completed.completed_proposition().ok(),
                                );
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
                            // The implicit closer is the direct logical closure
                            // of the claim from the outcome Proof: it records
                            // the completion claim certification matches. The
                            // exact surface checker below remains for claims
                            // that closure does not reach.
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            if let (Some(root), FunctionClaimRef::Ensure(_, ensure_clause)) =
                                (outcome_proof.as_ref(), claim)
                                && let Ensure::Proposition(surface_goal) = ensure_clause.ensure()
                            {
                                match close_claim_directly_from_outcome(
                                    root,
                                    function,
                                    claim,
                                    pre_state,
                                    arguments,
                                    &outcome,
                                    &path_requirements,
                                    surface_goal,
                                    &rewrite_claim_equalities[claim_index],
                                    &unfolded_predicates,
                                    &claim_label,
                                    path_index,
                                    parsed_function.parameters(),
                                    predicate_environment,
                                    click_function_environment,
                                )? {
                                    Ok(completed) => {
                                        closures[claim_index] =
                                            ClaimClosure::by_exact_check_completing(
                                                completed.completed_proposition().ok(),
                                            );
                                    }
                                    Err(reason) => closures[claim_index].record_failure(reason),
                                }
                                continue;
                            }
                            // A resource ensure or an effect claim is an exact
                            // check against the path's outcome, not a proof.
                            let exact = match claim {
                                FunctionClaimRef::Ensure(_, ensure_clause) => {
                                    match ensure_clause.ensure() {
                                        Ensure::Resource(resource) => Some(prove_ensure_resource(
                                            &claim_label,
                                            path_index,
                                            &path.execution_facts(),
                                            &path_requirements,
                                            resource,
                                            ensure_clause.borrowed(),
                                            parsed_function.parameters(),
                                            arguments,
                                            pre_state,
                                            &outcome,
                                        )),
                                        Ensure::Proposition(_) => None,
                                    }
                                }
                            };
                            match exact {
                                Some(Ok(())) => {
                                    closures[claim_index] = ClaimClosure::by_exact_check()
                                }
                                Some(Err(error)) => closures[claim_index]
                                    .record_failure(error.message().to_string()),
                                None if !matches!(outcome, CFunctionOutcome::Return { .. }) => {
                                    closures[claim_index].record_failure(format!(
                                        "`{claim_label}` failed on path {path_index}: {}",
                                        describe_function_outcome(
                                            &outcome,
                                            parsed_function.parameters(),
                                            arguments
                                        )
                                    ))
                                }
                                None => closures[claim_index].record_failure(format!(
                                    "`{claim_label}` has no outcome Proof to close it from"
                                )),
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
                        let closer = "`simp()`";
                        let detail = closures[claim_index]
                            .last_error()
                            .map(|message| format!("\nlast closing attempt:\n{message}"))
                            .unwrap_or_default();
                        return Err(ClickError::new(format!(
                            "`{proof_label}` path {path_index} left `{claim_label}` unproved; use {closer} after establishing the facts and resources it needs (claim index {claim_index}){detail}"
                        )));
                    }

                    // The specification's requirements are the certified path's
                    // own entry premises: exactly what the proof object checked the
                    // path under and what contract certification authorizes
                    // from the contract context before reusing the path, so a
                    // claim completed on the path is bound to premises
                    // certification already holds.
                    // The specification states the certified path's outcome: the
                    // body's under the contract's exit rule, which claim and
                    // contract certification consume. The proof's own outcome
                    // snapshot differs from it only in ghost resource
                    // representation; a claim completed at that snapshot is
                    // bound to the certified path by result, memory, and locals.
                    // Explicit instance folds are checked resource events,
                    // including after C returns. Certify their retained trace
                    // before accepting the resulting ownership representation.
                    let rewritten_path;
                    let certified_path = if has_return_instance_rewrite {
                        let core = &outcome_proof
                            .as_ref()
                            .and_then(Proof::execution)
                            .ok_or_else(|| {
                                ClickError::new("return instance fold lost its checked execution")
                            })?
                            .core;
                        rewritten_path = core
                            .checked_return_path(
                                execution,
                                function,
                                &assumptions_from_propositions(&base_certification_facts),
                                path_index,
                            )
                            .map_err(|message| {
                                ClickError::new(format!(
                                    "could not certify return instance fold: {message}"
                                ))
                            })?;
                        returned_core
                            .collect_return_resource_rewrites(core, path_index)
                            .map_err(ClickError::new)?;
                        any_return_instance_rewrite = true;
                        &rewritten_path
                    } else {
                        completed_execution
                            .paths()
                            .get(certified_path_index)
                            .ok_or_else(|| {
                                ClickError::new(
                                    "return instance fold changed execution path coverage",
                                )
                            })?
                    };
                    let Proposition::CFunctionVerifies {
                        outcome: specification_outcome,
                        ..
                    } = implication_body(certified_path.theorem().proposition())
                    else {
                        return Err(ClickError::new(
                            "return instance fold has no checked function outcome",
                        ));
                    };
                    let specification_outcome = specification_outcome.clone();
                    let specification_requirements = certified_path.assumptions().pure_facts();
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
                certified_path,
            ),
            )
            .ok_or_else(|| {
                ClickError::new(format!(
                    "execution proof for `{proof_label}` path {path_index} does not certify its exact function specification\n  requirements: {}",
                    specification.requires().len()
                ))
            })?;
                    for (claim_index, claim) in claims.iter().enumerate() {
                        let checked_proposition = closures[claim_index]
                            .closed()
                            .and_then(ClosedClaim::checked_proposition)
                            .and_then(|completion| {
                                c_checked_function_proposition(
                                    function,
                                    &specification,
                                    &theorem,
                                    completion,
                                    Some(&outcome),
                                )
                            });
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
                            frontier_loop_clauses: proof_execution
                                .presentation
                                .frontier_loop_clauses
                                .to_vec(),
                            frontier_loop_rules: proof_execution.core.frontier_loop_rules.to_vec(),
                            checked_execution: completed_execution.clone(),
                            checked_proposition,
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
                    for mut choice in selected_post_choices {
                        choice.tactic_offset = path_surface_post_tactics.len();
                        surface_post_choices.push(choice);
                    }
                    surface_post_choices_by_path.push(surface_post_choices);
                    surface_post_tactics_by_path.push(path_surface_post_tactics);
                    let implicitly_closable = path_deferred_capture_tactics.is_empty()
                        || (!require_explicit_closers
                            && claims
                                .iter()
                                .enumerate()
                                .all(|(claim_index, claim)| match claim {
                                    FunctionClaimRef::Ensure(_, ensure_clause)
                                        if matches!(
                                            ensure_clause.ensure(),
                                            Ensure::Proposition(_)
                                        ) =>
                                    {
                                        closures[claim_index].is_closed()
                                    }
                                    _ => true,
                                }));
                    if visits_selected_capture {
                        implicit_closure_by_path.push(implicitly_closable);
                        deferred_capture_tactics_by_path.push(path_deferred_capture_tactics);
                        deferred_capture_branches_by_path.push(deferred_capture_branch_path);
                    }
                    drop(_path_certification_timing);
                }
                Ok(())
            },
        )?;
        if any_return_instance_rewrite {
            let completed = returned_core
                .checked_function_execution(
                    execution,
                    function,
                    assumptions_from_propositions(&base_certification_facts),
                    function_environment.clone(),
                    execution_semantics,
                    execution_mode,
                )
                .map_err(|message| {
                    ClickError::new(format!("could not certify all return folds: {message}"))
                })?;
            for theorem in &mut verified {
                theorem.checked_execution = completed.clone();
            }
        }
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
            if surface_post_choices_by_path
                .iter()
                .any(|choices| !choices.is_empty())
            {
                match synthesize_post_execution_paths(
                    &surface_post_tactics_by_path,
                    &surface_grouped_closers_by_path,
                    &surface_post_choices_by_path,
                ) {
                    Ok(suffix) => {
                        for step in suffix {
                            append_surface_step_to_leaves(&mut expanded.steps, step);
                        }
                    }
                    Err(message) => expanded.block(message),
                }
            } else {
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
                    && let Err(message) = append_surface_tactics(
                        &mut expanded.steps,
                        &surface_grouped_closers_by_path,
                    )
                {
                    expanded.block(message);
                }
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
            let Some(deferred) = proof_execution
                .presentation
                .expansion
                .deferred_tactic_capture
                .as_ref()
            else {
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
                        .all(Option::is_none)
                    && implicit_closure_by_path.iter().all(|closable| *closable));
            if !contributes_no_tactics && path_independent_capture {
                // Every path produced the same checked expansion. It stands
                // at the selected source site, including inside an existing
                // proof branch. Repeating that branch here could evaluate a
                // caller local after return, when it is no longer in scope.
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
    fn deferred_cases_retain_prefixes_closers_and_duplicate_execution_paths() {
        let condition = ClickProposition::PredicateCall {
            name: "P".into(),
            arguments: vec![],
        };
        let choices = [true, true, false, false].map(|value| {
            vec![SurfacePathChoice {
                occurrence: 7,
                condition: condition.clone(),
                value,
                tactic_offset: 1,
            }]
        });
        let tactics = [true, true, false, false].map(|value| {
            vec![
                ProofTactic::Step,
                if value {
                    ProofTactic::Assumption
                } else {
                    ProofTactic::Normalize
                },
            ]
        });
        let closers = vec![vec![ProofTactic::Normalize]; 4];
        let steps = synthesize_post_execution_paths(&tactics, &closers, &choices).unwrap();
        let [
            ProofStep::Step,
            ProofStep::If {
                condition: actual,
                then_proof,
                else_proof,
            },
        ] = steps.as_slice()
        else {
            panic!("deferred branch lost its shared prefix");
        };
        assert_eq!(actual, &condition);
        assert_eq!(
            then_proof.steps(),
            &[ProofStep::Assumption, ProofStep::Normalize]
        );
        assert_eq!(
            else_proof.steps(),
            &[ProofStep::Normalize, ProofStep::Normalize]
        );
        let mut mismatched = tactics;
        mismatched[1][0] = ProofTactic::Normalize;
        assert!(synthesize_post_execution_paths(&mismatched, &closers, &choices).is_err());
    }

    #[test]
    fn unsupported_shape_diagnostic_names_route_and_tactic() {
        // Do not let a decline recorded by another proof attempt leak into
        // this direct diagnostic-unit test.
        take_driver_declines();
        let error = unsupported_proof_shape(
            "f.ensures_0",
            false,
            &[ProofTactic::Induct {
                parameter: "n".to_string(),
                hypothesis: "ih".to_string(),
            }],
        );

        assert!(error.message().contains("single-claim proof driver"));
        assert!(error.message().contains("tactic 0 (`induction`)"));
        assert!(error.message().contains("proof-shape limitation"));
        assert!(!error.message().contains("proof shape is not accepted"));
    }

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
