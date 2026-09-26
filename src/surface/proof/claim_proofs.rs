use super::proof_object::ProofCheckpoint;
use super::*;
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

/// Counted-population nonemptiness is a post-transition fact.  Keep its
/// obligation alive until result-aware post-execution tactics have had a
/// chance to prove it; all other path obligations still use the earlier
/// boundary check.
fn post_execution_population_obligation(obligation: &ProofObligation) -> bool {
    matches!(
        obligation.context(),
        Some("resource population remains nonempty" | "resource population body is active")
    )
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
                    selector: SurfacePathSelector::Proposition(condition.clone()),
                    value,
                    tactic_offset: selected.len(),
                });
                let arm = if value { then_tactics } else { else_tactics };
                select_checked_post_execution_tactics(proof, arm, selected, choices)?;
            }
            PostExecutionTactic::CallOutcomes {
                returned_tactics,
                threw_tactics,
            } => {
                let returned = proof.checked_call_returned()?;
                choices.push(SurfacePathChoice {
                    occurrence: deferred.source_index,
                    selector: SurfacePathSelector::CallOutcome,
                    value: returned,
                    tactic_offset: selected.len(),
                });
                let arm = if returned {
                    returned_tactics
                } else {
                    threw_tactics
                };
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
                .into_steps();
            steps.extend(
                ProofCertificate::from_proof_tactics(closers)
                    .map_err(|error| format!("post-execution closer is not simple: {error:?}"))?
                    .into_steps(),
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
        let suffix = synthesize_post_execution_paths(
            &select(tactics, &members),
            &select(closers, &members),
            &select(choices, &members),
        )?;
        append_surface_steps_at_step_branch_path(steps, &branch_path, suffix)?;
    }
    Ok(())
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
            ProofTactic::CallOutcomes(_) => "`outcomes`",
            ProofTactic::Loop(_) => "loop proof",
            ProofTactic::ConstructResource(_) => "resource construction",
            ProofTactic::Witness(_) => "`witness`",
            ProofTactic::Choose(_) => "`choose`",
            // `arithmetic()` closes a focused proposition goal. Between
            // execution steps there is no such goal, so name the tactic and
            // let the shared rewrite hint point at `have ... by { ... }`.
            ProofTactic::ArithmeticUsing(_) => "`arithmetic()`",
            ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::ApplyInductionUsing { .. } => "induction",
            _ => return None,
        };
        Some((index, shape))
    })
}

/// How deeply a tactic sequence nests execution regions: every `match`,
/// `branch`, or proof `if` written inside another one is one level. This is
/// the number the checked drivers bound, so a proof past the bound is told
/// what the bound is instead of being declined without a reason.
fn proof_region_nesting_depth(tactics: &[ProofTactic]) -> usize {
    fn arms_depth(arms: &[&[ProofTactic]]) -> usize {
        1 + arms
            .iter()
            .map(|arm| proof_region_nesting_depth(arm))
            .max()
            .unwrap_or(0)
    }
    tactics
        .iter()
        .map(|tactic| match tactic {
            ProofTactic::Match(proof_match) => arms_depth(
                &proof_match
                    .arms
                    .iter()
                    .map(|arm| arm.tactics.as_slice())
                    .collect::<Vec<_>>(),
            ),
            ProofTactic::Branch(branch) => {
                arms_depth(&[&branch.then_tactics, &branch.else_tactics])
            }
            ProofTactic::If(proof_if) => {
                arms_depth(&[&proof_if.then_tactics, &proof_if.else_tactics])
            }
            _ => 0,
        })
        .max()
        .unwrap_or(0)
}

/// The diagnostic for a proof whose written regions nest past the bound the
/// checked drivers accept, or `None` within the bound. Verification reports
/// it when the drivers decline such a proof; expansion refuses a rewrite with
/// the same diagnostic before emitting it.
pub(in crate::surface) fn proof_region_nesting_bound_error(
    proof_label: &str,
    tactics: &[ProofTactic],
) -> Option<ClickError> {
    let nesting = proof_region_nesting_depth(tactics);
    (nesting > MAX_CHECKED_PROOF_REGION_NESTING).then(|| {
        ClickError::new(format!(
            "`{proof_label}`: this proof nests {nesting} execution regions; the checked proof drivers support at most {MAX_CHECKED_PROOF_REGION_NESTING}. Move an inner `match`, `branch`, or proof `if` into a contracted helper, or prove part of it in a `have`."
        ))
    })
}

fn diagnostic_claim_label(function_name: &str, claim: &FunctionClaimRef<'_>) -> String {
    let label = function_claim_label(function_name, claim);
    match claim.clause().ensure() {
        Ensure::Resource(resource) => {
            let verb = if claim.clause().borrowed() {
                "owns"
            } else {
                "produces"
            };
            format!(
                "{function_name}.{verb}: {}",
                crate::surface::validation::describe_resource_clause(resource)
            )
        }
        Ensure::Proposition(proposition) => format!(
            "{label}: {}",
            crate::surface::diagnostics::describe_click_proposition(proposition)
        ),
    }
}

fn unsupported_proof_shape(
    proof_label: &str,
    grouped: bool,
    claim_labels: &[String],
    tactics: &[ProofTactic],
) -> ClickError {
    // The decline records are internal bookkeeping. Consume them here so a
    // later diagnostic does not inherit stale state, but do not expose the
    // driver topology to users.
    let _ = take_driver_declines();
    let depth_declined = take_region_depth_decline();
    let short_of_exit = take_short_of_exit_decline();
    let declined_operation = take_declined_operation();
    if let Some(error) = proof_region_nesting_bound_error(proof_label, tactics) {
        return error;
    }
    if let Some(reason) = declined_operation {
        // The drivers stopped at a written operation they refused for a
        // stated reason, such as an `apply` whose premise is missing. That
        // reason is the actionable part; the proof shape is not at fault.
        return ClickError::new(format!("`{proof_label}`: {reason}"));
    }
    if depth_declined {
        // The written nesting is within the bound, so the depth the driver
        // reached came from running the rest of the proof inside a
        // continuing arm. Say so, rather than calling the shape unsupported.
        return ClickError::new(format!(
            "`{proof_label}`: this proof nests execution regions more deeply than the checked proof drivers support, at most {MAX_CHECKED_PROOF_REGION_NESTING}. When one arm of a `branch` or call outcome returns and the other continues, or a proof `if` case continues past its arm, the proof after that split runs inside the continuing arm, one region deeper. Move an inner `match`, `branch`, or proof `if` into a contracted helper, or prove part of it in a `have`."
        ));
    }
    if short_of_exit {
        // The written shape is supported; what stopped the drivers is a path
        // the proof left open. Say which, rather than calling the shape
        // unimplemented, since the fix is in the proof script.
        return ClickError::new(format!(
            "`{proof_label}`: a `branch` or proof `if` split the path, one arm returned, and the tactics after the split ran out before the continuing arm reached the function exit, so that path is still open. The proof after the split runs inside the continuing arm; finish it there (for example with `execute();` and `simp();`), or check the continuation's last tactics."
        ));
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
    let shape = proof_shape_hint(tactics).map_or_else(
        || "the supplied tactic sequence".to_string(),
        |(index, shape)| format!("tactic {index} ({shape})"),
    );
    let rewrite = if grouped {
        "Every terminal path must establish every listed claim. If `step()` reaches a maybe-throwing call, use `outcomes { returned { ... } threw { ... } }` to handle its two successors. For proposition-only work, move the operation into `have proposition by { ... }`."
    } else {
        "If `step()` reaches a maybe-throwing call, use `outcomes { returned { ... } threw { ... } }` to handle its two successors. For proposition-only work, move the operation into `have proposition by { ... }`."
    };
    ClickError::new(format!(
        "`{proof_label}`: the proof script is valid, but the verifier cannot yet certify it for {claim_description}. It reached {shape}, which is not implemented in this execution context. No listed claim was shown false. {rewrite}"
    ))
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
    let _local_layouts =
        super::surface_synthesis::LocalStructLayoutScope::enter(parsed_function, function_block);
    let program = build_internal_proof_with_source(tactics, claim_label, tactic_source)?;
    let generated_by_source_index = match tactic_source {
        ProofTacticSource::SourceSyntax => None,
        ProofTacticSource::GeneratedBy { source_index } => Some(source_index),
    };
    let caller_source_owner =
        CallerSourceOwnerId::ordinary(source_path, function_block.signature().name());
    let InitialClaimContext {
        state,
        arguments,
        pure_facts,
        entry_fact_origins,
        surface_propositions,
    } = initial_claim_context_with_caller_owner(
        function_block,
        parsed_function,
        resource_environment,
        predicate_environment,
        click_function_environment,
        claim_label,
        Some(&caller_source_owner),
    )?;
    let caller_requirement_index = CallerRequirementIndex::from_entry_facts(
        caller_source_owner.clone(),
        function_block,
        parsed_function.parameters(),
        &pure_facts,
        &entry_fact_origins,
        crate::kernel::CMemorySnapshotIdentity::of(state.memory()),
    );
    let function = annotated_function_with_assumptions(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        Some(ResourceFrameEntry {
            assumptions: &assumptions_from_propositions(&pure_facts),
            checked_entry_state: None,
        }),
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
    let state = install_borrowed_contract_inputs(
        state,
        &function,
        &arguments,
        &pure_facts,
        parsed_function.parameters(),
        claim_label,
    )?;
    let function_entry_state =
        c_function_entry_state(&state, &function, &arguments).ok_or_else(|| {
            ClickError::new(format!("`{claim_label}` could not bind function arguments"))
        })?;
    // The proof of a function that declares an expression `decreases` measure
    // steps under that function's recursion anchor, which is what makes a
    // self-call raise the descent obligations. Certification derives the same
    // anchor for itself and reuses only an artifact whose environment carries
    // it, so this is not a step the proof may skip: without it the completed
    // execution is refused.
    let anchored_function_environment =
        crate::kernel::c_execution_environment_with_recursion_anchor(
            function_environment.clone(),
            &function,
            &state,
            &arguments,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    let function_environment = &anchored_function_environment;
    let proof_claims = [*claim];
    let constants = ExecutionProofConstants {
        proof_site: proof_site_for_claims(function_block, &proof_claims, false),
        source_layout: SourceExecutionLayout::for_function(parsed_function)?,
        execution_start_facts: Arc::new(pure_facts.clone()),
        entry_fact_origins: Arc::new(entry_fact_origins),
        caller_requirement_index: Arc::new(caller_requirement_index),
        caller_source_owner: Some(caller_source_owner),
        function_entry_state: Some(function_entry_state),
        function_source_registry,
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
    // A decline recorded by an earlier claim's attempt, which another driver
    // then satisfied, must not colour this claim's diagnostic.
    let _ = take_driver_declines();
    let _ = take_region_depth_decline();
    let _ = take_short_of_exit_decline();
    let _ = take_declined_operation();
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
    let claim_labels = [diagnostic_claim_label(
        function_block.signature().name(),
        claim,
    )];
    Err(unsupported_proof_shape(
        claim_label,
        false,
        &claim_labels,
        tactics,
    ))
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
    function_source_registry: Arc<FunctionSourceRegistry>,
    tactics: &[ProofTactic],
    tactic_source: ProofTacticSource,
) -> Result<ClaimProofResult, ClickError> {
    let proof_label = format!("{}.contract", function_block.signature().name());
    let _local_layouts =
        super::surface_synthesis::LocalStructLayoutScope::enter(parsed_function, function_block);
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
    let program = build_internal_proof_with_source(tactics, &proof_label, tactic_source)?;
    let generated_by_source_index = match tactic_source {
        ProofTacticSource::SourceSyntax => None,
        ProofTacticSource::GeneratedBy { source_index } => Some(source_index),
    };
    let caller_source_owner =
        CallerSourceOwnerId::ordinary(source_path, function_block.signature().name());
    let InitialClaimContext {
        state,
        arguments,
        pure_facts,
        entry_fact_origins,
        surface_propositions,
    } = initial_claim_context_with_caller_owner(
        function_block,
        parsed_function,
        resource_environment,
        predicate_environment,
        click_function_environment,
        &proof_label,
        Some(&caller_source_owner),
    )?;
    let caller_requirement_index = CallerRequirementIndex::from_entry_facts(
        caller_source_owner.clone(),
        function_block,
        parsed_function.parameters(),
        &pure_facts,
        &entry_fact_origins,
        crate::kernel::CMemorySnapshotIdentity::of(state.memory()),
    );
    let function = annotated_function_with_assumptions(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        Some(ResourceFrameEntry {
            assumptions: &assumptions_from_propositions(&pure_facts),
            checked_entry_state: None,
        }),
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
    let state = install_borrowed_contract_inputs(
        state,
        &function,
        &arguments,
        &pure_facts,
        parsed_function.parameters(),
        &proof_label,
    )?;
    let function_entry_state =
        c_function_entry_state(&state, &function, &arguments).ok_or_else(|| {
            ClickError::new(format!("`{proof_label}` could not bind function arguments"))
        })?;
    // Same anchor as the single-claim route; see `prove_claim_by_tactics`.
    let anchored_function_environment =
        crate::kernel::c_execution_environment_with_recursion_anchor(
            function_environment.clone(),
            &function,
            &state,
            &arguments,
        )
        .map_err(|message| ClickError::new(format!("`{proof_label}`: {message}")))?;
    let function_environment = &anchored_function_environment;
    let constants = ExecutionProofConstants {
        proof_site: proof_site_for_claims(function_block, claims, true),
        source_layout: SourceExecutionLayout::for_function(parsed_function)?,
        execution_start_facts: Arc::new(pure_facts.clone()),
        entry_fact_origins: Arc::new(entry_fact_origins),
        caller_requirement_index: Arc::new(caller_requirement_index),
        caller_source_owner: Some(caller_source_owner),
        function_entry_state: Some(function_entry_state),
        function_source_registry,
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
    // A decline recorded by an earlier claim's attempt, which another driver
    // then satisfied, must not colour this claim's diagnostic.
    let _ = take_driver_declines();
    let _ = take_region_depth_decline();
    let _ = take_short_of_exit_decline();
    let _ = take_declined_operation();
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
    let claim_labels = claims
        .iter()
        .map(|claim| diagnostic_claim_label(function_block.signature().name(), claim))
        .collect::<Vec<_>>();
    Err(unsupported_proof_shape(
        &proof_label,
        true,
        &claim_labels,
        tactics,
    ))
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
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut tactics = vec![ProofTactic::SmartExecute];
    if !claims.is_empty() {
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
        function_source_registry,
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
    function_source_registry: Arc<FunctionSourceRegistry>,
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
        Vacuous(&'e CCheckedFunctionExecution),
    }

    #[derive(Clone)]
    pub(super) struct ClosedClaim<'e> {
        key: CFunctionContractClaimKey,
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
        pub(super) fn checked_proposition(
            &self,
        ) -> Option<&crate::kernel::proof::CheckedProposition> {
            match &self.evidence {
                ClaimEvidence::Proposition(checked) => Some(checked),
                _ => None,
            }
        }
        pub(super) fn checked_resource_claim_key(&self) -> Option<&CFunctionContractClaimKey> {
            match &self.evidence {
                ClaimEvidence::Resource(checked) => Some(checked.claim_key()),
                _ => None,
            }
        }
        pub(super) fn checked_resource_claim_resources(
            &self,
        ) -> Option<&crate::kernel::ResourceContext> {
            match &self.evidence {
                ClaimEvidence::Resource(checked) => Some(checked.returned_resources()),
                _ => None,
            }
        }
        pub(super) fn contributes_checked_resource_claim_resources(&self) -> bool {
            match &self.evidence {
                ClaimEvidence::Resource(checked) => checked.contributes_returned_resources(),
                _ => false,
            }
        }
        pub(super) fn defers_checked_resource_transition(&self) -> bool {
            match &self.evidence {
                ClaimEvidence::Resource(checked) => checked.defers_resource_transition(),
                _ => false,
            }
        }
        pub(super) fn checked_resource_claim_has_grouped_transition(&self) -> bool {
            matches!(
                (&self.evidence, &self.certificate),
                (
                    ClaimEvidence::Resource(_),
                    ClaimCertificate::GroupedTransition
                )
            )
        }
        pub(super) fn validate_for(
            &self,
            execution: &CCheckedFunctionExecution,
            path_index: usize,
            key: &CFunctionContractClaimKey,
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
            execution: &CCheckedFunctionExecution,
            path_index: usize,
            key: &CFunctionContractClaimKey,
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

        pub(super) fn by_checked_proposition(
            key: CFunctionContractClaimKey,
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
            key: CFunctionContractClaimKey,
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
            key: CFunctionContractClaimKey,
            path_index: usize,
            checked: crate::kernel::proof::CheckedProposition,
        ) -> Self {
            Self::proposition(key, path_index, ClaimCertificate::ExactCheck, checked)
        }
        fn proposition(
            key: CFunctionContractClaimKey,
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
            execution: &'e CCheckedFunctionExecution,
            path_index: usize,
            key: CFunctionContractClaimKey,
            certificate: ClaimCertificate,
        ) -> Result<Self, ClickError> {
            let path = execution
                .paths()
                .get(path_index)
                .ok_or_else(|| ClickError::new("vacuous claim has no checked path"))?;
            let Proposition::CFunctionVerifies { outcome, .. } =
                implication_body(path.theorem().proposition())
            else {
                return Err(ClickError::new(
                    "vacuous claim has no checked function outcome",
                ));
            };
            if !matches!(
                (&key, outcome),
                (_, CFunctionOutcome::VerificationDiverges)
                    | (
                        CFunctionContractClaimKey::Ensure(_),
                        CFunctionOutcome::Throw { .. }
                    )
                    | (
                        CFunctionContractClaimKey::ExceptionalEnsure(_),
                        CFunctionOutcome::Return { .. }
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
    let mut goals = match claim {
        FunctionClaimRef::Ensure(source_index, _) => {
            let contract_index =
                function
                    .contract_claims()
                    .iter()
                    .find_map(|contract_claim| {
                        match (contract_claim.key(), contract_claim.target()) {
                            (
                                CFunctionContractClaimKey::Ensure(index),
                                CFunctionContractClaimTarget::EnsureProposition(contract_index),
                            ) if index == source_index => Some(*contract_index),
                            _ => None,
                        }
                    })?;
            crate::kernel::c_function_ensure_goals(
                function,
                contract_index,
                pre_state,
                arguments,
                outcome,
                assumptions,
                unfolded_predicates,
            )?
        }
        FunctionClaimRef::ExceptionalEnsure(source_index, _) => {
            let contract_index =
                function
                    .contract_claims()
                    .iter()
                    .find_map(|contract_claim| {
                        match (contract_claim.key(), contract_claim.target()) {
                            (
                                CFunctionContractClaimKey::ExceptionalEnsure(index),
                                CFunctionContractClaimTarget::ExceptionalEnsureProposition(
                                    contract_index,
                                ),
                            ) if index == source_index => Some(*contract_index),
                            _ => None,
                        }
                    })?;
            crate::kernel::c_function_exceptional_ensure_goals(
                function,
                contract_index,
                pre_state,
                arguments,
                outcome,
                assumptions,
            )?
        }
    };
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
fn required_outcome<'p, 'a>(root: &'p Option<Proof<'a>>) -> Result<&'p Proof<'a>, ClickError> {
    root.as_ref()
        .ok_or_else(|| ClickError::new("operation requires a retained outcome Proof"))
}

fn focus_claim_goal<'a>(
    root: &Proof<'a>,
    kernel_goal: Option<(Proposition, Vec<Proposition>)>,
    surface_goal: &ClickProposition,
) -> Result<Proof<'a>, ClickError> {
    match kernel_goal {
        Some((goal, facts)) => root.focus_lowered_outcome_claim(goal, &facts, surface_goal),
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
            if !claim.applies_to(outcome) {
                return None;
            }
            let ensure_clause = claim.clause();
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

    let root = outcome_root.clone();
    let kernel_goal = kernel_claim_goal(
        function,
        &claims[claim_index],
        pre_state,
        arguments,
        outcome,
        root.facts().assumptions(),
        &[],
    );
    let mut proof = focus_claim_goal(&root, kernel_goal, &surface_goal)?;
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
/// evaluated to and the checked proof context. The context is reported, not a
/// guess at which step was missing.
#[allow(clippy::too_many_arguments)]
fn close_claim_directly_from_outcome<'a>(
    outcome_root: &Proof<'a>,
    function: &CFunction,
    claim: &FunctionClaimRef<'_>,
    pre_state: &CState,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    surface_goal: &ClickProposition,
    rewrite_equalities: &[ClickProposition],
    unfolded_predicates: &[String],
    claim_label: &str,
    path_index: usize,
    parameters: &[syntax::C0Parameter],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Result<Proof<'a>, ClickError>, ClickError> {
    let surface = describe_click_proposition(surface_goal);
    let failure = |reason: String| {
        Ok(Err(ClickError::new(format!(
            "`ensures {surface}` failed for `{claim_label}` path {path_index}: {reason}"
        ))))
    };
    if !claim.applies_to(outcome) {
        return failure(describe_function_outcome(outcome, parameters, arguments));
    }
    let root = outcome_root.clone();
    let kernel_goal = kernel_claim_goal(
        function,
        claim,
        pre_state,
        arguments,
        outcome,
        root.facts().assumptions(),
        &[],
    );
    let mut proof = match focus_claim_goal(&root, kernel_goal, surface_goal) {
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
    let mut search = super::attempt::search_scope("claim outcome closure");
    if let Some(completed) = proof.try_direct_logical_closure()?
        && completed.is_complete()
    {
        search.succeed();
        return Ok(Ok(completed));
    }
    if let Some(completed) = proof.try_simp_closure()?
        && completed.is_complete()
    {
        search.succeed();
        return Ok(Ok(completed));
    }
    check_verification_deadline()?;
    // A comparison reports what each side evaluates to at the outcome, by
    // the same kernel evaluation every proof-side expression gets. Two
    // distinct load variables over one address render identically, so that
    // case names the surface spellings and which snapshot each reads.
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
                (Some(kernel_left), Some(kernel_right)) => {
                    let rendered_left = describe_c_value(&kernel_left, parameters, arguments);
                    let rendered_right = describe_c_value(&kernel_right, parameters, arguments);
                    // Which state a side reads, as the reader would name it.
                    // Both branches below need it: one to say the two sides
                    // read different snapshots, the other to say what a value
                    // may have changed *since*.
                    let snapshot_role = |expression: &ContractExpression| {
                        if contains_old_expression(expression) {
                            "function entry"
                        } else if contains_at_expression(expression) {
                            "a recorded snapshot"
                        } else {
                            "the outcome state"
                        }
                    };
                    if rendered_left == rendered_right && kernel_left != kernel_right {
                        let surface_left = describe_contract_expression(left);
                        let surface_right = describe_contract_expression(right);
                        let left_role = snapshot_role(left);
                        let right_role = snapshot_role(right);
                        let snapshot_note = if left_role == right_role {
                            format!("`{surface_left}` and `{surface_right}` both read {left_role}")
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
                            parameters,
                            arguments,
                        )
                        .map(|mismatch| format!("; {mismatch}"))
                        .unwrap_or_default();
                        format!(
                            "; the two sides read the same address in different memory snapshots ({snapshot_note}){tracked}"
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
                        let model_field = |value: &CValue, role: &str| {
                            describe_model_field_mismatch(
                                value,
                                state,
                                pre_state,
                                if role == "the outcome state" {
                                    "function entry"
                                } else {
                                    role
                                },
                                parameters,
                                arguments,
                            )
                        };
                        let unseparated =
                            describe_unseparated_write(&kernel_left, parameters, arguments)
                                .or_else(|| {
                                    describe_unseparated_write(&kernel_right, parameters, arguments)
                                })
                                .or_else(|| {
                                    model_field(&kernel_left, snapshot_role(left))
                                        .or_else(|| {
                                            model_field(&kernel_right, snapshot_role(right))
                                        })
                                        .map(|mismatch| format!("; {mismatch}"))
                                })
                                // A `count(..)` side is a population, whose
                                // version is the count the state holds.
                                .or_else(|| {
                                    describe_population_mismatch(
                                        left,
                                        state,
                                        pre_state,
                                        "function entry",
                                        parameters,
                                        arguments,
                                    )
                                    .or_else(|| {
                                        describe_population_mismatch(
                                            right,
                                            state,
                                            pre_state,
                                            "function entry",
                                            parameters,
                                            arguments,
                                        )
                                    })
                                    .map(|mismatch| format!("; {mismatch}"))
                                })
                                .unwrap_or_default();
                        format!(
                            "; left side evaluated to {rendered_left}, right side evaluated to {rendered_right}{unseparated}"
                        )
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
    let resource_facts: &[CResourceFact] = match outcome {
        CFunctionOutcome::Return { state, .. } | CFunctionOutcome::Throw { state, .. } => {
            state.resources().facts()
        }
        CFunctionOutcome::VerificationDiverges
        | CFunctionOutcome::UndefinedBehavior(_)
        | CFunctionOutcome::RuntimeError(_) => &[],
    };
    let context = describe_proof_context(
        &root.facts().propositions().cloned().collect::<Vec<_>>(),
        resource_facts,
        parameters,
        arguments,
        &[],
    );
    let error = proof.step_error(format!(
        "`ensures {surface}` failed for `{claim_label}` path {path_index}: unclosed goal: {surface}{evaluated_sides}\n{context}"
    ));
    Ok(Err(error.with_search_failures(search.finish())))
}

/// Serializes a completed existential claim Proof in the established
/// independently-checkable surface form. This is extraction only: the body
/// has already discharged the claim, and this certificate is never applied
/// during ordinary verification.
fn outcome_existence_surface_certificate(
    surface_goal: ClickProposition,
    completed: &Proof<'_>,
) -> Result<ProofCertificate, ClickError> {
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

pub(super) fn finish_ordered_proof<'a>(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof: Proof<'a>,
    source_path: &str,
    function_block: &std::sync::Arc<FunctionBlock>,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    require_explicit_closers: bool,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    _theorem_environment: &TheoremEnvironment,
    function_environment: &CExecutionEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    certificate_tactics: &std::sync::Arc<[ProofTactic]>,
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
    let (outcome_substrate, _) = proof.split_function_outcomes()?;
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
                predicate_environment,
                click_function_environment,
                resource_environment,
                Some(ResourceFrameEntry {
                    assumptions: &assumptions_from_propositions(entry_pure_facts.as_slice()),
                    checked_entry_state: proof_context.constants.function_entry_state.as_ref(),
                }),
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
            frontier_function_block
                .as_ref()
                .unwrap_or(&**function_block),
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
        completed_execution
            .paths()
            .iter()
            .try_for_each(|path| match implication_body(path.theorem().proposition()) {
                Proposition::CFunctionVerifies {
                    state,
                    function: proved_function,
                    arguments: proved_arguments,
                    ..
                } if state == pre_state
                    && proved_function == function
                    && proved_arguments == arguments =>
                {
                    Ok(())
                }
                proposition => Err(ClickError::new(format!(
                    "completion for `{proof_label}` produced an inexact theorem body {proposition:?}"
                ))),
            })?;
        // The completed paths are the proof's candidates in order, so each
        // candidate's certified path is its own index. A candidate the
        // Proof-owned outcome derivation rejected under an exact
        // contradictory path fact owns no goal and is not finished.
        let certified_path_for_proof: Vec<Option<usize>> = (0..execution.paths().len())
            .map(|path_index| {
                let rejected = !matches!(
                    execution.paths()[path_index].outcome(),
                    CFunctionOutcome::VerificationDiverges
                ) && outcome_substrate
                    .outcome_branch_for_path(path_index)
                    .is_none();
                (!rejected).then_some(path_index)
            })
            .collect();
        let mut verified = Vec::new();
        let mut checked_resource_claims_by_path =
            vec![Vec::<CFunctionContractClaimKey>::new(); execution.paths().len()];
        let mut checked_resource_transitions_by_path = vec![false; execution.paths().len()];
        let mut checked_returned_resources_by_path =
            vec![crate::kernel::ResourceContext::new(); execution.paths().len()];
        let mut returned_core = proof_execution.core.clone();
        let mut any_return_instance_rewrite = false;
        let mut surface_closers_by_claim = vec![Vec::new(); claims.len()];
        let mut surface_grouped_closers_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_choices_by_path = Vec::with_capacity(execution.paths().len());
        let mut surface_post_path_indices = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_tactics_by_path = Vec::with_capacity(execution.paths().len());
        let mut deferred_capture_branches_by_path = Vec::with_capacity(execution.paths().len());
        // Whether the implicit exact closer of a single-claim proof would
        // have discharged every open proposition claim on the path without
        // surface tactics. Consulted only when the captured expansions
        // disagree across paths (see the stitch below).
        let mut implicit_closure_by_path = Vec::with_capacity(execution.paths().len());

        // Every theorem below carries this one execution until the finished
        // execution replaces it for all of them at once.
        let provisional_checked_execution = std::sync::Arc::new(completed_execution.clone());
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
                    let path_base_facts = proof_execution
                        .core
                        .pending_exceptional_pure_facts(path_index)
                        .cloned()
                        .unwrap_or_else(|| proof.facts().clone());
                    let missing_obligations = crate::instrumentation::measure_operation(
                        function_block.signature().name(),
                        &proof_label,
                        "path obligation lookup",
                        || {
                            path.obligations()
                                .iter()
                                .filter(|obligation| {
                                    if post_execution_population_obligation(obligation) {
                                        return false;
                                    }
                                    !exact_fact_is_available(
                                        obligation.proposition(),
                                        &path_base_facts,
                                    )
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
                                &path_base_facts.to_vec(),
                                pre_state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                path.facts()
                            )
                        )));
                    }
                    let mut outcome = path.outcome().clone();
                    let mut outcome_proof = if matches!(
                        outcome,
                        CFunctionOutcome::VerificationDiverges
                    ) {
                        None
                    } else {
                        let goal = outcome_substrate.outcome_branch_for_path(path_index).ok_or_else(|| ClickError::new(
                            format!("`{proof_label}` path {path_index}: missing checked outcome goal")))?;
                        outcome_substrate
                            .focus_branch(goal)?
                            .prepare_outcome_cases()?
                    };
                    if outcome_proof.is_none()
                        && !matches!(outcome, CFunctionOutcome::VerificationDiverges)
                    {
                        continue 'execution_path;
                    }
                    let path_requirements = outcome_proof
                        .as_ref()
                        .map_or_else(|| proof.facts().clone(), |root| root.facts().clone());
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
                    if let Some(mut root) = outcome_proof.take() {
                        for name in &unfolded_predicates {
                            if let Ok(unfolded) =
                                root.apply_step(ProofStep::UnfoldPredicate(name.clone()))
                            {
                                root = unfolded;
                            } else {
                                check_verification_deadline()?;
                            }
                        }
                        outcome_proof = Some(root.project_outcome_resources()?);
                    }
                    if let Some(root) = outcome_proof.take() {
                        let root = root.with_contract_return_counts(&completed_execution)?;
                        outcome = root.focused_outcome_snapshot()?;
                        outcome_proof = Some(root);
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
                    let mut rewritten_claim_goals = vec![None::<Proposition>; claims.len()];
                    let mut outcome_surface_propositions =
                        proof_execution.presentation.surface_propositions.clone();
                    // The ordered surface equalities each claim's goal was
                    // rewritten through, parallel to `rewritten_claim_goals`.
                    // The direct Simp path checks them inside its checked
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
                    let mut existence_proof = None;
                    let mut has_return_instance_rewrite = false;
                    // Frame closure also applies the contract's returned
                    // resource transition. Track that ownership transition
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
                            && let Ok(transitioned) = required_outcome(&outcome_proof)?
                                .apply_outcome_contract_resources(pre_state, function)
                        {
                            outcome = transitioned.focused_outcome_snapshot()?;
                            resource_transition_applied = true;
                            outcome_proof = Some(transitioned);
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
                        let path_requirements = outcome_proof
                            .as_ref()
                            .map_or_else(|| proof.facts().clone(), |root| root.facts().clone());
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
                        outcome_proof =
                            outcome_proof.map(|proof| proof.at_source_tactic(*source_index));
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
                                let evolving = outcome_proof.take().ok_or_else(|| ClickError::new(
                                    format!("`{proof_label}` path {path_index}: resource scope has no outcome Proof")
                                ))?;
                                let closed = evolving.close_outcome_resource_scope(
                                    resource,
                                    *preserve_exposed_body,
                                )?;
                                outcome = closed.focused_outcome_snapshot()?;
                                outcome_proof = Some(closed);
                            }
                            PostExecutionTactic::UnfoldPredicate(name) => {
                                let CFunctionOutcome::Return { .. } = &outcome else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: predicate unfolding requires a return outcome"
                                    )));
                                };

                                let certificate = if let Some(evolving) = outcome_proof.take() {
                                    // The migrated path: the tactic advances
                                    // this path's one evolving outcome proof
                                    // and retains its checked step directly.
                                    let before = evolving.checkpoint();
                                    let unfolded = evolving
                                        .apply_step(ProofStep::UnfoldPredicate(name.clone()))?;
                                    let certificate = unfolded.certificate_since(&before)?;
                                    outcome_proof = Some(unfolded);
                                    certificate
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
                            PostExecutionTactic::UnfoldFunction {
                                application,
                                premises,
                            } => {
                                let evolving = outcome_proof.take().ok_or_else(|| ClickError::new(
                                    format!("`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable")
                                ))?;
                                let before = evolving.checkpoint();
                                let step = match premises {
                                    None => ProofStep::UnfoldFunction(application.clone()),
                                    Some(premises) => ProofStep::UnfoldFunctionUsing {
                                        application: application.clone(),
                                        premises: premises.clone(),
                                    },
                                };
                                let unfolded = evolving.apply_step(step)?;
                                let certificate = unfolded.certificate_since(&before)?;
                                outcome_proof = Some(unfolded);
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
                                let CFunctionOutcome::Return { .. } = &outcome else {
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
                                    let applied =
                                        evolving.apply_theorem_application(application)?;
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
                                // The retained `apply using` step is prefixed to every
                                // claim certificate, so independent verification holds the
                                // same checked conclusions when the closer runs.
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
                                let CFunctionOutcome::Return { .. } = &outcome else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: theorem application requires a return outcome"
                                    )));
                                };

                                if let Some(evolving) = outcome_proof.take() {
                                    // The migrated explicit case: the checked
                                    // application advances this path's
                                    // evolving outcome proof directly.
                                    let applied =
                                        evolving.apply_step(ProofStep::ApplyTheoremUsing {
                                            application: application.clone(),
                                            premises: premises.clone(),
                                        })?;
                                    outcome_proof = Some(applied);
                                } else {
                                    // The unconditional substrate makes this unreachable;
                                    // fail loudly rather than silently routing through the
                                    // deleted legacy fixed-state root.
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for this path is unavailable"
                                    )));
                                };
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
                                        let prepared = evolving
                                            .with_outcome_store_consequences()?;
                                        let before = prepared.checkpoint();
                                        let scope =
                                            prepared.begin_have(have.proposition.clone())?;
                                        let selected = match &have.proof {
                                            SourceProof::Default
                                            | SourceProof::Tactic(
                                                SmartTactic::Auto | SmartTactic::Simp,
                                            ) => scope.try_simp_closure()?,
                                            SourceProof::Script(tactics) => {
                                                scope.try_authoritative_linear_script(tactics)?
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

                                outcome_proof = Some(
                                    required_outcome(&outcome_proof)?
                                        .with_outcome_store_consequences()?,
                                );
                                let transport_available = required_outcome(&outcome_proof)?.facts();
                                let path_unfolds = direct_view.unfolded_predicates.to_vec();
                                let candidates = if premises.is_none() {
                                    Some(fact_transport_candidates_at_outcome(
                                        &transport_available.to_vec(),
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
                                let (checked_facts, certificate) = if let Some(evolving) =
                                    outcome_proof.take()
                                {
                                    // The migrated cases: an explicit
                                    // transport applies its source step and
                                    // a smart one searches its gathered
                                    // candidates, both advancing this
                                    // path's evolving outcome proof, which
                                    // records the checked lowerings on the
                                    // goal atomically.
                                    let prepared = evolving.with_outcome_store_consequences()?;
                                    let before = prepared.checkpoint();
                                    let transported = if let Some(premises) = premises {
                                        prepared.apply_step(ProofStep::TransportUsing {
                                            source: source.clone(),
                                            target: target.clone(),
                                            premises: premises.clone(),
                                        })?
                                    } else {
                                        prepared.search_fixed_state_fact_transport(
                                            source,
                                            target,
                                            candidates
                                                .clone()
                                                .expect("smart transport gathered candidates"),
                                        )?
                                    };
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
                                            claims,
                                            &closures,
                                            &rewrite_claim_equalities,
                                            &unfolded_predicates,
                                        )?,
                                    };
                                let proof = proof
                                    .refresh_outcome_from(required_outcome(&outcome_proof)?)?
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
                            PostExecutionTactic::LetSatisfy(binding) => {
                                let (claim_index, surface_goal, proof) =
                                    match existence_proof.take() {
                                        Some(active) => active,
                                        None => begin_outcome_existence_proof(
                                            outcome_proof.as_ref().ok_or_else(|| {
                                                ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: the typed outcome goal for `let satisfy` is unavailable"
                                                ))
                                            })?,
                                            function,
                                            pre_state,
                                            arguments,
                                            &outcome,
                                            claims,
                                            &closures,
                                            &rewrite_claim_equalities,
                                            &unfolded_predicates,
                                        )?,
                                    };
                                let proof = proof
                                    .refresh_outcome_from(required_outcome(&outcome_proof)?)?
                                    .apply_step(ProofStep::LetSatisfy(binding.clone()))?;
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
                                    ProofTactic::LetSatisfy(binding.clone()),
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
                                            claims,
                                            &closures,
                                            &rewrite_claim_equalities,
                                            &unfolded_predicates,
                                        )?,
                                    };
                                let proof = proof
                                    .refresh_outcome_from(required_outcome(&outcome_proof)?)?
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
                                            claims,
                                            &closures,
                                            &rewrite_claim_equalities,
                                            &unfolded_predicates,
                                        )?,
                                    };
                                let proof = proof
                                    .refresh_outcome_from(required_outcome(&outcome_proof)?)?
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
                                // A contract resource claim is visible only
                                // through the contract's checked resource
                                // transition, which `simp` applies before
                                // closing claims against the outcome. The
                                // closure `simp` records for such a claim is
                                // spelled `assumption`, so the same reading of
                                // the outcome has to be available here: without
                                // it an expanded `simp` cannot reproduce the
                                // claim its own certificate reports closed.
                                if !resource_transition_applied
                                    && matches!(outcome, CFunctionOutcome::Return { .. })
                                    && claims.iter().enumerate().any(|(index, claim)| {
                                        let clause = claim.clause();
                                        !closures[index].is_closed()
                                            && matches!(clause.ensure(), Ensure::Resource(_))
                                    })
                                    && crate::kernel::c_function_return_resources_definitionally_established(
                                        pre_state,
                                        function,
                                        arguments,
                                        &outcome,
                                        &assumptions_from_propositions(&path_requirements),
                                    )
                                    && let Ok(transitioned) = required_outcome(&outcome_proof)?
                                        .apply_outcome_contract_resources(pre_state, function)
                                {
                                    outcome = transitioned.focused_outcome_snapshot()?;
                                    resource_transition_applied = true;
                                    outcome_proof = Some(transitioned);
                                }

                                // Each claim is focused from the evolving
                                // outcome Proof and retains its completion.
                                let fixed_state_root = match (outcome_proof.as_ref(), &outcome) {
                                    (Some(evolving), _) => Some(evolving.clone()),
                                    (None, CFunctionOutcome::Return { .. }) => {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}: missing retained outcome Proof"
                                        )));
                                    }
                                    (
                                        None,
                                        CFunctionOutcome::Throw { .. }
                                        | CFunctionOutcome::VerificationDiverges
                                        | CFunctionOutcome::UndefinedBehavior(_)
                                        | CFunctionOutcome::RuntimeError(_),
                                    ) => None,
                                };
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let ensure_clause = claim.clause();
                                    if let Ensure::Resource(_resource) = ensure_clause.ensure() {
                                        if let Ok(checked_resource) =
                                            required_outcome(&outcome_proof)?
                                                .check_outcome_resource_claim(
                                                    &completed_execution,
                                                    *claim,
                                                )
                                        {
                                            closures[claim_index] = ClaimClosure::resource(
                                                ClaimCertificate::ExactCheck,
                                                checked_resource,
                                            );
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
                                                            claims[claim_index].key(),
                                                            path_index,
                                                            proof.completed_proposition()?,
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
                                                    .available_kernel_matching(
                                                        surface_goal,
                                                        |fact| {
                                                            path_requirements
                                                                .contains_top_level(fact)
                                                        },
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
                                                        claims[claim_index].key(),
                                                        path_index,
                                                        proof.completed_proposition()?,
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
                                            .focus_lowered_outcome_claim(
                                                goal,
                                                &goal_facts,
                                                surface_goal,
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
                                                    claims[claim_index].key(),
                                                    path_index,
                                                    proof.completed_proposition()?,
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
                            | PostExecutionTactic::ArithmeticUsing(_)
                            | PostExecutionTactic::ArithmeticCertificate(_)
                            | PostExecutionTactic::Both(_) => {
                                let closer_name = match post_tactic {
                                    PostExecutionTactic::Both(_) => "both",
                                    PostExecutionTactic::ArithmeticUsing(_) => "arithmetic",
                                    PostExecutionTactic::ArithmeticCertificate(_) => {
                                        "arithmetic_certificate"
                                    }
                                    _ => "normalize",
                                };
                                let normalization_step = match post_tactic {
                                    PostExecutionTactic::NormalizeUsing(premises) => {
                                        ProofStep::NormalizeUsing(premises.clone())
                                    }
                                    PostExecutionTactic::ArithmeticUsing(premises) => {
                                        ProofStep::ArithmeticUsing(premises.clone())
                                    }
                                    PostExecutionTactic::ArithmeticCertificate(certificate) => {
                                        ProofStep::ArithmeticCertificate(certificate.clone())
                                    }
                                    _ => ProofStep::Normalize,
                                };
                                let mut closed_any = false;
                                // Each claim is focused from the evolving
                                // outcome Proof and retains its completion.
                                let fixed_state_root = match (outcome_proof.as_ref(), &outcome) {
                                    (Some(evolving), _) => Some(evolving.clone()),
                                    (None, CFunctionOutcome::Return { .. }) => {
                                        return Err(ClickError::new(format!(
                                            "`{proof_label}` path {path_index}: missing retained outcome Proof"
                                        )));
                                    }
                                    (
                                        None,
                                        CFunctionOutcome::Throw { .. }
                                        | CFunctionOutcome::VerificationDiverges
                                        | CFunctionOutcome::UndefinedBehavior(_)
                                        | CFunctionOutcome::RuntimeError(_),
                                    ) => None,
                                };
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let ensure_clause = claim.clause();
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
                                        // Same rule for the explicit arithmetic
                                        // closer: its premises are cited against
                                        // a return state this path does not have.
                                        if matches!(
                                            normalization_step,
                                            ProofStep::ArithmeticUsing(_)
                                        ) {
                                            return Err(ClickError::new(
                                                "`arithmetic using` requires a return-state proposition; use context-free `normalize()` for a divergent path",
                                            ));
                                        }
                                        closures[claim_index] = ClaimClosure::vacuous(
                                            &completed_execution,
                                            path_index,
                                            claim.key(),
                                            ClaimCertificate::ExactCheck,
                                        )?;
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
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: `{closer_name}` could not lower goal: {message}"
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
                                                        claims[claim_index].key(),
                                                        path_index,
                                                        proof.completed_proposition()?,
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
                                            .focus_lowered_outcome_claim(
                                                goal,
                                                &goal_facts,
                                                surface_goal,
                                            )?;
                                        let candidate = if let PostExecutionTactic::Both(both) =
                                            post_tactic
                                        {
                                            focused.apply_both_source(both)
                                        } else if let PostExecutionTactic::ArithmeticUsing(
                                            surface_premises,
                                        ) = post_tactic
                                        {
                                            let kernels = surface_premises
                                                .iter()
                                                .map(|premise| {
                                                    focused.lower_cited_surface_proposition(
                                                        premise,
                                                        "post-execution arithmetic premise",
                                                    )
                                                })
                                                .collect::<Result<Vec<_>, _>>()?;
                                            for (premise_index, premise) in
                                                kernels.iter().enumerate()
                                            {
                                                if !focused
                                                    .facts()
                                                    .exact_available_across_effects(premise, &[])
                                                {
                                                    return Err(focused.step_error(format!(
                                                        "post-execution `arithmetic using` premise {premise_index} is not exactly available"
                                                    )));
                                                }
                                            }
                                            (|| -> Result<_, ClickError> {
                                                let goal = focused
                                                    .goal()
                                                    .ok_or_else(|| focused.step_error("post-execution arithmetic requires a proposition goal"))?;
                                                let surface_goal = focused
                                                    .surface_goal()
                                                    .ok_or_else(|| focused.step_error("post-execution arithmetic requires a source goal"))?;
                                                let pairs = kernels
                                                    .into_iter()
                                                    .zip(surface_premises.iter().cloned())
                                                    .collect::<Vec<_>>();
                                                let kernel_premises = pairs
                                                    .iter()
                                                    .map(|(kernel, _)| kernel.clone())
                                                    .collect::<Vec<_>>();
                                                let certificate = if let Some(plan) = crate::surface::checking::plan_special_arithmetic_certificate(
                                                    goal,
                                                    &kernel_premises,
                                                ) {
                                                    crate::surface::checking::special_plan_to_surface_certificate(
                                                        &plan,
                                                        surface_premises,
                                                        surface_goal,
                                                    )
                                                } else if let Some(plan) = crate::surface::checking::plan_integer_affine_certificate(
                                                    goal,
                                                    &kernel_premises,
                                                ) {
                                                    let snapshot = surface_snapshot_selector(surface_goal);
                                                    let integer_pairs = if let Some(selector) = snapshot {
                                                        pairs
                                                            .iter()
                                                            .map(|(kernel, surface)| {
                                                                surface_at_snapshot(surface, &selector)
                                                                    .map(|anchored| (kernel.clone(), anchored))
                                                            })
                                                            .collect::<Result<Vec<_>, _>>()
                                                            .map_err(|error| {
                                                                focused.step_error(format!(
                                                                    "post-execution Integer premise snapshot could not be serialized: {error:?}"
                                                                ))
                                                            })?
                                                    } else {
                                                        pairs.clone()
                                                    };
                                                    let certificate = crate::surface::proof::smart_closures::integer_plan_to_surface_certificate(
                                                        &plan,
                                                        &integer_pairs,
                                                        surface_goal,
                                                    )
                                                    .ok_or_else(|| {
                                                        focused.step_error(
                                                            "post-execution Integer arithmetic certificate could not be transcribed",
                                                        )
                                                    })?;
                                                    ArithmeticCertificate::integer(certificate)
                                                } else {
                                                    let plan = crate::surface::checking::plan_signed_arithmetic_certificate(
                                                        goal,
                                                        &kernel_premises,
                                                    )
                                                    .ok_or_else(|| {
                                                        focused.step_error(
                                                            "post-execution arithmetic certificate could not be constructed",
                                                        )
                                                    })?;
                                                    let certificate = focused
                                                        .signed_plan_to_surface_certificate(
                                                            &plan,
                                                            &pairs,
                                                            surface_goal,
                                                        )
                                                        .ok_or_else(|| {
                                                            focused.step_error(
                                                                "post-execution signed arithmetic certificate could not be transcribed",
                                                            )
                                                        })?;
                                                    ArithmeticCertificate {
                                                        family: ArithmeticCertificateFamily::SignedInt32(
                                                            certificate,
                                                        ),
                                                    }
                                                };
                                                focused.apply_step(
                                                    ProofStep::ArithmeticCertificate(certificate),
                                                )
                                            })()
                                        } else {
                                            focused.apply_step(normalization_step.clone())
                                        };
                                        match candidate {
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
                                                    claims[claim_index].key(),
                                                    path_index,
                                                    proof.completed_proposition()?,
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
                                let CFunctionOutcome::Return { .. } = &outcome else {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}, tactic {tactic_index}: `rewrite` requires a return outcome"
                                    )));
                                };
                                // Claim-goal rewrites focus fresh obligation
                                // roots; the evolving outcome proof supplies
                                // them when this path derived a goal, and the
                                // path lineage itself is not advanced.
                                let mut rewrote_any = false;
                                let mut first_error = None;
                                let mut retained_certificate = None;
                                for (claim_index, claim) in claims.iter().enumerate() {
                                    if closures[claim_index].is_closed() {
                                        continue;
                                    }
                                    let ensure_clause = claim.clause();
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
                                    // Continue the retained claim judgment, or
                                    // focus its exact lowering on the owning outcome.
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
                                                    proof,
                                                ));
                                            }
                                            Err(error) => last_error = Some(error),
                                        }
                                    } else {
                                        let evolving = required_outcome(&outcome_proof)?;
                                        for (goal, goal_facts) in &goal_candidates {
                                            match evolving
                                                .focus_lowered_outcome_claim(
                                                    goal.clone(),
                                                    goal_facts,
                                                    surface_goal,
                                                )?
                                                .apply_step(ProofStep::Rewrite(
                                                    surface_equality.clone(),
                                                )) {
                                                Ok(proof) => {
                                                    let certificate = proof.certificate();
                                                    rewritten_result = Some((
                                                        proof.goal().cloned(),
                                                        certificate,
                                                        proof,
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
                                            let checkpoint = chained.checkpoint();
                                            rewritten_claim_proofs[claim_index] =
                                                Some((chained, checkpoint));
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
                            PostExecutionTactic::If { .. }
                            | PostExecutionTactic::CallOutcomes { .. } => unreachable!(
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
                                    match required_outcome(&outcome_proof)?.apply_outcome_contract_resources(pre_state, function) {
                                        Ok(transitioned) => {
                                            outcome = transitioned.focused_outcome_snapshot()?;
                                            resource_transition_applied = true;
                                            outcome_proof = Some(transitioned);
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
                                    let proof = proof
                                        .refresh_outcome_from(required_outcome(&outcome_proof)?)?;
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
                                    )?;
                                    closures[claim_index] = ClaimClosure::by_checked_proposition(
                                        claims[claim_index].key(),
                                        path_index,
                                        &certificate,
                                        completed.completed_proposition()?,
                                    );
                                    if capturing_this_tactic {
                                        path_deferred_capture_tactics
                                            .extend(certificate.to_proof_tactics());
                                    }
                                    continue;
                                }
                                // A divergent path has no outcome to prove
                                // claims against. Its checked execution theorem
                                // supplies vacuity evidence for each selected claim.
                                if matches!(&outcome, CFunctionOutcome::VerificationDiverges) {
                                    let certificate = ProofCertificate::from_proof_tactics(&[
                                        ProofTactic::Normalize,
                                    ])
                                    .map_err(|error| {
                                        ClickError::new(format!(
                                            "`{proof_label}` path {path_index}, tactic {tactic_index}: divergence produced an invalid normalize certificate: {error:?}"
                                        ))
                                    })?;
                                    for (claim_index, closure) in closures.iter_mut().enumerate() {
                                        if closure.is_closed() {
                                            continue;
                                        }
                                        *closure = ClaimClosure::vacuous(
                                            &completed_execution,
                                            path_index,
                                            claims[claim_index].key(),
                                            ClaimCertificate::Claim(certificate.to_proof_tactics()),
                                        )?;
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
                                if claims
                                    .iter()
                                    .enumerate()
                                    .all(|(claim_index, _)| closures[claim_index].is_closed())
                                {
                                    continue;
                                }
                                // Plan claim scopes on the same retained outcome. A
                                // bounded miss leaves that immutable ancestor intact.
                                if let CFunctionOutcome::Return { .. }
                                | CFunctionOutcome::Throw { .. } = &outcome
                                {
                                    let mut direct_claims = Vec::new();
                                    // Exact resource checks return evidence separately
                                    // from the proposition scopes in this group.
                                    let mut direct_resource_claims = Vec::new();
                                    let mut direct_resource_evidence = BTreeMap::new();
                                    for (claim_index, claim) in claims.iter().enumerate() {
                                        if closures[claim_index].is_closed() {
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
                                    if !direct_resource_claims.is_empty() {
                                        let CFunctionOutcome::Return { .. } = &outcome else {
                                            unreachable!("gated on a return outcome above");
                                        };
                                        for (claim_index, _resource, _borrowed) in
                                            &direct_resource_claims
                                        {
                                            let claim_label = function_claim_label(
                                                function_block.signature().name(),
                                                &claims[*claim_index],
                                            );
                                            let checked = required_outcome(&outcome_proof)?.check_outcome_resource_claim(&completed_execution, claims[*claim_index]).map_err(|error| ClickError::new(format!(
                                                "`{proof_label}` path {path_index} left `{claim_label}` unproved; use `simp()` after establishing the facts and resources it needs (claim index {claim_index})\nlast closing attempt:\n{}", error.message()
                                            )))?;
                                            direct_resource_evidence.insert(*claim_index, checked);
                                        }
                                    }
                                    if direct_claims.is_empty()
                                        && !direct_resource_claims.is_empty()
                                    {
                                        let tactics = direct_resource_evidence
                                            .values()
                                            .map(|_| ProofTactic::Assumption)
                                            .collect::<Vec<_>>();
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
                                                    ClaimClosure::resource(ClaimCertificate::GroupedTransition,
                                                        direct_resource_evidence.remove(claim_index).ok_or_else(|| ClickError::new("grouped resource claim is missing its checked evidence"))?);
                                            }
                                            path_grouped_surface_closers
                                                .extend(certificate.to_proof_tactics());
                                        } else {
                                            for (claim_index, _, _) in &direct_resource_claims {
                                                closures[*claim_index] =
                                                    ClaimClosure::resource(ClaimCertificate::Claim(certificate.to_proof_tactics()),
                                                        direct_resource_evidence.remove(claim_index).ok_or_else(|| ClickError::new("resource claim is missing its checked evidence"))?);
                                            }
                                        }
                                        if capturing_this_tactic {
                                            path_deferred_capture_tactics
                                                .extend(certificate.to_proof_tactics());
                                        }
                                        continue;
                                    }
                                    if !direct_claims.is_empty() {
                                        let direct_certificate =
                                            crate::kernel::with_search_attempt_rollback(|| {
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
                                        let mut direct_proof = required_outcome(&outcome_proof)?.clone();

                                        // The grouped closure exports only
                                        // work after this checkpoint; earlier
                                        // drained tactics on an evolving root
                                        // are recorded by their own tactics.
                                        let direct_base = direct_proof.checkpoint();
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
                                            // claims, retained provenance
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
                                                    .map(|reason| format!("\n{}", reason.message()))
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
                                            return Ok(Some((direct_proof, certificate, completed.1)));
                                        }
                                        Ok(Some((direct_proof, completed.0, completed.1)))
                                                    };
                                                let outcome = attempt();
                                                let keep = matches!(&outcome, Ok(Some(_)));
                                                (outcome, keep)
                                            })?;
                                        if let Some((
                                            completed_root,
                                            certificate,
                                            checked_propositions,
                                        )) = direct_certificate
                                        {
                                            outcome_proof = Some(completed_root);
                                            if checked_propositions.len() != direct_claims.len() {
                                                return Err(ClickError::new(format!(
                                                    "`{proof_label}` path {path_index}, tactic {tactic_index}: completed proposition authority did not match the checked claim set"
                                                )));
                                            }
                                            if proof_context.constants.grouped_contract {
                                                // Each exact resource witness owns its
                                                // claim key. Serialize its explicit closer
                                                // after the checked proposition scopes.
                                                let certificate = if direct_resource_claims
                                                    .is_empty()
                                                {
                                                    certificate
                                                } else {
                                                    let mut tactics =
                                                        certificate.to_proof_tactics();
                                                    tactics.extend(
                                                        direct_resource_evidence
                                                            .values()
                                                            .map(|_| ProofTactic::Assumption),
                                                    );
                                                    ProofCertificate::from_proof_tactics(&tactics)
                                                        .map_err(|error| {
                                                            ClickError::new(format!(
                                                                "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped resource closer was invalid: {error:?}"
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
                                                            claims[claim_index].key(),
                                                            path_index,
                                                            &certificate,
                                                            checked_proposition,
                                                        );
                                                }
                                                for (claim_index, _, _) in &direct_resource_claims {
                                                    closures[*claim_index] =
                                                        ClaimClosure::resource(ClaimCertificate::GroupedTransition,
                                                        direct_resource_evidence.remove(claim_index).ok_or_else(|| ClickError::new("grouped resource claim is missing its checked evidence"))?);
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
                                                            claims[claim_index].key(),
                                                            path_index,
                                                            &certificate,
                                                            checked_proposition,
                                                        );
                                                }
                                                // Resource productions were checked
                                                // before the attempt; their surface
                                                // certificate is the same trivial
                                                // Assumption that explicit closure
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
                                                            ClaimClosure::resource(ClaimCertificate::Claim(assumption_certificate.to_proof_tactics()),
                                                        direct_resource_evidence.remove(claim_index).ok_or_else(|| ClickError::new("resource claim is missing its checked evidence"))?);
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
                                    let Some(root) = outcome_proof.as_ref() else {
                                        continue;
                                    };
                                    let ensure_clause = claim.clause();
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
                                        surface_goal,
                                        &rewrite_claim_equalities[claim_index],
                                        &unfolded_predicates,
                                        &claim_label,
                                        path_index,
                                        parsed_function.parameters(),
                                        predicate_environment,
                                        click_function_environment,
                                    )? {
                                        reasons.push(reason.message().to_owned());
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
                    let path_requirements = outcome_proof
                        .as_ref()
                        .map_or_else(|| proof.facts().clone(), |root| root.facts().clone());
                    drop(_post_execution_timing);
                    let _path_certification_timing = crate::instrumentation::OperationTiming::new(
                        function_block.signature().name(),
                        &proof_label,
                        "path closure and theorem assembly",
                    );

                    let deferred_population_obligations = path
                        .obligations()
                        .iter()
                        .filter(|obligation| post_execution_population_obligation(obligation))
                        .filter(|obligation| {
                            !exact_fact_is_available(obligation.proposition(), &path_requirements)
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    if !deferred_population_obligations.is_empty() {
                        return Err(ClickError::new(format!(
                            "execution proof failed for `{proof_label}` path {path_index}: {}",
                            describe_missing_proof_obligations(
                                &deferred_population_obligations,
                                &path_requirements.to_vec(),
                                pre_state.resources().facts(),
                                parsed_function.parameters(),
                                arguments,
                                path.facts(),
                            )
                        )));
                    }

                    // Closing pure claims with simple tactics does not itself
                    // perform the return-resource exchange. In particular a
                    // consuming contract may have no resource ensure whose
                    // `assumption` closer would trigger it. After all open
                    // bodies and deferred invariants have been checked, give
                    // every completed path the same checked exit transition
                    // that a closing `simp` would perform.
                    if !resource_transition_applied
                        && matches!(outcome, CFunctionOutcome::Return { .. })
                        && crate::kernel::c_function_return_resources_definitionally_established(
                            pre_state,
                            function,
                            arguments,
                            &outcome,
                            path_requirements.assumptions(),
                        )
                        && let Ok(transitioned) = required_outcome(&outcome_proof)?
                            .apply_outcome_contract_resources(pre_state, function)
                    {
                        outcome = transitioned.focused_outcome_snapshot()?;
                        resource_transition_applied = true;
                        outcome_proof = Some(transitioned);
                    }

                    if matches!(outcome, CFunctionOutcome::Return { .. }) {
                        let lifetime_assumptions = path_requirements.assumptions();
                        let lifetime_obligation =
                            required_outcome(&outcome_proof)?.allocation_lifetime_obligation()?;
                        let deferred_resource_transition =
                            claims.iter().enumerate().any(|(claim_index, claim)| {
                                matches!(claim.clause().ensure(), Ensure::Resource(_))
                                    && closures[claim_index].closed().is_some_and(
                                        ClosedClaim::defers_checked_resource_transition,
                                    )
                            });
                        let has_returned_resource_claims =
                            claims.iter().enumerate().any(|(claim_index, claim)| {
                                matches!(claim.clause().ensure(), Ensure::Resource(_))
                                    && closures[claim_index].closed().is_some_and(
                                        ClosedClaim::contributes_checked_resource_claim_resources,
                                    )
                            });
                        let all_resource_claims_checked = has_returned_resource_claims
                            && claims.iter().enumerate().all(|(claim_index, claim)| {
                                !matches!(claim.clause().ensure(), Ensure::Resource(_))
                                    || closures[claim_index]
                                        .closed()
                                        .and_then(ClosedClaim::checked_resource_claim_resources)
                                        .is_some()
                            });
                        let mut checked_returned_resources = crate::kernel::ResourceContext::new();
                        if all_resource_claims_checked {
                            for closure in &closures {
                                if let Some(resources) = closure
                                    .closed()
                                    .and_then(ClosedClaim::checked_resource_claim_resources)
                                    .filter(|_| {
                                        closure
                                            .closed()
                                            .is_some_and(ClosedClaim::contributes_checked_resource_claim_resources)
                                    })
                                {
                                    checked_returned_resources = checked_returned_resources
                                        .unchecked_with_facts(resources.facts().iter().cloned());
                                }
                            }
                        }
                        if !deferred_resource_transition {
                            match check_allocation_lifetime(
                                &completed_execution,
                                lifetime_obligation,
                                path_index,
                                lifetime_assumptions,
                                all_resource_claims_checked.then_some(&checked_returned_resources),
                                &outcome,
                            )? {
                                Ok(Some(obligation)) => {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}: C operation could not be verified: {}",
                                        describe_runtime_error(
                                            &crate::kernel::CRuntimeError::LiveAllocationLeak {
                                                allocation: obligation.allocation().clone(),
                                                resource: obligation.holder().cloned(),
                                                hint: None,
                                            },
                                            parsed_function.parameters(),
                                            arguments,
                                        )
                                    )));
                                }
                                Ok(None) => {}
                                Err(error) => {
                                    return Err(ClickError::new(format!(
                                        "`{proof_label}` path {path_index}: C operation could not be verified: {}",
                                        describe_runtime_error(
                                            &error,
                                            parsed_function.parameters(),
                                            arguments,
                                        )
                                    )));
                                }
                            }
                        }
                    }

                    if !require_explicit_closers
                        && let Some((claim_index, _, proof)) = existence_proof.take()
                    {
                        let proof =
                            proof.refresh_outcome_from(required_outcome(&outcome_proof)?)?;
                        match proof.try_direct_logical_closure()? {
                            Some(completed) if completed.is_complete() => {
                                // The source's choose/witness steps are already
                                // retained in the path surface stream. The
                                // ordinary implicit closer contributes no
                                // additional syntax.
                                closures[claim_index] = ClaimClosure::by_exact_check_completing(claims[claim_index].key(), path_index,
                                    completed.completed_proposition()?,
                                );
                            }
                            _ => closures[claim_index].record_failure(ClickError::new(
                                "the retained existential Proof did not close by the implicit exact check",
                            )),
                        }
                    }

                    if !require_explicit_closers {
                        for (claim_index, claim) in claims.iter().enumerate() {
                            if closures[claim_index].is_closed() {
                                continue;
                            }
                            if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
                                closures[claim_index] = ClaimClosure::vacuous(
                                    &completed_execution,
                                    path_index,
                                    claim.key(),
                                    ClaimCertificate::ExactCheck,
                                )?;
                                continue;
                            }
                            // The implicit closer is the direct logical closure
                            // of the claim from the outcome Proof: it records
                            // the completion claim certification matches. The
                            // exact surface checker below remains for claims
                            // that closure does not reach.
                            let claim_label =
                                function_claim_label(function_block.signature().name(), claim);
                            if let Some(root) = outcome_proof.as_ref()
                                && let Ensure::Proposition(surface_goal) = claim.clause().ensure()
                            {
                                match close_claim_directly_from_outcome(
                                    root,
                                    function,
                                    claim,
                                    pre_state,
                                    arguments,
                                    &outcome,
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
                                                claims[claim_index].key(),
                                                path_index,
                                                completed.completed_proposition()?,
                                            );
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
                                Some(Ok(checked)) => {
                                    closures[claim_index] = ClaimClosure::resource(
                                        ClaimCertificate::ExactCheck,
                                        checked,
                                    )
                                }
                                Some(Err(error)) => closures[claim_index].record_failure(error),
                                None if !matches!(outcome, CFunctionOutcome::Return { .. }) => {
                                    closures[claim_index].record_failure(ClickError::new(format!(
                                        "`{claim_label}` failed on path {path_index}: {}",
                                        describe_function_outcome(
                                            &outcome,
                                            parsed_function.parameters(),
                                            arguments
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

                    if let Some((claim_index, claim)) = claims
                        .iter()
                        .enumerate()
                        .find(|(claim_index, _)| !closures[*claim_index].is_closed())
                    {
                        let claim_label =
                            function_claim_label(function_block.signature().name(), claim);
                        let closer = "`simp()`";
                        let summary = format!(
                            "`{proof_label}` path {path_index} left `{claim_label}` unproved; use {closer} after establishing the facts and resources it needs (claim index {claim_index})"
                        );
                        if let Some(error) = closures[claim_index].last_error() {
                            return Err(error.clone().with_context(summary));
                        }
                        return Err(ClickError::new(summary));
                    }

                    for closure in &closures {
                        if let Some(key) = closure
                            .closed()
                            .and_then(ClosedClaim::checked_resource_claim_key)
                        {
                            checked_resource_claims_by_path[path_index].push(key.clone());
                        }
                    }
                    let has_returned_resource_claims =
                        claims.iter().enumerate().any(|(claim_index, claim)| {
                            matches!(claim.clause().ensure(), Ensure::Resource(_))
                                && closures[claim_index].closed().is_some_and(
                                    ClosedClaim::contributes_checked_resource_claim_resources,
                                )
                        });
                    let deferred_resource_transition =
                        claims.iter().enumerate().any(|(claim_index, claim)| {
                            matches!(claim.clause().ensure(), Ensure::Resource(_))
                                && closures[claim_index]
                                    .closed()
                                    .is_some_and(ClosedClaim::defers_checked_resource_transition)
                        });
                    let all_resource_claims_checked = has_returned_resource_claims
                        && claims
                            .iter()
                            .enumerate()
                            .filter(|(_, claim)| {
                                matches!(claim.clause().ensure(), Ensure::Resource(_))
                            })
                            .all(|(claim_index, _)| {
                                closures[claim_index]
                                    .closed()
                                    .and_then(ClosedClaim::checked_resource_claim_resources)
                                    .is_some()
                            });
                    let returned_claims_have_grouped_transition = has_returned_resource_claims
                        && claims.iter().enumerate().all(|(claim_index, claim)| {
                            !matches!(claim.clause().ensure(), Ensure::Resource(_))
                                || !closures[claim_index].closed().is_some_and(
                                    ClosedClaim::contributes_checked_resource_claim_resources,
                                )
                                || closures[claim_index].closed().is_some_and(
                                    ClosedClaim::checked_resource_claim_has_grouped_transition,
                                )
                        });
                    let mut checked_returned_resources = crate::kernel::ResourceContext::new();
                    if all_resource_claims_checked {
                        for closure in &closures {
                            if let Some(resources) = closure
                                .closed()
                                .and_then(ClosedClaim::checked_resource_claim_resources)
                                .filter(|_| {
                                    closure.closed().is_some_and(
                                        ClosedClaim::contributes_checked_resource_claim_resources,
                                    )
                                })
                            {
                                checked_returned_resources = checked_returned_resources
                                    .unchecked_with_facts(resources.facts().iter().cloned());
                            }
                        }
                    }
                    let returned_resources_are_jointly_available = matches!(outcome, CFunctionOutcome::Return { ref state, .. } if state
                            .resources()
                            .clone()
                            .without_facts(
                                checked_returned_resources.facts(),
                                &assumptions_from_propositions(&path_requirements),
                            )
                            .is_some());
                    checked_resource_transitions_by_path[path_index] = !deferred_resource_transition
                        && (resource_transition_applied
                            || (all_resource_claims_checked
                                && returned_claims_have_grouped_transition
                                && returned_resources_are_jointly_available));
                    if all_resource_claims_checked {
                        checked_returned_resources_by_path[path_index] =
                            checked_returned_resources.clone();
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
                        let closed = closures[claim_index].require_evidence(
                            &completed_execution,
                            path_index,
                            &claim.key(),
                        )?;
                        let checked_proposition = closed
                            .checked_proposition()
                            .map(|completion| {
                                crate::kernel::c_checked_function_proposition_with_reason(
                                    function,
                                    &specification,
                                    &theorem,
                                    completion,
                                    certified_path,
                                )
                                .map_err(|reason| {
                                    ClickError::new(format!(
                                        "`{proof_label}` claim {:?} on path {path_index} has mismatched proposition completion evidence: {reason}",
                                        claim.key()
                                    ))
                                })
                            })
                            .transpose()?;
                        verified.push(VerifiedCTheorem {
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
                            frontier_loop_clauses: proof_execution
                                .presentation
                                .frontier_loop_clauses
                                .to_vec(),
                            frontier_loop_rules: proof_execution.core.frontier_loop_rules.to_vec(),
                            checked_execution: std::sync::Arc::clone(
                                &provisional_checked_execution,
                            ),
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
                    surface_post_path_indices.push(path_index);
                    surface_post_tactics_by_path.push(path_surface_post_tactics);
                    let implicitly_closable = path_deferred_capture_tactics.is_empty()
                        || (!require_explicit_closers
                            && claims.iter().enumerate().all(|(claim_index, claim)| {
                                !matches!(claim.clause().ensure(), Ensure::Proposition(_))
                                    || closures[claim_index].is_closed()
                            }));
                    if visits_selected_capture {
                        implicit_closure_by_path.push(implicitly_closable);
                        deferred_capture_tactics_by_path.push(path_deferred_capture_tactics);
                        deferred_capture_branches_by_path.push(deferred_capture_branch_path);
                    }
                    outcome_proof
                        .as_ref()
                        .unwrap_or(&proof)
                        .record_accepted_trace(&proof_label, path_index);
                    drop(_path_certification_timing);
                }
                Ok(())
            },
        )?;
        let mut final_checked_execution = completed_execution.clone();
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
            final_checked_execution = completed;
        }
        let completed_with_resource_claims =
            final_checked_execution.with_checked_resource_claims(checked_resource_claims_by_path);
        let completed_with_resource_claims = completed_with_resource_claims
            .with_checked_resource_transitions(checked_resource_transitions_by_path);
        let completed_with_resource_claims = completed_with_resource_claims
            .with_checked_returned_resources(checked_returned_resources_by_path);
        let completed_with_resource_claims = std::sync::Arc::new(completed_with_resource_claims);
        for theorem in &mut verified {
            theorem.checked_execution = std::sync::Arc::clone(&completed_with_resource_claims);
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
                    // Outcomes that share a proof arm but not a C branch
                    // cannot share one suffix after the C `if`; place the
                    // proof cases inside each C leaf instead.
                    Err(message) => {
                        let mut by_leaf = expanded.steps.clone();
                        match append_post_execution_paths_by_surface_leaf(
                            &mut by_leaf,
                            &surface_post_tactics_by_path,
                            &surface_grouped_closers_by_path,
                            &surface_post_choices_by_path,
                            |index| {
                                direct_view.surface_step_branch_path(
                                    surface_post_path_indices[index],
                                    &retained_surface.steps,
                                )
                            },
                        ) {
                            Ok(()) => expanded.steps = by_leaf,
                            Err(_) => expanded.block(message),
                        }
                    }
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
                selector: SurfacePathSelector::Proposition(condition.clone()),
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
            &["f.ensures_0".to_string()],
            &[ProofTactic::Induct {
                parameter: "n".to_string(),
                hypothesis: "ih".to_string(),
            }],
        );

        assert!(error.message().contains("cannot yet certify it"));
        assert!(error.message().contains("tactic 0 (induction)"));
        assert!(error.message().contains("proof script is valid"));
        assert!(error.message().contains("No listed claim was shown false"));
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
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(right.clone()),
                    Box::new(left.clone()),
                ),
                true,
            ));
        let right_term = right;
        // A fact whose negation is *exactly* available still registers as a
        // conflict, and the inconsistency guard is what stops that conflict
        // from being read as sibling-path evidence.
        let exactly_refuted = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(right_term.clone()),
                Box::new(left.clone()),
            ),
            false,
        );
        assert_eq!(
            proof_case_fact_conflicts(&exactly_refuted, &assumptions),
            Err(())
        );

        // An unrelated fact is not evidence either, but for a narrower
        // reason since the general prover left the kernel: the exact routes
        // report no conflict at all rather than deriving one by explosion.
        let unrelated = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(2))),
                Box::new(Bitvector32Term::Constant(10)),
            ),
            true,
        );
        assert_eq!(
            proof_case_fact_conflicts(&unrelated, &assumptions),
            Ok(false)
        );
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

#[cfg(test)]
mod evidence_tests {
    use super::*;

    #[test]
    fn outcome_resource_evidence_rejects_missing_wrong_claim_and_wrong_path() {
        let source = r#"
            resource marker() { fact 0 == 0; }
            verifying "zero.c";
            int32 zero() { owns marker(); ensures result == 0; } by { execute(); simp(); }
        "#;
        let verified =
            verify_c0_sources(source, &[("zero.c", "int32 zero() { return 0; }")]).unwrap();
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
        let Proposition::CFunctionVerifies {
            state,
            arguments,
            outcome,
            ..
        } = implication_body(path.theorem().proposition())
        else {
            panic!("checked function path")
        };
        let key = CFunctionContractClaimKey::Ensure(*index);
        let facts = ProofFacts::from_ordered(&path.assumptions().pure_facts());
        let lifetime = crate::kernel::proof::AllocationLifetimeObligation::new(0);
        let checked = prove_ensure_resource(
            execution,
            key.clone(),
            "resource evidence",
            0,
            &lifetime,
            &[],
            &facts,
            resource,
            clause.borrowed(),
            &[],
            arguments,
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
                .require_evidence(execution, 0, &CFunctionContractClaimKey::Ensure(index + 1))
                .is_err()
        );
        assert!(
            closure
                .require_evidence(&CCheckedFunctionExecution::clone(execution), 0, &key)
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
                loop diverges { invariant 0 == 0; initialize by simp;
                    preserve by { step(); close_invariants(); }
                }
                simp();
            }
        "#;
        let verified = verify_c0_sources(
            source,
            &[("spin.c", "int32 spin() { while (1) {} return 0; }")],
        )
        .unwrap();
        let execution = &verified[0].checked_execution;
        let key = CFunctionContractClaimKey::Ensure(0);
        let closure =
            ClaimClosure::vacuous(execution, 0, key.clone(), ClaimCertificate::ExactCheck).unwrap();
        closure.require_evidence(execution, 0, &key).unwrap();
        assert!(closure.require_evidence(execution, 1, &key).is_err());
        assert!(ClaimClosure::vacuous(execution, 1, key, ClaimCertificate::ExactCheck).is_err());
    }

    #[test]
    fn outcome_driver_has_no_fact_resynchronization_or_certificate_only_closer() {
        let driver = include_str!("claim_proofs.rs");
        let facts = include_str!("../../kernel/proof/facts.rs");
        let outcomes = include_str!("proof_object/outcomes_and_focus.rs");
        let resources = include_str!("resources.rs");
        for retired in [
            concat!("with_checked_", "outcome_facts"),
            concat!("by_checked_", "certificate"),
            concat!("by_grouped_", "transition"),
            concat!("let mut ", "path_requirements"),
        ] {
            assert!(
                !driver.contains(retired),
                "retired outcome boundary: {retired}"
            );
        }
        assert!(!facts.contains(concat!("resync_ordered_", "preserving_provenance")));
        assert!(!outcomes.contains(concat!("with_checked_", "outcome_facts")));
        assert!(!resources.contains(concat!("LegacyResource", "PureFacts")));
    }
}
