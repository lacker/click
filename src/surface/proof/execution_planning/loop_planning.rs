use super::*;
use std::sync::Arc;

/// The proof scope a loop's phase proofs are written in.
///
/// `initialize` and `preserve` bodies are written where the `loop` tactic
/// was written: inside whatever proof `match` arm, `let { ... } = unfold(...)` binding,
/// or call-result binder reached that frontier. Their sub-proofs are built
/// from fresh roots, so the scope has to be attached explicitly or a `have`
/// goal inside a phase body would fail to resolve a name the loop's own
/// clauses resolve. `ExecutionProofEnvironment::proof_locals` is the same
/// map the clause re-annotation uses.
fn phase_proof_scope(
    environment: &ExecutionProofEnvironment<'_>,
) -> PersistentMap<String, ContractExpression> {
    environment
        .proof_locals
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect()
}

/// The first loop binder of `clause` whose name no enclosing contract binder
/// declares.
///
/// D5's landed rule is that a loop binder reuses the enclosing binder's name:
/// the loop takes over that instance, and a fresh name consumes it for the
/// rest of the function. A fresh name is therefore not in scope before the
/// loop, so an entry invariant that reads it has nothing to read and the
/// lowering fails with no name in it. This recovers the name for that
/// refusal; the loop-head checks own every other fresh-name outcome, such as
/// the ambiguity refusal for two matching instances.
fn fresh_loop_binder_name(
    function_block: &FunctionBlock,
    clause: &StructuralClause,
) -> Option<String> {
    let mut enclosing = BTreeSet::new();
    for requirement in function_block.requires() {
        if let Requirement::Resource(ResourceClause::Named { binding, .. }) = requirement.inner() {
            enclosing.insert(binding.name.clone());
        }
    }
    for ensure in function_block.ensures() {
        if let Ensure::Resource(ResourceClause::Named { binding, .. }) = ensure.ensure() {
            enclosing.insert(binding.name.clone());
        }
    }
    clause
        .resources()
        .iter()
        .find_map(|resource| match resource {
            ResourceClause::Named { binding, .. } if !enclosing.contains(&binding.name) => {
                Some(binding.name.clone())
            }
            _ => None,
        })
}

#[allow(clippy::too_many_arguments)]
/// The written invariants of `loop_index`, read through the proof scope the
/// clause was written under: a clause bound inside a proof `match` arm names
/// that arm's bindings, and lowering sees the values they stand for.
fn loop_invariant_surfaces(
    environment: &ExecutionProofEnvironment<'_>,
    loop_index: usize,
    claim_label: &str,
) -> Result<Vec<ClickProposition>, ClickError> {
    environment
        .function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .map(|clause| {
            clause.resolved().map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` loop {loop_index}: could not resolve loop clause bindings: {message}"
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .map(|clauses| {
            clauses
                .iter()
                .flat_map(StructuralClause::items)
                .map(|item| item.proposition().clone())
                .collect()
        })
}

/// Pair the kernel's selected loop-head clauses with generated spellings that
/// explicitly read the iteration-entry snapshot. The written, unqualified
/// clauses retain their source meaning in the enclosing presentation map.
fn record_loop_entry_invariants(
    surface_propositions: &mut SurfacePropositionMap,
    invariant_surfaces: &[ClickProposition],
    preservation: &crate::kernel::CLoopPreservationContext,
    statement_index: usize,
) -> Result<Vec<ClickProposition>, ClickError> {
    if invariant_surfaces.len() != preservation.invariant_propositions().len() {
        return Err(ClickError::new(
            "loop-head invariant results do not align with declared clauses",
        ));
    }
    invariant_surfaces
        .iter()
        .zip(preservation.invariant_propositions())
        .map(|(surface, kernel)| {
            let anchored = surface_at_snapshot(
                surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Statement(statement_index),
                    kind: ProgramPointKind::Entry,
                },
            )?;
            surface_propositions.record_lowering(&anchored, kernel)?;
            Ok(anchored)
        })
        .collect()
}

/// How a written `initialize by { ... }` script divides into the steps that
/// belong to the whole phase and the steps that belong to one invariant.
///
/// A phase script has to establish every declared invariant, but only the
/// `have` that names an invariant is that invariant's own proof. A step
/// written beside them is a helper: it establishes one standalone fact the
/// rest of the phase reads. Handing the whole script to the per-invariant
/// planner made every sibling step part of every invariant's proof, so
/// expansion printed each helper once per invariant and the duplicated
/// script then failed round-trip validation.
struct InitializeScriptLayout<'a> {
    /// Leading `unfold`/`have` steps, with their absolute source indices.
    /// They are planned once, in the order written, and their facts are
    /// available to everything below.
    helpers: Vec<(usize, &'a ProofTactic)>,
    /// `Some` when the script names every declared invariant with its own
    /// `have`, in declaration order: each entry is that `have`'s absolute
    /// source index and the body it was written with.
    invariant_bodies: Option<Vec<(usize, &'a SourceProof)>>,
    /// The proof every invariant runs when the script does not name them
    /// individually.
    shared: SourceProof,
    /// Absolute source indices of the trailing `simp()` closers: a smart
    /// tactic that stands for the whole remaining phase rather than for one
    /// invariant.
    closers: Vec<usize>,
}

impl InitializeScriptLayout<'_> {
    fn whole_proof(proof: &SourceProof) -> InitializeScriptLayout<'_> {
        InitializeScriptLayout {
            helpers: Vec::new(),
            invariant_bodies: None,
            shared: proof.clone(),
            closers: Vec::new(),
        }
    }

    /// True when planning follows the historical shape exactly: no helper is
    /// hoisted and every invariant runs the whole written script.
    fn is_whole_proof(&self) -> bool {
        self.helpers.is_empty() && self.invariant_bodies.is_none()
    }
}

fn initialize_script_layout<'a>(
    proof: &'a SourceProof,
    invariant_items: &[&StructuralItem],
    phase_start: usize,
) -> InitializeScriptLayout<'a> {
    let Some(tactics) = proof.tactics() else {
        return InitializeScriptLayout::whole_proof(proof);
    };
    let mut next_source_index = phase_start;
    let source_indices = tactics
        .iter()
        .map(|tactic| {
            let at = next_source_index;
            next_source_index += source_tactic_count(std::slice::from_ref(tactic));
            at
        })
        .collect::<Vec<_>>();
    let names_an_invariant = |tactic: &ProofTactic| {
        matches!(tactic, ProofTactic::Have(have)
            if invariant_items
                .iter()
                .any(|item| item.proposition() == &have.proposition))
    };
    let helper_end = tactics
        .iter()
        .position(|tactic| match tactic {
            ProofTactic::UnfoldPredicate(_) => false,
            ProofTactic::Have(_) => names_an_invariant(tactic),
            _ => true,
        })
        .unwrap_or(tactics.len());
    let helpers = source_indices[..helper_end]
        .iter()
        .copied()
        .zip(&tactics[..helper_end])
        .collect::<Vec<_>>();
    let rest = &tactics[helper_end..];
    let names_every_invariant = rest.len() >= invariant_items.len()
        && rest.iter().zip(invariant_items).all(|(tactic, item)| {
            matches!(tactic, ProofTactic::Have(have)
                    if &have.proposition == item.proposition())
        })
        && rest[invariant_items.len()..]
            .iter()
            .all(|tactic| matches!(tactic, ProofTactic::Assumption | ProofTactic::Simp));
    let invariant_bodies = names_every_invariant.then(|| {
        rest.iter()
            .take(invariant_items.len())
            .enumerate()
            .map(|(index, tactic)| {
                let ProofTactic::Have(have) = tactic else {
                    unreachable!("the shape check accepted only `have` tactics")
                };
                (source_indices[helper_end + index], &have.proof)
            })
            .collect()
    });
    // Only a `simp()` that stands for what is left of the phase is a
    // whole-phase closer. A `simp()` written before the steps it closes
    // would be one invariant's own proof, not the phase's.
    let closer_start = if names_every_invariant {
        helper_end + invariant_items.len()
    } else {
        tactics.len().saturating_sub(1)
    };
    let closers = source_indices[closer_start.min(tactics.len())..]
        .iter()
        .copied()
        .zip(&tactics[closer_start.min(tactics.len())..])
        .filter(|(_, tactic)| matches!(tactic, ProofTactic::Simp))
        .map(|(index, _)| index)
        .collect();
    InitializeScriptLayout {
        helpers,
        invariant_bodies,
        shared: if helper_end == 0 {
            proof.clone()
        } else {
            SourceProof::Script(rest.to_vec())
        },
        closers,
    }
}

/// Source positions derived once with the verification layout. Expansion
/// consumes retained provenance without interpreting the source layout again.
struct InitializePhaseExpansion {
    helpers: usize,
    individual_bodies: bool,
    sites: Vec<usize>,
}

impl InitializePhaseExpansion {
    fn new(layout: &InitializeScriptLayout<'_>, phase_start: usize) -> Self {
        let mut sites = layout.closers.clone();
        if layout.is_whole_proof() {
            sites.push(phase_start);
        }
        Self {
            helpers: layout.helpers.len(),
            individual_bodies: layout.invariant_bodies.is_some(),
            sites,
        }
    }

    fn expand(&self, selected: usize, certificate: &ProofCertificate) -> Option<Vec<ProofTactic>> {
        if !self.sites.contains(&selected) {
            return None;
        }
        if self.individual_bodies {
            return Some(Vec::new());
        }
        Some(
            certificate
                .to_proof_tactics()
                .into_iter()
                .skip(self.helpers)
                .collect(),
        )
    }
}

pub(in crate::surface::proof) fn verify_loop_initialization_pure_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    proof: &SourceProof,
    clause: &StructuralClause,
    context: &PlanningExecutionContext,
    invariant_checks: &[CLoopInvariantCheck],
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<CheckedLoopInitialization, ClickError> {
    let legacy_site = ProofSite::LoopPhase {
        function_name: environment.function_block.signature().name().to_string(),
        loop_index,
        phase: "initialize",
    };
    let (claim_label, initialize_source_index, initialize_site) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source.claim_label.clone(),
                source
                    .initialize_source_index
                    .unwrap_or(source.loop_source_index),
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
            )
        })
        .unwrap_or_else(|| (legacy_site.description(), 0, legacy_site));
    let mut recorded_snapshots = context.recorded_snapshots.clone();
    recorded_snapshots.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        context.state.clone(),
    );
    for label in environment
        .function_block
        .structural_clauses()
        .iter()
        .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        .filter_map(StructuralClause::label)
    {
        recorded_snapshots.insert(
            ProgramPointRef {
                region: CodeRegionRef::Label(label.to_string()),
                kind: ProgramPointKind::Entry,
            },
            context.state.clone(),
        );
    }
    let invariant_items = clause.items().iter().collect::<Vec<_>>();
    // Generated initialization steps belong to the explicit phase tactic when
    // one exists, or to the enclosing `loop` keyword for an omitted phase.
    // Computing the source statement is only worth it when timings are read.
    let timings_enabled = crate::instrumentation::enabled();
    let initialize_statement_index = if timings_enabled {
        SourceExecutionLayout::for_function(environment.parsed_function)?
            .loop_body_entry(loop_index)
            .unwrap_or(0)
    } else {
        0
    };
    let entry_goals = crate::kernel::c_loop_entry_goals(
        &context.state,
        invariant_checks,
        &assumptions_from_propositions(&context.pure_facts),
    )
    .map_err(|message| {
        if let Some(name) = fresh_loop_binder_name(environment.function_block, clause) {
            return ClickError::new(format!(
                "`{claim_label}`: loop binder `{name}` is not an enclosing contract binder, so an \
                 invariant that reads it has nothing to read at loop entry; reuse the enclosing \
                 binder's name, whose instance the loop takes over"
            ));
        }
        if let Some(refusal) = invariant_items.iter().find_map(|item| {
            crate::surface::diagnostics::describe_consumed_instance_field_read(
                item.proposition(),
                &context.state,
                true,
            )
        }) {
            return ClickError::new(format!(
                "`{claim_label}` loop {loop_index} invariant: {refusal}"
            ));
        }
        ClickError::new(format!("`{claim_label}`: {message}"))
    })?;
    if entry_goals.declarations().len() != invariant_items.len() {
        return Err(ClickError::new(format!(
            "loop {loop_index} entry has {} lowered declarations for {} written invariants",
            entry_goals.declarations().len(),
            invariant_items.len(),
        )));
    }
    let layout = initialize_script_layout(proof, &invariant_items, initialize_source_index);
    let selected_source_index =
        selected_tactic_index_for_site(expansion_capture.as_deref(), &initialize_site);
    let mut phase = Proof::for_fixed_state_frontier(
        &claim_label,
        0,
        &context.pure_facts,
        environment.parsed_function.parameters(),
        environment.arguments,
        environment.initial_state,
        &context.state,
        None,
        &recorded_snapshots,
        &context.surface_propositions,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.theorem_environment,
        &[],
        &[],
    )
    .with_surface_local_scope(&phase_proof_scope(environment));
    for (source_index, helper) in &layout.helpers {
        let checkpoint = phase.checkpoint();
        phase = match helper {
            ProofTactic::UnfoldPredicate(name) => {
                phase.apply_step(ProofStep::UnfoldPredicate(name.clone()))?
            }
            ProofTactic::Have(have) => {
                let scope = phase.begin_have(have.proposition.clone())?;
                check_initialization_body(&scope, &have.proof)?.join()?
            }
            _ => unreachable!("only unfold and have steps are phase helpers"),
        };
        if selected_source_index == Some(*source_index) {
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                &initialize_site,
                *source_index,
                &phase.certificate_since(&checkpoint)?.to_proof_tactics(),
            );
        }
    }
    let mut completions = Vec::new();
    for (invariant_index, (item, goals)) in invariant_items
        .iter()
        .zip(entry_goals.declarations())
        .enumerate()
    {
        let own_body = layout
            .invariant_bodies
            .as_ref()
            .and_then(|bodies| bodies.get(invariant_index))
            .copied();
        let invariant_proof = own_body.map_or(&layout.shared, |(_, body)| body);
        let planned_step = timings_enabled.then(|| {
            ProofTactic::Have(ProofHave {
                proposition: item.proposition().clone(),
                proof: invariant_proof.clone(),
            })
        });
        let _timing = planned_step.as_ref().and_then(|step| {
            TacticTiming::named_for_tactic(
                &claim_label,
                "plan_invariant_entry",
                step,
                invariant_index,
                initialize_source_index,
                initialize_statement_index,
            )
        });
        for obligation in goals {
            let checkpoint = phase.checkpoint();
            let scope = phase.begin_loop_entry_goal(item.proposition().clone(), obligation)?;
            let body_checkpoint = scope.checkpoint();
            let checked = check_initialization_body(&scope, invariant_proof).map_err(|error| {
                // The kernel already refused this declaration and says why.
                if obligation.is_impossible_goal()
                    && let Some(reason) = obligation.context()
                {
                    return ClickError::new(reason);
                }
                error.with_context(format!(
                    "loop {loop_index} invariant {invariant_index} entry"
                ))
            })?;
            let body_certificate = checked.certificate_since(&body_checkpoint)?;
            completions.push(checked.completed_loop_entry_goal()?);
            phase = checked.join()?;
            if let Some(selected) = selected_source_index
                && own_body.map(|(index, _)| index) == Some(selected)
            {
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    &initialize_site,
                    selected,
                    &phase.certificate_since(&checkpoint)?.to_proof_tactics(),
                );
            } else if environment.frontier_loop_source.is_none()
                && layout.is_whole_proof()
                && let Some(index) = selected_source_index
            {
                let tactics = body_certificate.to_proof_tactics();
                let expansion = match invariant_proof {
                    SourceProof::Default | SourceProof::Tactic(_) => tactics,
                    SourceProof::Script(_) => tactics.get(index).cloned().into_iter().collect(),
                };
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    &initialize_site,
                    index,
                    &expansion,
                );
            }
        }
    }
    Ok(CheckedLoopInitialization {
        expansion: InitializePhaseExpansion::new(&layout, initialize_source_index),
        certificate: phase.certificate(),
        entry_goals,
        completions,
    })
}

/// Source execution and smart planning share the checked scope. An explicit
/// failure is final; no other phase body or certificate checker is tried.
fn check_initialization_body<'a>(
    scope: &proof_object::ProofScope<'a>,
    source: &SourceProof,
) -> Result<proof_object::ProofScope<'a>, ClickError> {
    let checked = match source {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
            scope.try_simp_closure()?
        }
        SourceProof::Script(tactics) => scope.try_authoritative_linear_script(tactics)?,
    }
    .ok_or_else(|| ClickError::new("loop initialization body did not close its goal"))?;
    if !checked.is_complete() {
        return Err(ClickError::new(
            "loop initialization body retained an open goal",
        ));
    }
    Ok(checked)
}

pub(in crate::surface::proof) struct CheckedLoopInitialization {
    pub(in crate::surface::proof) certificate: ProofCertificate,
    entry_goals: crate::kernel::CLoopEntryGoals,
    expansion: InitializePhaseExpansion,
    completions: Vec<crate::kernel::proof::CheckedProposition>,
}

impl CheckedLoopInitialization {
    pub(in crate::surface::proof) fn phase_closer_expansion(
        &self,
        selected: usize,
        certificate: &ProofCertificate,
    ) -> Option<Vec<ProofTactic>> {
        self.expansion.expand(selected, certificate)
    }

    pub(in crate::surface::proof) fn is_complete(&self) -> bool {
        let mut completions = self.completions.iter();
        let matched = self
            .entry_goals
            .declarations()
            .iter()
            .flatten()
            .all(|goal| {
                completions
                    .next()
                    .is_some_and(|completion| completion.proposition() == goal.proposition())
            });
        matched && completions.next().is_none()
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn plan_automatic_loop_preservation_body(
    loop_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    body: &CStatement,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<ProofCertificate, ClickError> {
    let claim_label = environment.frontier_loop_source.map_or_else(
        || {
            format!(
                "{}.loop({loop_index}).preserve",
                environment.function_block.signature().name()
            )
        },
        |source| source.claim_label.clone(),
    );
    let source_layout = SourceExecutionLayout::for_function(environment.parsed_function)?;
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: body.clone().into(),
        },
        region: ExecutionRegionKind::LoopBody,
        in_loop_body: true,
        natural_backedge_target: source_layout.natural_loop_target(loop_index),
        natural_exit_target: source_layout.natural_exit_target(loop_index),
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    let mut recorded_snapshots = RecordedSnapshots::new();
    let constants = ExecutionProofConstants {
        proof_site: environment
            .frontier_loop_source
            .and_then(|source| source.proof_site.clone()),
        source_layout,
        function_entry_state: Some(environment.initial_state.clone()),
        function_source_registry: environment.function_source_registry.clone(),
        ..ExecutionProofConstants::default()
    };
    record_statement_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_loop_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        loop_index,
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    let invariant_surfaces = loop_invariant_surfaces(environment, loop_index, &claim_label)?;
    let mut surface_propositions = environment.surface_propositions.clone();
    record_loop_entry_invariants(
        &mut surface_propositions,
        &invariant_surfaces,
        preservation,
        loop_body_statement_index,
    )?;
    let root = Proof::for_execution_frontier(
        &claim_label,
        0,
        ExecutionProofState::at_entry(
            preservation.state().clone(),
            frontier,
            recorded_snapshots,
            surface_propositions,
            PersistentSequence::default(),
        ),
        pure_facts.to_vec(),
        constants.clone(),
        environment.function_block,
        environment.function,
        environment.parsed_function,
        environment.arguments,
        environment.function_environment,
        environment.resource_environment,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.theorem_environment,
    )
    .with_surface_local_scope(&phase_proof_scope(environment));
    let mut pending = vec![root];
    let mut completed = Vec::new();
    let mut steps = 0;
    while let Some(proof) = pending.pop() {
        if proof.is_at_region_boundary() || proof.execution_view()?.frontier.is_at_function_exit() {
            completed.push(proof);
            continue;
        }
        if steps == BOUNDED_EXECUTE_STEP_LIMIT {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation exhausted its {BOUNDED_EXECUTE_STEP_LIMIT}-step budget"
            )));
        }
        steps += 1;
        let view = proof.execution_view()?;
        let is_branch = view
            .context
            .constants
            .source_layout
            .statement(view.frontier.next_statement_index)
            .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }));
        if is_branch {
            let FrontierPosition::StatementEntry { remaining } = &view.frontier.position else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` automatic preservation branch is not at a statement entry"
                )));
            };
            let (source_statement, _) =
                split_next_source_operation(remaining).map_err(ClickError::new)?;
            let CStatement::If { condition, .. } = source_statement else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` source branch does not match the lowered statement"
                )));
            };
            let condition = surface_c_condition(&condition);
            let (split, ids) = proof.split_preservation_case(&condition, 0)?;
            for id in ids.into_iter().flatten() {
                pending.push(preservation_smart_step(split.focus_branch(id)?)?);
            }
        } else {
            pending.push(preservation_smart_step(proof)?);
        }
    }
    let mut paths = Vec::new();
    for leaf in completed {
        let context_execution = leaf.execution_view()?.execution.clone();
        if let Some(blocker) = &context_execution.presentation.surface_record.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` automatic preservation could not lower a body step: {blocker}"
            )));
        }
        let case_path = context_execution
            .presentation
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
                match_arm: choice.match_arm.clone(),
            })
            .collect::<Vec<_>>();
        let surface_tactics = leaf.path_certificate()?.to_proof_tactics();
        let (certificate, selected_offsets) =
            certificate_leaf_for_case_path(&claim_label, &surface_tactics, &case_path)?;
        let case_offsets = selected_offsets
            .or_else(|| recorded_case_offsets(&context_execution.presentation, case_path.len()));
        paths.push(PathCertificate {
            case_path,
            case_offsets,
            certificate,
        });
    }
    merge_phase_path_aligned_certificates(&claim_label, paths)
}

pub(in crate::surface::proof) struct LoopPreservationProofResult {
    pub(in crate::surface::proof) certificate: ProofCertificate,
    pub(in crate::surface::proof) final_exit_candidates: Vec<CLoopFinalExitCandidate>,
    /// The body paths that left this loop through `break`, each an exit at
    /// its own state. The loop rule joins them with the guard-false exit.
    pub(in crate::surface::proof) break_exits: Vec<CLoopBreakExit>,
    /// Loop rules checked by frontier-local tactics inside this loop's
    /// preservation proof. They are evidence for termination only; the
    /// enclosing contract still uses the outer loop's checked artifact.
    pub(in crate::surface::proof) nested_loop_rules: Vec<CVerifiedLoopRule>,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn verify_one_loop_preservation_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    tactics: &[ProofTactic],
    first_generated_tactic_index: usize,
    preservation: &crate::kernel::CLoopPreservationContext,
    pure_facts: &[Proposition],
    invariant_checks: &[CLoopInvariantCheck],
    ranking_measures: &[crate::kernel::CRankingComponent],
    structural_measure: Option<&str>,
    condition: &CExpression,
    body: &CStatement,
    do_while: bool,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<LoopPreservationProofResult, ClickError> {
    let legacy_site = ProofSite::LoopPhase {
        function_name: environment.function_block.signature().name().to_string(),
        loop_index,
        phase: "preserve",
    };
    let (claim_label, preserve_source_index, preserve_site) = environment
        .frontier_loop_source
        .map(|source| {
            (
                source.claim_label.clone(),
                source
                    .preserve_source_index
                    .unwrap_or(source.loop_source_index),
                source
                    .proof_site
                    .clone()
                    .unwrap_or_else(|| legacy_site.clone()),
            )
        })
        .unwrap_or_else(|| (legacy_site.description(), 0, legacy_site));

    let mut program = if environment
        .frontier_loop_source
        .is_some_and(|source| source.preserve_source_index.is_none())
    {
        build_generated_certificate_proof(tactics, &claim_label, preserve_source_index)?
    } else {
        build_internal_proof_from_source_index(tactics, preserve_source_index)?
    };
    if first_generated_tactic_index < tactics.len() {
        // Automatic preservation appends planned body steps and a closer
        // after the source-written unfold prefix. They are owned by the loop
        // tactic, not additional source occurrences after `preserve`.
        // Detach them so a later nested clause cannot be mistaken for one of
        // these generated tactics by expand.
        detach_generated_suffix_from_source_indices(&mut program, first_generated_tactic_index);
    }
    let source_layout = SourceExecutionLayout::for_function(environment.parsed_function)?;
    let natural_loop = source_layout.natural_loop_target(loop_index).is_some();
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let invariant_surfaces = loop_invariant_surfaces(environment, loop_index, &claim_label)?;
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: body.clone().into(),
        },
        region: ExecutionRegionKind::LoopBody,
        in_loop_body: true,
        natural_backedge_target: source_layout.natural_loop_target(loop_index),
        natural_exit_target: source_layout.natural_exit_target(loop_index),
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    let mut recorded_snapshots = RecordedSnapshots::new();
    let nested_tactic_capture = expansion_capture
        .as_deref()
        .and_then(|capture| capture.nested_for_site(Some(&preserve_site)));
    let mut constants = ExecutionProofConstants {
        nested_tactic_capture,
        proof_site: Some(preserve_site),
        invariant_body_context: Some(Arc::new(InvariantBodyContext {
            loop_entry_state: preservation.loop_entry_state().clone(),
            loop_entry_selector: Some(SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Entry,
            })),
            iteration_entry_state: preservation.state().clone(),
            iteration_entry_selector: Some(SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Statement(loop_body_statement_index),
                kind: ProgramPointKind::Entry,
            })),
            checks: invariant_checks.to_vec(),
            ranking_measures: ranking_measures.to_vec(),
            structural_measure: structural_measure.map(str::to_string),
            declared_invariant_surfaces: invariant_surfaces.clone(),
            loop_head_premises: Vec::new(),
            binders: preservation.binders().to_vec(),
            binder_names: Arc::new(written_invariant_binder_names(invariant_checks)),
        })),
        source_layout,
        function_entry_state: Some(environment.initial_state.clone()),
        function_source_registry: environment.function_source_registry.clone(),
        ..ExecutionProofConstants::default()
    };
    let mut surface_propositions = environment.surface_propositions.clone();
    record_statement_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_code_region_program_snapshot_state(
        &mut recorded_snapshots,
        environment.function_block,
        CodeRegion::Loop(loop_index),
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    // The invariants are available at the body entry as kernel facts. A
    // pre-tested loop also has its condition there; a do-while does not, so
    // it must not be recorded as an available premise for the first body.
    let loop_condition = surface_c_condition(condition);
    // The loop head's own clauses, in declaration order, are what a smart
    // bundle closure may cite for a ranking member. Each declared invariant
    // is named twice, once as written and once re-read at iteration entry:
    // the back edge holds the written spelling only where an earlier bundle
    // member or an inner loop already established it, and the closer keeps
    // only the spellings that are exactly available there. Nothing else
    // becomes a candidate, so the set is named by the loop head rather than
    // selected from the ambient fact context.
    let mut loop_head_premises = invariant_surfaces
        .iter()
        .map(|surface| (*surface).clone())
        .collect::<Vec<_>>();
    loop_head_premises.extend(record_loop_entry_invariants(
        &mut surface_propositions,
        &invariant_surfaces,
        preservation,
        loop_body_statement_index,
    )?);
    if !do_while
        && let Ok(lowered) = lower_fixed_state_proposition(
            &loop_condition,
            pure_facts,
            environment.parsed_function.parameters(),
            environment.arguments,
            environment.initial_state,
            preservation.state(),
            None,
            &recorded_snapshots,
            environment.predicate_environment,
            environment.click_function_environment,
        )
    {
        let surface = surface_at_snapshot(
            &loop_condition,
            &ProgramPointRef {
                region: CodeRegionRef::Statement(loop_body_statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        surface_propositions.record_lowering(&surface, &lowered)?;
        loop_head_premises.push(surface);
    }
    if let Some(bundle) = constants.invariant_body_context.as_mut() {
        Arc::make_mut(bundle).loop_head_premises = loop_head_premises;
    }
    let proof_site_for_driver = constants.proof_site.clone();
    let owning_source_index = if environment
        .frontier_loop_source
        .is_some_and(|source| source.preserve_source_index.is_none())
    {
        preserve_source_index
    } else {
        usize::MAX
    };
    // The body runs on a head state that already carries the identities the
    // head invented: the havoc of every local and mutable cell the body
    // writes, a re-bound binder's model fields, an arbitrary algebraic
    // binding. Starting this proof's counter at the base of the identity
    // range would hand the body's first heap allocation, opaque call result
    // or nested join one of them.
    let mut body_execution = ExecutionProofState::at_entry(
        preservation.state().clone(),
        frontier,
        recorded_snapshots,
        surface_propositions,
        PersistentSequence::default(),
    );
    body_execution
        .core
        .advance_kernel_variable_mark(preservation.next_kernel_variable())
        .map_err(|message| ClickError::new(format!("`{claim_label}`.preserve: {message}")))?;
    let root = Proof::for_execution_frontier(
        &claim_label,
        internal_proof_first_index(&program).unwrap_or(0),
        body_execution,
        pure_facts.to_vec(),
        constants.clone(),
        environment.function_block,
        environment.function,
        environment.parsed_function,
        environment.arguments,
        environment.function_environment,
        environment.resource_environment,
        environment.predicate_environment,
        environment.click_function_environment,
        environment.theorem_environment,
    )
    .with_surface_local_scope(&phase_proof_scope(environment));
    if let Some(parent_lineage) = crate::surface::proof_trace::loop_parent_lineage() {
        root.register_trace_scope_under(parent_lineage);
    }
    let mut leaves = Vec::new();
    let mut refuted_match_paths = Vec::new();
    let mut unfinished = Vec::new();
    advance_preservation_region(
        root,
        &program,
        &[],
        expansion_capture.as_deref_mut(),
        proof_site_for_driver.as_ref(),
        owning_source_index,
        &claim_label,
        &mut leaves,
        &mut refuted_match_paths,
        &mut unfinished,
        None,
    )?;
    let invariant_surfaces = loop_invariant_surfaces(environment, loop_index, &claim_label)?;
    let invariant_premise_surfaces = invariant_surfaces
        .iter()
        .map(|surface| {
            surface_at_snapshot(
                surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Statement(loop_body_statement_index),
                    kind: ProgramPointKind::Entry,
                },
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut certificate_paths = Vec::new();
    let mut final_exit_candidates = Vec::new();
    let mut break_exits = Vec::new();
    let mut nested_loop_rules = Vec::new();
    for (execution, path_certificate) in refuted_match_paths {
        let case_path = execution
            .presentation
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
                match_arm: choice.match_arm.clone(),
            })
            .collect::<Vec<_>>();
        let source_tactics = path_certificate.to_proof_tactics();
        let (certificate, selected_offsets) =
            certificate_leaf_for_case_path(&claim_label, &source_tactics, &case_path)?;
        let case_offsets = selected_offsets
            .or_else(|| recorded_case_offsets(&execution.presentation, case_path.len()));
        certificate_paths.push(PathCertificate {
            case_path,
            case_offsets,
            certificate,
        });
    }
    // A path whose script ran out of tactics is reported only after the
    // finished paths have closed their back edges below, so a wrong
    // `close_invariants` on a finished arm is named while its sibling arm
    // is still being written. The report is prepared first because the
    // loop consumes the leaves it counts.
    let deferred_frontier = unfinished
        .first()
        .map(|path| path.report(&claim_label, &leaves));
    for (leaf_index, leaf) in leaves.into_iter().enumerate() {
        leaf.record_nested_accepted_trace(&claim_label, leaf_index);
        let context_execution = leaf.execution_view()?.execution.clone();
        for rule in context_execution.core.frontier_loop_rules.iter() {
            if !nested_loop_rules
                .iter()
                .any(|existing: &CVerifiedLoopRule| existing == rule)
            {
                nested_loop_rules.push(rule.clone());
            }
        }
        let context_frontier = leaf.execution_view()?.frontier.clone();
        let case_path = context_execution
            .presentation
            .case_assumptions
            .iter()
            .map(|choice| ProofCaseChoice {
                condition: choice.condition.clone(),
                value: choice.value,
                match_arm: choice.match_arm.clone(),
            })
            .collect::<Vec<_>>();
        let source_tactics = leaf.path_certificate()?.to_proof_tactics();
        let region_simp = context_execution.presentation.region_simp;
        let proof_site = leaf.execution_view()?.context.constants.proof_site.clone();
        let invariants_close_requested = context_execution.core.region_invariants_close_requested;
        // A path that left through `break` is an exit, not a back edge: it
        // owes no invariant and no measure, and the loop rule joins it with
        // the loop's other exits instead of returning it to the head.
        let is_break_exit = context_frontier.loop_control.is_exit();
        let is_return_exit = context_frontier.is_at_function_exit();
        let is_natural_return_exit = natural_loop
            && (is_return_exit
                || matches!(
                    context_frontier.loop_control,
                    crate::kernel::proof::LoopControlExit::NaturalExit(_)
                ));
        let is_terminal_return_exit = is_return_exit || is_natural_return_exit;
        let has_retained_invariant_body =
            context_execution.core.checked_invariant_lowerings.is_some();
        let statement_index = context_frontier.next_statement_index;
        let (closer_index, closer_source, closer_name, closer_class) =
            if let Some(step) = context_execution.presentation.invariant_closer_step {
                (
                    step.tactic_index,
                    step.source_index,
                    "close_invariants",
                    "simple",
                )
            } else if let Some((tactic_index, source_index)) = region_simp {
                (tactic_index, source_index, "simp", "smart")
            } else {
                (tactics.len(), tactics.len(), "assumption", "simple")
            };
        let _timing = crate::instrumentation::enabled().then(|| {
            if crate::instrumentation::starts_enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(
                        crate::instrumentation::TacticEvent {
                            claim: claim_label.clone(),
                            tactic_index: closer_index,
                            tactic_name: closer_name.to_string(),
                            class: closer_class.to_string(),
                            statement_index,
                            source_index: closer_source,
                        },
                    ),
                );
            }
            let timing_context = TimingTacticContext {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class.to_string(),
                statement_index,
            };
            push_timing_tactic(timing_context.clone());
            TacticTiming {
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class,
                statement_index,
                start: std::time::Instant::now(),
                context: timing_context,
            }
        });
        let bundle_checkpoint = leaf.checkpoint();
        // A region-level `simp` is a Surface planner. Establish each named
        // invariant through the checked proposition Proof before asking the
        // kernel to close the bundle. In particular, upper-bound extension
        // now becomes a nested proof `if` here instead of recursive search in
        // proposition reasoning.
        let mut leaf = leaf;
        if is_terminal_return_exit || is_break_exit {
            // Nothing is closed on an exit path, so nothing is planned here.
        } else if has_retained_invariant_body {
            // A completed body is bound to this exact premise store. Validate
            // it before skipping preplanning; a source close request alone
            // is not evidence. Adding further `have`s would stale the body.
            leaf.validate_loop_invariant_bundle(invariant_checks, ranking_measures)?;
        } else if region_simp.is_some() {
            if invariant_surfaces.len() != invariant_checks.len() {
                return Err(leaf.step_error(
                    "surface invariants do not align with the lowered invariant bundle",
                ));
            }
            for (index, invariant) in invariant_surfaces.iter().enumerate() {
                let scope = leaf.begin_have(invariant.clone())?;
                let Some(proved) =
                    scope.try_simp_closure_with_surfaces(&invariant_premise_surfaces[..=index])?
                else {
                    continue;
                };
                leaf = proved.join()?;
            }
        }
        let checked = if is_terminal_return_exit || is_break_exit {
            leaf.clone()
        } else if invariant_checks.is_empty()
            && ranking_measures.is_empty()
            && structural_measure.is_none()
        {
            leaf.check_loop_state_join(
                preservation.loop_entry_state(),
                preservation.state(),
                condition,
                &[],
                preservation.binders(),
                structural_measure,
                environment.function.composite_resource_definitions(),
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} state join): {}",
                    error.message()
                ))
            })?;
            leaf.clone()
        } else {
            leaf.prepare_loop_invariant_bundle(
                preservation.loop_entry_state(),
                preservation.state(),
                condition,
                invariant_checks,
                ranking_measures,
                structural_measure,
                &invariant_surfaces,
                preservation.binders(),
                environment.function.composite_resource_definitions(),
                do_while,
            )
            .and_then(|prepared| match prepared {
                Some(proof) => {
                    proof.certify_loop_invariant_bundle(invariant_checks, ranking_measures)
                }
                // A do-while exit has no continuing back edge to certify.
                None => Ok(leaf.clone()),
            })
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` (loop {loop_index} invariant bundle preservation): {}",
                    error.message()
                ))
            })?
        };
        let checked_execution = checked.execution_view()?.execution.clone();
        if is_natural_return_exit {
            // A natural-cycle return is a terminal loop exit. It does not
            // owe the loop invariant or ranking bundle; the kernel joins its
            // checked return path with the other exits.
            let exit = CLoopFinalExitCandidate::new(
                (*checked_execution.core.state).clone(),
                checked.facts().to_vec(),
            )
            .with_loan_evidence(checked_execution.core.loan_evidence().clone());
            if !final_exit_candidates.contains(&exit) {
                final_exit_candidates.push(exit);
            }
        } else if is_return_exit {
            // The kernel's independently checked body execution contributes
            // the actual function-return outcome. This proof leaf only shows
            // that the source preservation path reached that terminal point;
            // it is neither a back edge nor a candidate for the loop guard's
            // next evaluation.
        } else if is_break_exit {
            // The exit is this path's own state and the facts it retained
            // there. The loop rule joins it with every other exit into the
            // single successor, so nothing about this path is dropped and
            // nothing about it is assumed to satisfy the invariants.
            let exit = CLoopBreakExit::new(
                (*checked_execution.core.state).clone(),
                checked.facts().to_vec(),
            )
            .with_loan_evidence(checked_execution.core.loan_evidence().clone());
            if !break_exits.contains(&exit) {
                break_exits.push(exit);
            }
        } else {
            let mut join_facts = checked.facts().to_vec();
            join_facts.extend(
                checked_execution
                    .core
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            join_facts.extend(crate::kernel::certified_store_equations(
                &checked_execution.core.effect_facts,
            ));
            // The body must return to the head it started from, which carries
            // the loop's own resource context when the loop declares one.
            let join_assumptions = assumptions_from_propositions(&join_facts);
            let back_edge_fails = crate::kernel::c_loop_state_with_loop_binders_rebound(
                preservation.state(),
                &checked_execution.core.state,
                preservation.binders(),
                &join_assumptions,
            )
            .and_then(|rebound| {
                crate::kernel::c_loop_state_components_match_at_back_edge(
                    preservation.state(),
                    &crate::kernel::c_loop_state_with_head_binder_models(
                        &rebound,
                        preservation.state(),
                        preservation.binders(),
                    ),
                    &join_assumptions,
                    environment.function.composite_resource_definitions(),
                )
            })
            .is_err();
            // A `do ... while` reads its guard after the body, so the state a
            // body path ends in is the loop's only guard-false exit. Recording
            // it only when the back edge fails to close exported no exit at
            // all for a body that does close it, and every claim after the
            // loop was then vacuous.
            if do_while || back_edge_fails {
                let candidate = CLoopFinalExitCandidate::new(
                    (*checked_execution.core.state).clone(),
                    checked.facts().to_vec(),
                )
                .with_loan_evidence(checked_execution.core.loan_evidence().clone());
                if !final_exit_candidates.contains(&candidate) {
                    final_exit_candidates.push(candidate);
                }
            }
        }
        let closer_tactics = if is_terminal_return_exit
            || is_break_exit
            || (invariant_checks.is_empty()
                && ranking_measures.is_empty()
                && structural_measure.is_none())
            || invariants_close_requested
        {
            Vec::new()
        } else {
            checked
                .certificate_since(&bundle_checkpoint)?
                .to_proof_tactics()
                .to_vec()
        };
        let omitted_frontier_preservation = environment
            .frontier_loop_source
            .is_some_and(|source| source.preserve_source_index.is_none());
        if !omitted_frontier_preservation
            && region_simp.is_some_and(|(_, source_index)| {
                // Region simp is deferred by the preservation driver, so it
                // never opens an active tactic capture. Match its selected
                // source occurrence just as the driver's explicit steps do.
                proof_site.as_ref().is_some_and(|site| {
                    selected_tactic_index_for_site(expansion_capture.as_deref(), site)
                        == Some(source_index)
                })
            })
        {
            let capture = ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(&closer_tactics)
                    .expect("the loop closer is a simple proof")
                    .steps()
                    .to_vec(),
                ..ProofCertificateBuilder::default()
            };
            // A region whose invariants are already closed has a
            // legitimately empty closer: the selected `simp` contributes no
            // surface tactics and its exact expansion removes it.
            finish_tactic_expansion_capture(
                expansion_capture.as_deref_mut(),
                &capture,
                closer_tactics.is_empty(),
            );
        }
        let (prefix, selected_offsets) =
            certificate_leaf_for_case_path(&claim_label, &source_tactics, &case_path)?;
        let case_offsets = selected_offsets
            .or_else(|| recorded_case_offsets(&context_execution.presentation, case_path.len()));
        let mut leaf_tactics = prefix.to_proof_tactics().to_vec();
        leaf_tactics.extend(closer_tactics);
        let certificate = ProofCertificate::from_proof_tactics(&leaf_tactics).map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` produced an invalid preservation leaf certificate: {error:?}"
            ))
        })?;
        certificate_paths.push(PathCertificate {
            case_path: case_path.clone(),
            case_offsets,
            certificate,
        });
    }
    if let Some(frontier) = deferred_frontier {
        return Err(frontier);
    }
    let certificate = merge_phase_path_aligned_certificates(&claim_label, certificate_paths)?;
    Ok(LoopPreservationProofResult {
        certificate,
        final_exit_candidates,
        break_exits,
        nested_loop_rules,
    })
}
