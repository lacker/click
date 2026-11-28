use super::*;
use std::sync::Arc;

/// The proof scope a loop's phase proofs are written in.
///
/// `initialize` and `maintain` bodies are written where the `loop` tactic
/// was written: inside whatever proof `match` arm, `let { ... } = unfold(...)` binding,
/// or call-result binder reached that frontier. Their sub-proofs are built
/// from fresh roots, so the scope has to be attached explicitly or a `have`
/// goal inside a phase body would fail to resolve a name the loop's own
/// clauses resolve. `ExecutionProofEnvironment::proof_locals` is the same
/// map the clause re-annotation uses.
fn phase_proof_scope(
    environment: &ExecutionProofEnvironment<'_>,
) -> PersistentBinderMap<SyntaxTerm> {
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
        if let Requirement::Resource(ResourceClause::Named { binding, .. }) = requirement {
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

/// The written invariants of `loop_index`, read through the proof scope the
/// clause was written under: a clause bound inside a proof `match` arm names
/// that arm's bindings, and lowering sees the values they stand for.
fn loop_invariant_surfaces(
    environment: &ExecutionProofEnvironment<'_>,
    loop_index: usize,
    claim_label: &str,
) -> Result<Vec<SyntaxProposition>, ClickError> {
    environment
        .function_block
        .structural_clauses()
        .for_loop(loop_index).into_iter()
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

/// The loop's declared `decreases` components, as the resolved clause holds
/// them. Empty when no clause declares a ranking measure or a clause's
/// bindings do not resolve; the descent member then has no written spelling.
fn loop_ranking_surfaces(
    environment: &ExecutionProofEnvironment<'_>,
    loop_index: usize,
) -> Vec<SyntaxTerm> {
    environment
        .function_block
        .structural_clauses()
        .for_loop(loop_index)
        .into_iter()
        .filter_map(|clause| clause.resolved().ok())
        .find_map(|clause| {
            clause
                .decreases()
                .map(|measure| measure.components().to_vec())
        })
        .unwrap_or_default()
}

/// Pair the kernel's selected loop-head clauses with generated spellings that
/// explicitly read the iteration-entry state. The written, unqualified
/// clauses retain their source meaning in the enclosing presentation map.
fn record_loop_entry_invariants(
    surface_propositions: &mut SurfacePropositionMap,
    invariant_surfaces: &[SyntaxProposition],
    preservation: &crate::kernel::LoopPreservationContext,
    statement_index: usize,
) -> Result<Vec<SyntaxProposition>, ClickError> {
    if invariant_surfaces.len() != preservation.invariant_propositions().len() {
        return Err(ClickError::new(
            "loop-head invariant results do not align with declared clauses",
        ));
    }
    invariant_surfaces
        .iter()
        .zip(preservation.invariant_propositions())
        .map(|(surface, kernel)| {
            let anchored = surface_at_program_point(
                surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Region(statement_index),
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
    /// `have`, in declaration order: each entry holds, for one invariant,
    /// the absolute source index and written body of each `have` naming it.
    /// An invariant owes its side conditions as goals of their own beside
    /// its body, so it may be named once, with a body run for each goal, or
    /// once per goal it owes, in the order they are owed.
    invariant_bodies: Option<Vec<Vec<(usize, &'a SourceProof)>>>,
    /// The proof every invariant runs when the script does not name them
    /// individually.
    shared: SourceProof,
    /// The absolute source index of each tactic of `shared`, when it is a
    /// written script.
    shared_source_indices: Vec<usize>,
    /// Absolute source indices of the trailing `close()` closers: a smart
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
            shared_source_indices: Vec::new(),
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
            ProofTactic::UnfoldProposition(_) | ProofTactic::UnfoldFunction(_) => false,
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
    // One `have` per invariant, in declaration order, is read position by
    // position: two invariants may state one proposition and each keeps its
    // own body. Otherwise each invariant takes every consecutive `have`
    // naming it, one per goal it owes.
    let one_each = rest.len() >= invariant_items.len()
        && rest.iter().zip(invariant_items).all(|(tactic, item)| {
            matches!(tactic, ProofTactic::Have(have)
                    if &have.proposition == item.proposition())
        })
        && rest[invariant_items.len()..].iter().all(|tactic| {
            matches!(
                tactic,
                ProofTactic::Known | ProofTactic::Close | ProofTactic::Solve
            )
        });
    let mut grouped: Vec<Vec<(usize, &SourceProof)>> = Vec::new();
    let mut consumed = 0;
    for item in invariant_items {
        let mut bodies = Vec::new();
        while let Some(ProofTactic::Have(have)) = rest.get(consumed)
            && &have.proposition == item.proposition()
            && !(one_each && !bodies.is_empty())
        {
            bodies.push((source_indices[helper_end + consumed], &have.proof));
            consumed += 1;
        }
        if bodies.is_empty() {
            break;
        }
        grouped.push(bodies);
    }
    let names_every_invariant = grouped.len() == invariant_items.len()
        && rest[consumed..].iter().all(|tactic| {
            matches!(
                tactic,
                ProofTactic::Known | ProofTactic::Close | ProofTactic::Solve
            )
        });
    let invariant_bodies = names_every_invariant.then_some(grouped);
    // A closing call that stands for the rest of the phase is a whole-phase
    // closer. An earlier one belongs to an individual invariant proof.
    let closer_start = if names_every_invariant {
        helper_end + consumed
    } else {
        tactics.len().saturating_sub(1)
    };
    let closers = source_indices[closer_start.min(tactics.len())..]
        .iter()
        .copied()
        .zip(&tactics[closer_start.min(tactics.len())..])
        .filter(|(_, tactic)| matches!(tactic, ProofTactic::Close | ProofTactic::Solve))
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
        shared_source_indices: source_indices[helper_end..].to_vec(),
        closers,
    }
}

/// Source positions derived once with the verification layout. Expansion
/// consumes retained evidence without interpreting the source layout again.
struct InitializePhaseExpansion {
    helpers: usize,
    individual_bodies: bool,
    sites: Vec<usize>,
    /// The first tactic of the script every invariant runs.
    shared_start: Option<usize>,
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
            shared_start: layout.shared_source_indices.first().copied(),
        }
    }

    /// The source index a closer's expansion replaces from. The expansion
    /// is one step per invariant, each holding the whole shared script, so
    /// it stands for every shared tactic written before the closer too.
    fn replaces_from(&self, selected: usize) -> Option<usize> {
        if self.individual_bodies || !self.sites.contains(&selected) {
            return None;
        }
        self.shared_start.filter(|start| *start < selected)
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
    invariant_checks: &[LoopInvariantCheck],
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<CheckedLoopInitialization, ClickError> {
    let source = environment.frontier_loop_source;
    let claim_label = source.claim_label.clone();
    let initialize_source_index = source
        .initialize_source_index
        .unwrap_or(source.loop_source_index);
    let initialize_site = source.proof_site.as_ref();
    let mut recorded_states = context.recorded_states.clone();
    for label in environment
        .function_block
        .structural_clauses()
        .for_loop(loop_index)
        .into_iter()
        .filter_map(StructuralClause::label)
    {
        recorded_states.label_loop(loop_index, label);
    }
    recorded_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Loop(loop_index),
            kind: ProgramPointKind::Entry,
        },
        context.state.clone(),
    );
    let invariant_items = clause.items().iter().collect::<Vec<_>>();
    // Generated initialization steps belong to the explicit phase tactic when
    // one exists, or to the enclosing `loop` keyword for an omitted phase.
    // Computing the source statement is only worth it when timings are read.
    let timings_enabled = crate::instrumentation::enabled();
    let initialize_statement_index = if timings_enabled {
        environment
            .source_layout
            .loop_body_entry(loop_index)
            .unwrap_or(0)
    } else {
        0
    };
    let entry_goals = crate::kernel::loop_entry_goals(
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
            ))
            .with_proof_refusal(ProofRefusal::Contract);
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
            ))
            .with_proof_refusal(ProofRefusal::IncompleteProof);
        }
        ClickError::new(format!("`{claim_label}`: {message}"))
    })?;
    if entry_goals.declarations().len() != invariant_items.len() {
        return Err(ClickError::new(format!(
            "loop {loop_index} entry has {} lowered declarations for {} written invariants",
            entry_goals.declarations().len(),
            invariant_items.len(),
        ))
        .with_kind(ClickErrorKind::Internal));
    }
    let layout = initialize_script_layout(proof, &invariant_items, initialize_source_index);
    let mut phase = Proof::for_fixed_state_frontier_of_list(
        &claim_label,
        0,
        &context.pure_facts,
        environment.parameter_binding(),
        FixedStateFrame::new(
            environment.initial_state,
            &context.state,
            None,
            &recorded_states,
        ),
        &context.surface_propositions,
        environment.spec_definitions,
        environment.theorem_environment,
        &[],
    )
    .with_surface_local_scope(&phase_proof_scope(environment))
    // The entry checks the invariants before the first pass.
    .with_loop_iterations(&crate::kernel::IntegerTerm::constant(0.into()))
    .with_nested_tactic_capture(
        expansion_capture
            .as_deref()
            .and_then(|capture| capture.nested_for_site(initialize_site)),
    );
    let phase_site = phase.site().clone();
    for (source_index, helper) in &layout.helpers {
        // Address the helper, and so every tactic written in its body, by
        // its source position, as the other phases address theirs.
        phase = phase.at_source_tactic(*source_index);
        let checkpoint = phase.checkpoint();
        phase = match helper {
            ProofTactic::UnfoldProposition(target) => phase
                .driver()
                .apply_step(ProofStep::UnfoldProposition(target.clone()))?,
            ProofTactic::UnfoldFunction(application) => phase
                .driver()
                .apply_step(ProofStep::UnfoldFunction(application.clone()))?,
            ProofTactic::Have(have) => {
                check_loop_phase_have(&phase, have, "initialization", false)?.0
            }
            _ => unreachable!("only unfold and have steps are phase helpers"),
        };
        if let Some(site) = initialize_site
            && capture_selects_source(expansion_capture.as_deref(), site, *source_index)
        {
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                *source_index,
                &phase.certificate_since(&checkpoint)?.to_proof_tactics(),
            );
        }
    }
    // The invariant bodies are not the last helper's.
    phase = phase.at_site(&phase_site);
    let mut completions = Vec::new();
    for (invariant_index, (item, goals)) in invariant_items
        .iter()
        .zip(entry_goals.declarations())
        .enumerate()
    {
        let own_bodies = layout
            .invariant_bodies
            .as_ref()
            .and_then(|bodies| bodies.get(invariant_index));
        if let Some(bodies) = own_bodies
            && bodies.len() != 1
            && bodies.len() != goals.len()
        {
            return Err(ClickError::new(format!(
                "loop {loop_index} {} owes {} entry goals but the `initialize` script names it {} times; name it once, or once per goal",
                item.title(invariant_index),
                goals.len(),
                bodies.len()
            )).with_proof_refusal(ProofRefusal::Tactic).with_failed_tactic("loop"));
        }
        // With one body the invariant's goals all run it; the timing label
        // below describes that first body either way.
        let own_body = own_bodies.and_then(|bodies| bodies.first()).copied();
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
        for (goal_index, obligation) in goals.iter().enumerate() {
            // The `have` written for this goal, when the invariant is named
            // once per goal it owes.
            let own_body = own_bodies
                .and_then(|bodies| bodies.get(goal_index).or_else(|| bodies.first()))
                .copied();
            let invariant_proof = own_body.map_or(&layout.shared, |(_, body)| body);
            let body_sites = invariant_proof.tactics().map(|tactics| match own_body {
                Some((index, _)) => {
                    let have_site = phase_site.at_source_tactic(index);
                    (0..tactics.len())
                        .map(|position| have_site.in_have_body(position))
                        .collect::<Vec<_>>()
                }
                None => layout
                    .shared_source_indices
                    .iter()
                    .map(|&index| phase_site.at_source_tactic(index))
                    .collect(),
            });
            let checkpoint = phase.checkpoint();
            let scope = phase.begin_loop_entry_goal(item.proposition().clone(), obligation)?;
            let body = check_loop_phase_goal(
                &scope,
                invariant_proof,
                body_sites.as_deref(),
                "initialization",
            );
            let checked = body.map_err(|error| {
                // The kernel already refused this declaration and says why.
                if obligation.is_impossible_goal()
                    && let Some(reason) = obligation.context()
                {
                    return error
                        .with_rewritten_place(|detail| Some(format!("{reason}\n{detail}")));
                }
                // Name the judgment that was compared: a declaration owes its
                // side conditions as goals of their own beside its body, so
                // "invariant N" alone does not say which one failed.
                let owed =
                    crate::surface::proof::surface_synthesis::synthesize_surface_proposition(
                        obligation.proposition(),
                        environment.parameter_binding(),
                        &context.state,
                    )
                    .map(|surface| crate::surface::printing::source_click_proposition(&surface))
                    .unwrap_or_else(|| {
                        let (parameters, arguments) = phase.diagnostic_naming_tables();
                        crate::surface::diagnostics::describe_stated_fact(
                            obligation.proposition(),
                            ParameterBinding::new(&parameters, &arguments),
                        )
                    });
                let error = if environment
                    .function_block
                    .signature()
                    .rust_loop_iterators()
                    .get(loop_index)
                    .and_then(Option::as_ref)
                    .is_some_and(|iterator| iterator.range_bounds.is_some())
                {
                    // The bound can hold the same value as a parameter at
                    // entry. Keep the written accessor beside the lowered
                    // obligation, where they may share a value spelling.
                    let written =
                        crate::surface::printing::source_click_proposition(item.proposition());
                    error.with_rewritten_place(|reason| {
                        Some(format!("written invariant `{written}`: {reason}"))
                    })
                } else {
                    error
                };
                error.with_rewritten_place(|reason| {
                    Some(format!(
                        "loop {loop_index} {} entry, owing `{owed}`: {reason}",
                        item.title(invariant_index)
                    ))
                })
            })?;
            completions.push(checked.completed_loop_entry_goal()?);
            phase = checked.join()?;
            if let Some((selected, _)) = own_body
                && let Some(site) = initialize_site
                && capture_selects_source(expansion_capture.as_deref(), site, selected)
            {
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    selected,
                    &phase.certificate_since(&checkpoint)?.to_proof_tactics(),
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

fn check_loop_phase_have<'a>(
    phase: &Proof<'a>,
    have: &ProofHave,
    phase_name: &str,
    record_conclusion: bool,
) -> Result<(Proof<'a>, Option<Proposition>), ClickError> {
    let scope = phase.driver().open_have(have.proposition.clone())?;
    let conclusion = record_conclusion
        .then(|| scope.body().goal().cloned())
        .flatten();
    let proof = check_loop_phase_goal(&scope, &have.checking_proof(), None, phase_name)?.join()?;
    Ok((proof, conclusion))
}

/// Source execution and smart planning share the checked scope. An explicit
/// failure is final; no other phase body or certificate checker is tried.
/// `sites`, when given, addresses each tactic of a written script.
fn check_loop_phase_goal<'a>(
    scope: &proof_object::ProofScope<'a>,
    source: &SourceProof,
    sites: Option<&[ProofStepSite]>,
    phase_name: &str,
) -> Result<proof_object::ProofScope<'a>, ClickError> {
    let _origin = source
        .uses_implicit_tail()
        .then(|| crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit solve"));
    let did_search = !matches!(source, SourceProof::Script(_));
    let checked = match source {
        SourceProof::Tactic(SmartTactic::ImplicitTail) => scope.driver().try_solve_closure()?,
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Solve) => {
            (scope).driver().try_solve_closure()?
        }
        SourceProof::Script(tactics) => match sites {
            Some(sites) => scope
                .driver()
                .try_addressed_linear_script(tactics, sites, true)?,
            None => scope
                .driver()
                .try_authoritative_linear_script_reporting(tactics, &mut None, &mut None, true)?,
        },
    }
    .ok_or_else(|| {
        let reason = format!("loop {phase_name} body did not close its goal");
        if did_search {
            scope.body().solve_failure().with_context(reason)
        } else {
            ClickError::new(reason)
        }
    })?;
    if !checked.is_complete() {
        return Err(ClickError::new(format!(
            "loop {phase_name} body retained an open goal"
        )));
    }
    Ok(checked)
}

pub(in crate::surface::proof) struct CheckedLoopInitialization {
    pub(in crate::surface::proof) certificate: ProofCertificate,
    entry_goals: crate::kernel::LoopEntryGoals,
    expansion: InitializePhaseExpansion,
    completions: Vec<crate::kernel::proof::CheckedProposition>,
}

impl CheckedLoopInitialization {
    pub(in crate::surface::proof) fn phase_closer_expansion(
        &self,
        selected: usize,
        certificate: &ProofCertificate,
    ) -> Option<Vec<ProofTactic>> {
        let expansion = self.expansion.expand(selected, certificate)?;
        if let Some(from) = self.expansion.replaces_from(selected) {
            crate::surface::expansion::note_expansion_replaces_from(from);
        }
        Some(expansion)
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

// This switch lets proof migration measure the new export boundary while
// production proofs still use the legacy loop rule.
pub(super) fn scoped_loop_exit_facts_enabled() -> bool {
    #[cfg(all(test, not(feature = "fast-gate")))]
    if SCOPED_LOOP_EXIT_FACTS.with(std::cell::Cell::get) {
        return true;
    }
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var_os("CLICK_SCOPED_LOOP_EXIT_FACTS").is_some_and(|value| value == "1")
    })
}

#[cfg(all(test, not(feature = "fast-gate")))]
thread_local! {
    static SCOPED_LOOP_EXIT_FACTS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(all(test, not(feature = "fast-gate")))]
pub(in crate::surface) fn with_scoped_loop_exit_facts<T>(run: impl FnOnce() -> T) -> T {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            SCOPED_LOOP_EXIT_FACTS.set(self.0);
        }
    }
    let _reset = Reset(SCOPED_LOOP_EXIT_FACTS.replace(true));
    run()
}

/// The written candidates are the loop's own proof statements. A nested
/// loop has its own export boundary, and a have body proves its parent goal
/// in a separate scope.
fn loop_exit_claims(clause: &StructuralClause) -> Vec<&SyntaxProposition> {
    use crate::surface::TacticChild;
    let mut pending = [clause.preserve_proof(), clause.otherwise_proof()]
        .into_iter()
        .flatten()
        .filter_map(SourceProof::tactics)
        .flatten()
        .collect::<Vec<_>>();
    let mut claims = Vec::new();
    while let Some(tactic) = pending.pop() {
        match tactic {
            ProofTactic::Have(have) => claims.push(&have.proposition),
            ProofTactic::Loop(_) => {}
            _ => pending.extend(
                tactic
                    .children()
                    .into_iter()
                    .filter_map(|child| match child {
                        TacticChild::Continuing(proof) => proof.tactics(),
                        TacticChild::Obligation(_) => None,
                    })
                    .flatten(),
            ),
        }
    }
    claims
}

fn loop_exit_recorded_states(
    loop_index: usize,
    state: &ExecutionState,
    iterations: &crate::kernel::IntegerTerm,
    context: &PlanningExecutionContext,
    environment: &ExecutionProofEnvironment<'_>,
) -> RecordedStates {
    let mut recorded_states = context.recorded_states.clone();
    for (kind, state) in [
        (ProgramPointKind::Entry, &context.state),
        (ProgramPointKind::Exit, state),
    ] {
        record_code_region_program_state(
            &mut recorded_states,
            environment.function_block,
            CodeRegion::Loop(loop_index),
            kind,
            state.clone(),
        );
    }
    let iterations = crate::kernel::KernelTermImport::default().integer(&iterations.clone().into());
    recorded_states.record_loop_iterations_root(loop_index, iterations);
    recorded_states
}

fn loop_exit_scope<'a>(
    state: &'a ExecutionState,
    iterations: &crate::kernel::IntegerTerm,
    recorded_states: &'a RecordedStates,
    facts: &'a PureFactList,
    context: &'a PlanningExecutionContext,
    environment: &'a ExecutionProofEnvironment<'a>,
) -> Proof<'a> {
    Proof::for_fixed_state_frontier_of_list(
        &environment.frontier_loop_source.claim_label,
        0,
        facts,
        environment.parameter_binding(),
        FixedStateFrame::new(environment.initial_state, state, None, recorded_states),
        &context.surface_propositions,
        environment.spec_definitions,
        environment.theorem_environment,
        &[],
    )
    .with_surface_local_scope(&phase_proof_scope(environment))
    .with_loop_iterations(iterations)
}

/// Check the experimental export interface against the actual outer scope.
/// Exit-private proof locals and historical points are absent from this frame.
pub(super) fn scoped_loop_exit_facts(
    loop_index: usize,
    state: &ExecutionState,
    iterations: &crate::kernel::IntegerTerm,
    exits: &[(ExecutionState, crate::kernel::ExecutionFacts)],
    facts: &crate::kernel::ExecutionFacts,
    context: &PlanningExecutionContext,
    environment: &ExecutionProofEnvironment<'_>,
) -> (Vec<bool>, Vec<Proposition>) {
    use crate::surface::proof::raise_lower_audit::{self, RoundTrip};

    let recorded_states =
        loop_exit_recorded_states(loop_index, state, iterations, context, environment);
    let outer = loop_exit_scope(
        state,
        iterations,
        &recorded_states,
        &context.pure_facts,
        context,
        environment,
    );
    let claims = environment
        .function_block
        .structural_clauses()
        .for_loop(loop_index)
        .map_or_else(Vec::new, loop_exit_claims);
    let addresses_in_scope = |proposition: &Proposition| {
        !crate::kernel::proof::term_rewrite::proposition_pointer_terms(proposition)
            .iter()
            .any(|address| {
                matches!(address.base, AddressBase::AutomaticLocal { .. })
                    && [&context.state, state].into_iter().all(|visible| {
                        visible
                            .locals()
                            .name_for_slot(&address.with_offset(AddressOffset::constant(0)))
                            .is_none()
                    })
            })
    };
    let mut written_exports = BTreeSet::new();
    if !claims.is_empty() {
        let exit_inputs = exits
            .iter()
            .map(|(state, facts)| {
                let mut available = context.pure_facts.clone();
                available.extend(facts.iter().map(|fact| fact.proposition().clone()));
                (
                    loop_exit_recorded_states(loop_index, state, iterations, context, environment),
                    available,
                )
            })
            .collect::<Vec<_>>();
        let exit_scopes = exits
            .iter()
            .zip(&exit_inputs)
            .map(|((state, _), (records, available))| {
                loop_exit_scope(state, iterations, records, available, context, environment)
            })
            .collect::<Vec<_>>();
        let lower = |scope: &Proof<'_>, claim| {
            without_open_obligation_probe(|| {
                scope.lower_surface_proposition_direct(claim, "written loop exit fact")
            })
        };
        for claim in claims {
            let Ok(joined) = lower(&outer, claim) else {
                continue;
            };
            if addresses_in_scope(&joined)
                && exit_scopes.iter().all(|exit| {
                    lower(exit, claim)
                        .is_ok_and(|lowered| exit.facts().has_stated_conjunct(&lowered))
                })
            {
                written_exports.insert(joined);
            }
        }
    }

    let admitted = facts
        .iter()
        .map(|fact| {
            let proposition = fact.proposition();
            if written_exports.remove(proposition) {
                return true;
            }
            if !addresses_in_scope(proposition) {
                return false;
            }
            let Some(spelling) = outer.structural_proposition_candidate(proposition) else {
                return false;
            };
            let lowered = without_open_obligation_probe(|| {
                outer.lower_surface_proposition_direct(&spelling, "loop exit fact")
            });
            lowered.is_ok_and(|lowered| {
                matches!(
                    raise_lower_audit::classify(proposition, &lowered),
                    RoundTrip::Same | RoundTrip::Polarity
                )
            })
        })
        .collect();
    (admitted, written_exports.into_iter().collect())
}

pub(in crate::surface::proof) fn verify_loop_otherwise(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    tactics: &[ProofTactic],
    loop_entry: &ExecutionState,
    exit_state: &ExecutionState,
    exit_facts: &crate::kernel::ExecutionFacts,
    guard_points: Option<&RecordedRegionPoints>,
    context: &PlanningExecutionContext,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<(crate::kernel::ExecutionFacts, ProofCertificate), ClickError> {
    let source = environment.frontier_loop_source;
    let mut recorded_states = context.recorded_states.clone();
    record_code_region_program_state(
        &mut recorded_states,
        environment.function_block,
        CodeRegion::Loop(loop_index),
        ProgramPointKind::Entry,
        loop_entry.clone(),
    );
    if let Some(points) = guard_points {
        recorded_states.record_region_points(points);
    }
    let mut available = context.pure_facts.clone();
    available.extend(exit_facts.iter().map(|fact| fact.proposition().clone()));
    let mut phase = Proof::for_fixed_state_frontier_of_list(
        &source.claim_label,
        0,
        &available,
        environment.parameter_binding(),
        FixedStateFrame::new(
            environment.initial_state,
            exit_state,
            None,
            &recorded_states,
        ),
        &context.surface_propositions,
        environment.spec_definitions,
        environment.theorem_environment,
        &[],
    )
    .with_surface_local_scope(&phase_proof_scope(environment))
    .with_nested_tactic_capture(
        expansion_capture
            .as_deref()
            .and_then(|capture| capture.nested_for_site(source.proof_site.as_ref())),
    );
    let initial_facts = phase.facts().clone();
    let scoped_exits = scoped_loop_exit_facts_enabled();
    let mut explicit_facts = Vec::new();
    let mut index = source
        .otherwise_source_index
        .unwrap_or(source.loop_source_index);
    for tactic in tactics {
        let ProofTactic::Have(have) = tactic else {
            unreachable!("otherwise was validated as a sequence of have tactics");
        };
        phase = phase.at_source_tactic(index);
        let checkpoint = phase.checkpoint();
        let (next, conclusion) = check_loop_phase_have(&phase, have, "otherwise", true)?;
        phase = next;
        explicit_facts.extend(conclusion);
        if let Some(site) = source.proof_site.as_ref()
            && capture_selects_source(expansion_capture.as_deref(), site, index)
        {
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                index,
                &phase.certificate_since(&checkpoint)?.to_proof_tactics(),
            );
        }
        index += source_tactic_count(std::slice::from_ref(tactic));
    }
    let facts = if scoped_exits {
        explicit_facts
    } else {
        let mut introduced = phase
            .facts()
            .introduced_since(&initial_facts)
            .expect("checked have extends the phase facts");
        // A checked `have` may use a conclusion already present in the phase.
        // The exit must still state it for the join to rebind its model.
        let introduced_set = introduced.iter().collect::<BTreeSet<_>>();
        explicit_facts.retain(|fact| !introduced_set.contains(fact));
        introduced.extend(explicit_facts);
        introduced
    };
    Ok((
        facts.into_iter().map(ExecutionPureFact::new).collect(),
        phase.certificate(),
    ))
}

/// The body the automatic closer planned for a loop with no written
/// `maintain` proof.
pub(in crate::surface::proof) struct AutomaticLoopBody {
    pub(in crate::surface::proof) certificate: ProofCertificate,
}

pub(in crate::surface::proof) fn plan_automatic_loop_preservation_body(
    loop_index: usize,
    preservation: &crate::kernel::LoopPreservationContext,
    pure_facts: &PureFactList,
    enclosing_states: &RecordedStates,
    body: &ProgramStatement,
    update: Option<&Arc<ProgramStatement>>,
    test: Option<&crate::kernel::LoopTestRegion>,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<AutomaticLoopBody, ClickError> {
    let claim_label = environment.frontier_loop_source.claim_label.clone();
    let source_layout = environment.source_layout.clone();
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let continuation =
        crate::kernel::program_loop_continuation(update.map(|update| update.as_ref()), test);
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: Arc::new(crate::kernel::program_loop_preservation_pass(
                body,
                update.map(|update| update.as_ref()),
                test.expect("loop preservation owns its test"),
            )),
        },
        region: ExecutionRegionKind::LoopBody,
        in_loop_body: true,
        loop_phase_source: test.map(|test| crate::kernel::proof::LoopPhaseSource {
            header_index: loop_body_statement_index - 1,
            test_position: test.position,
        }),
        loop_update: continuation.as_ref().and_then(|update| {
            source_layout
                .loop_continuation_entry(loop_index)
                .map(|index| (update.clone(), index))
        }),
        natural_backedge_target: source_layout.natural_loop_target(loop_index),
        natural_exit_target: source_layout.natural_exit_target(loop_index),
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    // A preservation proof is nested in the enclosing execution proof.
    // Its marks still name fixed states; share their persistent map prefix.
    let mut recorded_states = enclosing_states.clone();
    let constants = ExecutionProofConstants {
        proof_site: environment.frontier_loop_source.proof_site.clone(),
        source_layout,
        function_entry_state: Some(environment.initial_state.clone()),
        function_source_registry: environment.function_source_registry.clone(),
        parameter_index: environment.parent_constants.parameter_index.clone(),
        parameter_naming: environment.parent_constants.parameter_naming.clone(),
        ..ExecutionProofConstants::default()
    };
    record_statement_program_state(
        &mut recorded_states,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_loop_program_state(
        &mut recorded_states,
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
    // The planned body runs on the same head state as the checked one, so
    // it starts its identity counter where the head left it, for the same
    // reason (`verify_one_loop_preservation_proof`). Starting at the base of
    // the range gave a join in the planned body the identity the head's
    // havoc had already given a local, and the two became one value.
    let mut body_execution = ExecutionProofState::at_entry_with_descent(
        preservation.state().clone(),
        frontier,
        recorded_states,
        surface_propositions,
        PersistentSequence::default(),
        environment.function,
        environment.function_environment,
    )?;
    body_execution
        .core
        .advance_kernel_variable_mark(preservation.next_kernel_variable())
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    let root = Proof::for_execution_frontier(
        &claim_label,
        0,
        body_execution,
        pure_facts.clone(),
        constants.clone(),
        environment.function_block,
        environment.function,
        environment.parsed_function,
        environment.arguments,
        environment.function_environment,
        environment.resource_environment,
        environment.spec_definitions,
        environment.theorem_environment,
    )
    .with_surface_local_scope(&phase_proof_scope(environment))
    .with_loop_iterations(preservation.iterations());
    let completed = walk_loop_body(root)?;
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
    Ok(AutomaticLoopBody {
        certificate: merge_phase_path_aligned_certificates(&claim_label, paths)?,
    })
}

/// Walks a loop body from `root` to its ends, one smart step at a time, as a
/// function's implicit tail walks its body: each C `if` whose condition the
/// path does not decide splits, and each arm runs on as its own path to the
/// back edge, a `break`, a `continue` or function exit, where it closes the
/// bundle with everything it established. The walk shares the implicit
/// tail's step and split budgets and its refusal past them, which names the
/// explicit join, `branch ensuring { ... }`. Returns the paths that reached
/// one of the body's ends or function exit.
pub(in crate::surface::proof) fn walk_loop_body<'a>(
    root: Proof<'a>,
) -> Result<Vec<Proof<'a>>, ClickError> {
    let mut pending = vec![root];
    let mut completed = Vec::new();
    let mut steps = 0usize;
    let mut splits = 0usize;
    while let Some(proof) = pending.pop() {
        if proof.is_at_region_boundary() || proof.execution_view()?.frontier.is_at_function_exit() {
            completed.push(proof);
            continue;
        }
        proof.charge_execute_step(&mut steps, splits)?;
        let view = proof.execution_view()?;
        let at_branch = view
            .context
            .constants
            .source_layout
            .statement(view.frontier.next_statement_index)
            .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }));
        if !at_branch {
            pending.extend(preservation_step_paths(&proof)?);
            continue;
        }
        // A path may already know the condition, for example from assigning
        // a comparison to a Boolean local. Retain its checked branch step.
        let error = match preservation_smart_step(&proof) {
            Ok(stepped) => {
                pending.push(stepped);
                continue;
            }
            Err(error) => error,
        };
        check_verification_deadline()?;
        // A Rust `match` arm's variant test splits into the variants the
        // facts leave live, each its own path to the back edge, as the
        // function's implicit tail splits it and as a written `match` would.
        if proof.is_at_enum_match_test()? {
            let Some(split) = error.path_case_match().cloned() else {
                return Err(error);
            };
            let split = Arc::new(split);
            let prepared = proof.prepare_execution_match(false, 0)?;
            let plan = prepared.plan_execution_match(&split)?;
            splits += 1;
            for index in plan.live_cases() {
                pending.push(prepared.enter_execution_match_arm(&plan, index)?);
            }
            continue;
        }
        let FrontierPosition::StatementEntry { remaining } = &view.frontier.position else {
            return Err(
                proof.step_error("automatic preservation branch is not at a statement entry")
            );
        };
        let (source_statement, _) =
            split_next_source_operation(remaining).map_err(ClickError::new)?;
        let ProgramStatement::If { condition, .. } = source_statement else {
            return Err(proof.step_error("source branch does not match the lowered statement"));
        };
        let condition = surface_program_condition(
            &condition,
            view.state,
            Some(&view.execution.presentation.recorded_states),
        )?;
        let (split, ids) = proof.split_preservation_case(&condition, 0)?;
        splits += 1;
        for id in ids.into_iter().flatten() {
            pending.extend(preservation_step_paths(&split.focus_branch(id)?)?);
        }
    }
    Ok(completed)
}

/// Steps the statement at the frontier. A statement whose successors are
/// path cases, such as a comparison assigned to a local, is first split on
/// the condition that separates them, as the implicit tail splits it, and each
/// case is stepped.
fn preservation_step_paths<'a>(proof: &Proof<'a>) -> Result<Vec<Proof<'a>>, ClickError> {
    let error = match preservation_smart_step(proof) {
        Ok(stepped) => return Ok(vec![stepped]),
        Err(error) => error,
    };
    let Some(condition) = error.path_case_condition() else {
        return Err(error);
    };
    let (split, ids) = proof.split_preservation_case(condition, 0)?;
    ids.into_iter()
        .flatten()
        .map(|id| preservation_smart_step(&split.focus_branch(id)?))
        .collect()
}

pub(in crate::surface::proof) struct LoopPreservationProofResult {
    pub(in crate::surface::proof) return_proofs: Vec<Arc<LoopReturnProof>>,
    pub(in crate::surface::proof) certificate: ProofCertificate,
    pub(in crate::surface::proof) final_exit_candidates: Vec<LoopFinalExitCandidate>,
    /// The body paths that left this loop through `break`, each an exit at
    /// its own state. The loop rule joins them with the guard-false exit.
    pub(in crate::surface::proof) early_exits: Vec<LoopEarlyExit>,
    /// The body paths that left the function through `return`, each with
    /// the value it returned and the state it returned in. The loop rule
    /// exports each as a `Return` outcome of the loop statement.
    pub(in crate::surface::proof) return_exits: Vec<LoopReturnExit>,
    /// The points each path that left the loop recorded during its pass.
    pub(in crate::surface::proof) exit_points: Vec<RecordedRegionPoints>,
    /// Loop rules checked by frontier-local tactics inside this loop's
    /// preservation proof. They are evidence for termination only; the
    /// enclosing contract still uses the outer loop's checked artifact.
    pub(in crate::surface::proof) nested_loop_rules: Vec<VerifiedLoopRule>,
    /// The loop head this preservation proof started from and the states
    /// its body reached when it returned there.
    pub(in crate::surface::proof) back_edges: crate::kernel::LoopBackEdges,
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn verify_one_loop_preservation_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    tactics: &[ProofTactic],
    first_generated_tactic_index: usize,
    preservation: &crate::kernel::LoopPreservationContext,
    pure_facts: &PureFactList,
    enclosing_states: &RecordedStates,
    invariant_checks: &[LoopInvariantCheck],
    ranking_measures: &[crate::kernel::RankingComponent],
    structural_measure: Option<&str>,
    condition: Option<&ProgramExpression>,
    body: &ProgramStatement,
    update: Option<&Arc<ProgramStatement>>,
    test: Option<&crate::kernel::LoopTestRegion>,
    mut guard_points: Option<&mut Vec<RecordedRegionPoints>>,
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<LoopPreservationProofResult, ClickError> {
    // A `cases` that rejoins its arms is noted for the rest of this proof's
    // check, so a back edge that then fails to close says the rejoin dropped
    // what only one arm established.
    let _cases_note = crate::surface::proof::begin_preservation_cases_note();
    let source = environment.frontier_loop_source;
    let claim_label = source.claim_label.clone();
    let preserve_source_index = source
        .preserve_source_index
        .unwrap_or(source.loop_source_index);
    let preserve_site = source.proof_site.as_ref();

    // A trailing shared closer can have a different checked body on each
    // execution leaf. Capture the whole phase so those bodies stay where
    // their premises and memory states were established.
    let capture_shared_closer = tactics.last().is_some_and(|tactic| {
        matches!(
            tactic,
            ProofTactic::CloseInvariants | ProofTactic::CloseInvariantsBy(_)
        )
    }) && expansion_capture.as_deref().is_some_and(|capture| {
        let index = preserve_source_index + source_tactic_count(&tactics[..tactics.len() - 1]);
        preserve_site.is_some_and(|site| capture.selects(site, index))
            && capture
                .batch
                .as_ref()
                .and_then(|batch| batch.targets.get(&index))
                .unwrap_or(capture)
                .nested
                .is_none()
    });

    let mut program = if source.preserve_source_index.is_none() {
        build_generated_certificate_proof(tactics, &claim_label, preserve_source_index)?
    } else {
        build_internal_proof_from_source_index(tactics, preserve_source_index)?
    };
    if first_generated_tactic_index < tactics.len() {
        // Automatic preservation appends planned body steps and a closer
        // after the source-written unfold prefix. They are owned by the loop
        // tactic, not additional source occurrences after `maintain`.
        // Detach them so a later nested clause cannot be mistaken for one of
        // these generated tactics by expand.
        detach_generated_suffix_from_source_indices(&mut program, first_generated_tactic_index);
    }
    let source_layout = environment.source_layout.clone();
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let invariant_surfaces = loop_invariant_surfaces(environment, loop_index, &claim_label)?;
    let continuation =
        crate::kernel::program_loop_continuation(update.map(|update| update.as_ref()), test);
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: Arc::new(crate::kernel::program_loop_preservation_pass(
                body,
                update.map(|update| update.as_ref()),
                test.expect("loop preservation owns its test"),
            )),
        },
        region: ExecutionRegionKind::LoopBody,
        in_loop_body: true,
        loop_phase_source: test.map(|test| crate::kernel::proof::LoopPhaseSource {
            header_index: loop_body_statement_index - 1,
            test_position: test.position,
        }),
        loop_update: continuation.as_ref().and_then(|update| {
            source_layout
                .loop_continuation_entry(loop_index)
                .map(|index| (update.clone(), index))
        }),
        natural_backedge_target: source_layout.natural_loop_target(loop_index),
        natural_exit_target: source_layout.natural_exit_target(loop_index),
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    // Inner marks remain local to this proof's persistent-map version.
    let mut recorded_states = enclosing_states.clone();
    let nested_tactic_capture = expansion_capture
        .as_deref()
        .and_then(|capture| capture.nested_for_site(preserve_site));
    let mut constants = ExecutionProofConstants {
        nested_tactic_capture,
        proof_site: preserve_site.cloned(),
        invariant_body_context: Some(Arc::new(InvariantBodyContext {
            loop_index,
            loop_entry_state: preservation.loop_entry_state().clone(),
            loop_entry_selector: Some(ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Loop(loop_index),
                kind: ProgramPointKind::Entry,
            })),
            iteration_entry_state: preservation.state().clone(),
            iteration_entry_selector: Some(ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(loop_body_statement_index),
                kind: ProgramPointKind::Entry,
            })),
            iterations: Some(preservation.iterations().clone()),
            checks: invariant_checks.to_vec(),
            entry_guard: condition.cloned().map(Arc::new),
            ranking_measures: ranking_measures.to_vec(),
            ranking_surfaces: loop_ranking_surfaces(environment, loop_index),
            structural_measure: structural_measure.map(str::to_string),
            // Generated back-edge proofs use the invariant's written
            // bindings from the loop's lexical scope.
            declared_invariant_surfaces: environment
                .function_block
                .structural_clauses()
                .for_loop(loop_index)
                .into_iter()
                .flat_map(StructuralClause::items)
                .map(|item| item.proposition().clone())
                .collect(),
            loop_head_premises: Vec::new(),
            binders: preservation.binders().to_vec(),
            binder_names: Arc::new({
                // The head's pass count is spelled `iterations`.
                let mut names = written_invariant_binder_names(invariant_checks);
                if let crate::kernel::IntegerTerm::Variable(count) = preservation.iterations() {
                    names.insert(
                        *count,
                        SurfaceBinder::from(crate::surface::LOOP_ITERATIONS_NAME),
                    );
                }
                names
            }),
        })),
        source_layout,
        function_entry_state: Some(environment.initial_state.clone()),
        function_source_registry: environment.function_source_registry.clone(),
        parameter_index: environment.parent_constants.parameter_index.clone(),
        parameter_naming: environment.parent_constants.parameter_naming.clone(),
        ..ExecutionProofConstants::default()
    };
    let mut surface_propositions = environment.surface_propositions.clone();
    record_statement_program_state(
        &mut recorded_states,
        environment.function_block,
        loop_body_statement_index,
        ProgramPointKind::Entry,
        preservation.state().clone(),
    );
    record_code_region_program_state(
        &mut recorded_states,
        environment.function_block,
        CodeRegion::Loop(loop_index),
        ProgramPointKind::Entry,
        preservation.loop_entry_state().clone(),
    );
    // The invariants are available at the body entry as kernel facts. A
    // pre-tested loop also has its condition there; a do-while does not, so
    // it must not be recorded as an available premise for the first body.
    let loop_condition = condition
        .map(|condition| {
            surface_program_condition(condition, preservation.state(), Some(&recorded_states))
        })
        .transpose()?;
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
    if let Some(loop_condition) = loop_condition
        && let Ok(lowered) = lower_fixed_state_proposition(
            &loop_condition,
            pure_facts,
            environment.parameter_binding(),
            FixedStateFrame::new(
                environment.initial_state,
                preservation.state(),
                None,
                &recorded_states,
            ),
            environment.spec_definitions,
        )
    {
        let surface = surface_at_program_point(
            &loop_condition,
            &ProgramPointRef {
                region: CodeRegionRef::Region(loop_body_statement_index),
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
        .preserve_source_index
        .is_none()
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
    let mut body_execution = ExecutionProofState::at_entry_with_descent(
        preservation.state().clone(),
        frontier,
        recorded_states,
        surface_propositions,
        PersistentSequence::default(),
        environment.function,
        environment.function_environment,
    )?;
    body_execution
        .core
        .advance_kernel_variable_mark(preservation.next_kernel_variable())
        .map_err(|message| ClickError::new(format!("`{claim_label}`.maintain: {message}")))?;
    let root = Proof::for_execution_frontier(
        &claim_label,
        internal_proof_first_index(&program).unwrap_or(0),
        body_execution,
        pure_facts.clone(),
        constants.clone(),
        environment.function_block,
        environment.function,
        environment.parsed_function,
        environment.arguments,
        environment.function_environment,
        environment.resource_environment,
        environment.spec_definitions,
        environment.theorem_environment,
    )
    .with_surface_local_scope(&phase_proof_scope(environment))
    .with_loop_iterations(preservation.iterations());
    if let Some(parent_lineage) = crate::surface::proof_trace::loop_parent_lineage() {
        root.register_trace_scope_under(parent_lineage);
    }
    let mut leaves = Vec::new();
    let mut refuted_case_paths = Vec::new();
    let mut unfinished = Vec::new();
    with_preservation_continuation_record(|| {
        advance_preservation_region(
            root,
            &program,
            &[],
            expansion_capture.as_deref_mut(),
            proof_site_for_driver.as_ref(),
            owning_source_index,
            &claim_label,
            &mut leaves,
            &mut refuted_case_paths,
            &mut unfinished,
            None,
        )
    })?;
    let invariant_surfaces = loop_invariant_surfaces(environment, loop_index, &claim_label)?;
    let invariant_premise_surfaces = invariant_surfaces
        .iter()
        .map(|surface| {
            surface_at_program_point(
                surface,
                &ProgramPointRef {
                    region: CodeRegionRef::Region(loop_body_statement_index),
                    kind: ProgramPointKind::Entry,
                },
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut certificate_paths = Vec::new();
    let mut final_exit_candidates = Vec::new();
    let mut early_exits = Vec::new();
    // The points each leaving path recorded during its pass, from the start
    // of the pass on: after the loop they name that pass's points.
    let pass_start = enclosing_states.history_mark();
    let mut exit_points = Vec::new();
    let mut return_exits = Vec::new();
    let mut return_proofs = Vec::new();
    let mut seen_nested_returns = std::collections::HashSet::new();
    // Each exit is recorded once. The lists are compared by a hash of the
    // exit's state and facts first, so a new exit is checked for equality only against
    // exits in its own bucket rather than against every exit recorded so far.
    let mut seen_final_exits = SeenLoopExits::default();
    let mut seen_early_exits = SeenLoopExits::default();
    let mut back_edge_states = Vec::new();

    let mut nested_loop_rules = Vec::new();
    for (execution, path_certificate) in refuted_case_paths {
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
    if crate::surface::proof_trace::enabled_for(&claim_label) {
        for (path_index, path) in unfinished.iter().enumerate() {
            path.proof.record_unfinished_trace(&claim_label, path_index);
        }
    }
    let deferred_frontier = unfinished
        .first()
        .map(|path| path.report(&claim_label, &leaves));
    for (leaf_index, leaf) in leaves.into_iter().enumerate() {
        leaf.record_nested_accepted_trace(&claim_label, leaf_index);
        let context_execution = leaf.execution_view()?.execution.clone();
        for rule in context_execution.core.frontier_loop_rules.iter() {
            if !nested_loop_rules
                .iter()
                .any(|existing: &VerifiedLoopRule| existing == rule)
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
        let region_solve = context_execution.presentation.region_solve;
        let proof_site = leaf.execution_view()?.context.constants.proof_site.clone();
        let invariants_close_requested = context_execution.core.region_invariants_close_requested;
        // A path that left through `break` is an exit, not a back edge: it
        // owes no invariant and no measure, and the loop rule joins it with
        // the loop's other exits instead of returning it to the head.
        let is_early_exit = context_frontier.loop_control.is_exit();
        // A path that reached the function exit left through `return`. It is
        // a function-exit path of the enclosing execution in every loop form,
        // and owes neither an invariant nor a measure.
        let is_return_exit = context_frontier.is_at_function_exit();
        let jump_target = match context_frontier.loop_control {
            crate::kernel::proof::LoopControlExit::Jump(target) => Some(target),
            _ => None,
        };
        let is_terminal_return_exit = is_return_exit || jump_target.is_some();
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
            } else if let Some((tactic_index, source_index)) = region_solve {
                (tactic_index, source_index, "solve", "smart")
            } else {
                // The implicit bundle closer plans a default `solve` body.
                // Its premise selection is smart work even when the first
                // checked member happens to close by `close()`.
                let (at, name) = match source.preserve_source_index {
                    Some(at) => (at, crate::instrumentation::IMPLICIT_LOOP_CLOSER_TACTIC),
                    None => (
                        source.loop_source_index,
                        crate::instrumentation::IMPLICIT_SOLVE_TACTIC,
                    ),
                };
                (tactics.len(), at, name, "smart")
            };
        let _timing = crate::instrumentation::enabled().then(|| {
            if crate::instrumentation::starts_enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(
                        crate::instrumentation::TacticEvent {
                            source_tactic_path: None,
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
                source_tactic_path: None,
                claim_label: claim_label.clone(),
                tactic_index: closer_index,
                source_index: closer_source,
                tactic_name: closer_name.to_string(),
                tactic_class: closer_class.to_string(),
                statement_index,
            };
            push_timing_tactic(timing_context.clone());
            TacticTiming {
                source_tactic_path: None,
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
        // A region-level `solve` is a Surface planner. Establish each named
        // invariant through the checked proposition Proof before asking the
        // kernel to close the bundle. In particular, upper-bound extension
        // now becomes a nested proof `if` here instead of recursive search in
        // proposition reasoning.
        let mut leaf = leaf;
        if is_terminal_return_exit || is_early_exit {
            // Nothing is closed on an exit path, so nothing is planned here.
        } else if !has_retained_invariant_body && region_solve.is_some() {
            if invariant_surfaces.len() != invariant_checks.len() {
                return Err(leaf.step_error(
                    "surface invariants do not align with the lowered invariant bundle",
                ));
            }
            for (index, invariant) in invariant_surfaces.iter().enumerate() {
                let scope = leaf.driver().open_have(invariant.clone())?;
                let Some(proved) = (scope)
                    .driver()
                    .try_solve_closure_with_surfaces(&invariant_premise_surfaces[..=index])?
                else {
                    continue;
                };
                leaf = proved.join()?;
            }
        }
        let (checked, boundary) = if is_terminal_return_exit || is_early_exit {
            (leaf.clone(), None)
        } else if invariant_checks.is_empty()
            && ranking_measures.is_empty()
            && structural_measure.is_none()
        {
            let boundary = leaf
                .check_loop_boundary(
                    preservation.loop_entry_state(),
                    preservation.state(),
                    preservation.iterations(),
                    condition,
                    &[],
                    preservation.binders(),
                    structural_measure,
                    environment.function.composite_resource_definitions(),
                    false,
                )
                .map_err(|error| {
                    error.with_context(format!("`{claim_label}` (loop {loop_index} state join)"))
                })?;
            (leaf.clone(), Some(boundary))
        } else {
            leaf.driver()
                .prepare_loop_invariant_bundle(
                    preservation.loop_entry_state(),
                    preservation.state(),
                    preservation.iterations(),
                    condition,
                    invariant_checks,
                    ranking_measures,
                    structural_measure,
                    &invariant_surfaces,
                    preservation.binders(),
                    environment.function.composite_resource_definitions(),
                )
                .and_then(|(proof, boundary)| {
                    proof
                        .certify_loop_invariant_bundle(
                            invariant_checks,
                            boundary.required_ranking_measures(ranking_measures),
                        )
                        .map(|proof| (proof, Some(boundary)))
                })
                .map_err(|error| {
                    let error = error.with_context(format!(
                        "`{claim_label}` (loop {loop_index} invariant bundle preservation)"
                    ));
                    // A closer the `loop` tactic generated is no written tactic;
                    // the `loop` tactic is where the user reads its failure.
                    error.attributed_to_source_tactic(
                        environment.frontier_loop_source.loop_source_index,
                    )
                })?
        };
        // An iteration that returns to the head is on no exit's path: the
        // loop rule reads its writes from this state.
        if let Some(state) = boundary.as_ref().and_then(LoopBoundary::back_edge_state) {
            back_edge_states.push(state.clone());
        }
        let checked_execution = checked.execution_view()?.execution.clone();
        // An inner loop may return while this iteration continues. Export
        // those checked terminal paths through the outer rule as well.
        for pending in checked_execution.core.pending_loop_returns() {
            let Some(nested) = pending
                .loop_index
                .and_then(|index| {
                    checked_execution
                        .presentation
                        .loop_return_proofs
                        .get(&index)
                })
                .and_then(|proofs| proofs.paths.get(pending.return_index))
            else {
                return Err(ClickError::new("nested loop return lost its surface owner"));
            };
            if !seen_nested_returns.insert(Arc::as_ptr(nested) as usize) {
                continue;
            }
            let FunctionOutcome::Return { value, state } = &pending.outcome else {
                return Err(ClickError::new("nested loop return has no returned value"));
            };
            return_exits.push(
                LoopReturnExit::from_store(value.clone(), (**state).clone(), &pending.pure_facts)
                    .with_borrow_evidence(pending.borrow_evidence.clone()),
            );
            let mut nested = (**nested).clone();
            nested.owners.push((
                loop_index,
                environment.frontier_loop_source.loop_source_index,
            ));
            return_proofs.push(Arc::new(nested));
        }
        if is_return_exit {
            // The path left the function here. The loop rule exports it as a
            // `Return` outcome of the loop statement, so the enclosing
            // execution certifies the postcondition and the resource
            // obligations on the returned value and the state at the
            // `return`. It is neither a back edge nor a candidate for the
            // loop guard's next evaluation: offered as a candidate, a guard
            // the C never falsifies (a natural cycle's `while (1)`) swallowed
            // it, and dropped outright it never reached certification.
            let (value, state) = checked_execution
                .core
                .completed_return_outcome()
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` (loop {loop_index} preservation): a path that reached the function exit retained no returned outcome"
                    ))
                })?;
            let (state, exit_facts) = preservation.restored_return(
                &state,
                checked.facts(),
                &assumptions_from_propositions(checked.facts()),
            );
            let exit = LoopReturnExit::from_store(value, state, &exit_facts)
                .with_borrow_evidence(checked_execution.core.borrow_evidence().clone());
            // Equal semantic exits may carry different written proofs. Keep
            // each arm so no source proof disappears through deduplication.
            return_exits.push(exit);
            if let Some(nested) = context_execution.loop_return_proof(0) {
                let mut nested = (**nested).clone();
                nested.owners.push((
                    loop_index,
                    environment.frontier_loop_source.loop_source_index,
                ));
                return_proofs.push(Arc::new(nested));
            } else {
                let mut tactics = context_execution
                    .presentation
                    .post_execution_tactics
                    .clone();
                if tactics.is_empty() {
                    tactics.push(DeferredPostExecutionTactic {
                        lexical_bindings: None,
                        reads_deferred_binding: false,
                        tactic_index: environment.frontier_loop_source.loop_tactic_index,
                        source_index: environment.frontier_loop_source.loop_source_index,
                        tactic: PostExecutionTactic::Solve,
                    });
                }
                return_proofs.push(Arc::new(LoopReturnProof {
                    loop_index,
                    owners: {
                        let mut owners = PersistentSequence::default();
                        owners.push((
                            loop_index,
                            environment.frontier_loop_source.loop_source_index,
                        ));
                        owners
                    },
                    case_path: case_path.clone(),
                    tactics,
                    batch_captures: context_execution
                        .presentation
                        .expansion
                        .batch_deferred_captures
                        .clone(),
                    capture: context_execution
                        .presentation
                        .expansion
                        .deferred_tactic_capture
                        .clone(),
                }));
            }
        } else if let Some(target) = jump_target {
            // The jump leaves for its named label without owing the loop
            // invariant or ranking bundle.
            let (state, exit_facts) = preservation.restored_exit(
                &checked_execution.core.state,
                checked.facts(),
                &assumptions_from_propositions(checked.facts()),
            );
            let exit = LoopFinalExitCandidate::from_store(state, &exit_facts)
                .with_jump_target(target)
                .with_borrow_evidence(checked_execution.core.borrow_evidence().clone());
            if seen_final_exits.is_new(
                exit.state(),
                exit.pure_facts(),
                &final_exit_candidates,
                &exit,
            ) {
                final_exit_candidates.push(exit);
            }
        } else if is_early_exit {
            let points = context_execution
                .presentation
                .recorded_states
                .recorded_since(&pass_start);
            let guard_false = matches!(
                context_frontier.loop_control,
                crate::kernel::proof::LoopControlExit::TestFalse
            );
            let points_index = if guard_false {
                guard_points.as_deref_mut().map(|records| {
                    let index = records.len();
                    records.push(points.clone());
                    index
                })
            } else {
                None
            };
            exit_points.push(points);
            // The exit is this path's own state and the facts it retained
            // there. The loop rule joins it with every other exit into the
            // single successor, so nothing about this path is dropped and
            // nothing about it is assumed to satisfy the invariants.
            let state = preservation.restored_exit_state(
                &checked_execution.core.state,
                &assumptions_from_propositions(checked.facts()),
            );
            let exit = LoopEarlyExit::from_store(state, checked.facts())
                .with_guard_false(guard_false)
                .with_guard_points_index(points_index)
                .with_borrow_evidence(checked_execution.core.borrow_evidence().clone());
            if seen_early_exits.is_new(exit.state(), exit.pure_facts(), &early_exits, &exit) {
                early_exits.push(exit);
            }
        } else if let Some(exit_state) = boundary
            .as_ref()
            .and_then(LoopBoundary::explicit_exit_state)
        {
            // This classified false-guard exit needs its own state; a
            // head-compatible exit already has the invariant-head summary.
            // A feasible continuing edge with different ownership was refused
            // by the producer rather than reinterpreted as an exit.
            let join_assumptions = checked.back_edge_assumptions(&checked_execution);
            let (state, exit_facts) =
                preservation.restored_exit(exit_state, checked.facts(), &join_assumptions);
            let points_index = guard_points.as_deref_mut().map(|records| {
                let index = records.len();
                records.push(
                    context_execution
                        .presentation
                        .recorded_states
                        .recorded_since(&pass_start),
                );
                index
            });
            let candidate = LoopFinalExitCandidate::from_store(state, &exit_facts)
                .with_guard_points_index(points_index)
                .with_borrow_evidence(checked_execution.core.borrow_evidence().clone());
            if seen_final_exits.is_new(
                candidate.state(),
                candidate.pure_facts(),
                &final_exit_candidates,
                &candidate,
            ) {
                final_exit_candidates.push(candidate);
            }
        }
        let closer_tactics = if is_terminal_return_exit
            || is_early_exit
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
        if closer_name == crate::instrumentation::IMPLICIT_LOOP_CLOSER_TACTIC
            && !closer_tactics.is_empty()
            && crate::instrumentation::enabled()
        {
            crate::instrumentation::emit(
                crate::instrumentation::VerificationEvent::LoopCloserProof,
            );
        }
        let omitted_frontier_preservation = environment
            .frontier_loop_source
            .preserve_source_index
            .is_none();
        if !omitted_frontier_preservation
            && region_solve.is_some_and(|(_, source_index)| {
                // Region solve is deferred by the preservation driver, so it
                // never opens an active tactic capture. Match its selected
                // source occurrence just as the driver's explicit steps do.
                proof_site.as_ref().is_some_and(|site| {
                    capture_selects_source(expansion_capture.as_deref(), site, source_index)
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
            // legitimately empty closer: the selected `solve` contributes no
            // surface tactics and its exact expansion removes it.
            if let Some(selected) = region_solve.map(|(_, source)| source)
                && let Some(outer) = expansion_capture.as_deref_mut()
                && let Some(batch) = &mut outer.batch
            {
                batch.active_source = Some(selected);
            }
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
                "`{claim_label}` produced an invalid preservation leaf certificate: {error}"
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
    if capture_shared_closer {
        let capture = expansion_capture.expect("selected shared closer");
        let selected = preserve_source_index + source_tactic_count(&tactics[..tactics.len() - 1]);
        if capture.batch.is_some() {
            let target = capture
                .target_mut(selected)
                .expect("selected shared closer");
            target.active = true;
            target.result = Some(Ok(certificate.to_proof_tactics()));
            target.replaces_from = Some(preserve_source_index);
        } else {
            capture.active = true;
            capture.result = Some(Ok(certificate.to_proof_tactics()));
            crate::surface::expansion::note_expansion_replaces_from(preserve_source_index);
        }
    }
    Ok(LoopPreservationProofResult {
        return_proofs,
        certificate,
        final_exit_candidates,
        early_exits,
        return_exits,
        nested_loop_rules,
        exit_points,
        back_edges: preservation.back_edges(back_edge_states),
    })
}

/// The exits already recorded in one list, by the hash of each exit's state
/// and facts.
///
/// `Vec::contains` compared a new exit with every earlier one, and two exits
/// of one loop body usually agree on most of their state, so each comparison
/// read most of a state before finding the difference. The answer here is the
/// same: an exit is new exactly when no recorded exit equals it. Only the
/// candidates for that equality are narrowed.
#[derive(Default)]
struct SeenLoopExits {
    by_hash: std::collections::HashMap<u64, Vec<usize>>,
}

impl SeenLoopExits {
    /// Whether `exit` equals none of `recorded`, and files it at the position
    /// the caller is about to push it to when it is new.
    fn is_new<T: PartialEq>(
        &mut self,
        state: &ExecutionState,
        facts: &crate::kernel::LoopExitFacts,
        recorded: &[T],
        exit: &T,
    ) -> bool {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        state.hash(&mut hasher);
        for fact in facts.iter() {
            fact.hash(&mut hasher);
            crate::instrumentation::record_deterministic_work(1);
        }
        crate::instrumentation::record_deterministic_work(1);
        let bucket = self.by_hash.entry(hasher.finish()).or_default();
        if bucket.iter().any(|index| {
            crate::instrumentation::record_deterministic_work(1);
            &recorded[*index] == exit
        }) {
            return false;
        }
        bucket.push(recorded.len());
        true
    }
}
