use super::*;
use crate::kernel::LoweringIntroduction;
use std::sync::Arc;

/// The proof scope a loop's phase proofs are written in.
///
/// `initialize` and `preserve` bodies are written where the `loop` tactic
/// was written: inside whatever proof `match` arm, `unfold ... as` binding,
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

/// The goal one loop-entry invariant certificate must discharge.
///
/// The entry obligation lowering hands back may be wrapped in leading
/// implications: path guards and lowering-inserted loadability or definedness
/// guards. An antecedent that is exactly one of the available facts is already
/// discharged, so it is stripped. Every other antecedent stays in the goal and
/// the certificate must introduce it explicitly.
///
/// Planning and independent validation both derive their goal here, so a
/// retained certificate is always checked against the goal it was built for.
/// Deciding "already known" with a prover on one side and exact containment on
/// the other is what this function replaces.
pub(in crate::surface::proof) fn loop_entry_checked_goal(
    obligation: &Proposition,
    available: &[Proposition],
) -> Proposition {
    loop_entry_checked_goal_with_stripped(obligation, available).0
}

/// [`loop_entry_checked_goal`], also reporting how many head nodes it
/// stripped. The lowering record for the obligation describes those same
/// nodes from the outside in, so dropping that many entries leaves the
/// record that describes the checked goal.
pub(in crate::surface::proof) fn loop_entry_checked_goal_with_stripped(
    obligation: &Proposition,
    available: &[Proposition],
) -> (Proposition, usize) {
    let facts = crate::kernel::proof::ProofFacts::from_ordered(available);
    let mut goal = obligation.clone();
    let mut stripped = 0;
    while let Proposition::Implies(antecedent, body) = &goal {
        if !facts.contains(antecedent) {
            break;
        }
        let body = body.as_ref().clone();
        goal = body;
        stripped += 1;
    }
    (goal, stripped)
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

/// Whether the facts an initialization proof established discharge one entry
/// obligation.
///
/// The certificate proves [`loop_entry_checked_goal`], so that goal is the
/// first thing to look for. An obligation that lowering wrapped in leading
/// implications is also discharged by any body of that chain: `guard implies
/// body` follows from `body` alone. Both steps are exact lookups over this
/// obligation's own head chain, never a proof search over the fact set.
fn loop_entry_obligation_is_discharged(
    obligation: &Proposition,
    available: &[Proposition],
) -> bool {
    let facts = crate::kernel::proof::ProofFacts::from_ordered(available);
    let mut goal = loop_entry_checked_goal(obligation, available);
    loop {
        if facts.contains(&goal) {
            return true;
        }
        let Proposition::Implies(_, body) = goal else {
            return false;
        };
        goal = body.as_ref().clone();
    }
}

/// The kernel form the surface invariant itself denotes inside a checked
/// goal that still carries leading guards, read from the lowering record.
///
/// Lowering wraps an entry obligation in implications that have no Surface
/// connective: path guards and loadability or definedness premises. The
/// certificate introduces those with `intro`, which keeps the written
/// Surface goal focused, and the surface proposition map records the same
/// pairing. Only the recorded chain says which leading implications are
/// those guards, so this walks the record, not the constructor shape: it
/// stops at the first node the spec wrote.
///
/// `None` means the pairing is not exact here — the record ran out before
/// the guards did, or an already-discharged written connective was stripped
/// from the goal — and nothing is recorded rather than pairing by shape.
fn invariant_lowering_under_recorded_guards<'a>(
    goal: &'a Proposition,
    introductions: Option<&[LoweringIntroduction]>,
) -> Option<&'a Proposition> {
    let mut introductions = introductions?.iter();
    let mut goal = goal;
    loop {
        match introductions.next() {
            Some(LoweringIntroduction::PathFactGuard | LoweringIntroduction::ObligationGuard) => {
                let Proposition::Implies(_, body) = goal else {
                    // The record and the proposition disagree; refuse the
                    // pairing instead of guessing which is right.
                    return None;
                };
                goal = body;
            }
            // A written node, or the end of the record, is where the
            // written invariant itself starts.
            _ => return Some(goal),
        }
    }
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
    /// individually, and the fallback when an invariant's own body does not
    /// close the entry goal on its own.
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

/// The expansion of a selected whole-phase `initialize` closer.
///
/// A smart tactic that stands for the rest of the phase expands to the
/// invariant steps the planner built. The helper steps the script already
/// spells stay written where they are, so they are dropped from the
/// replacement; an `initialize` that names every invariant already proves
/// them, so its trailing `simp()` expands to nothing at all.
pub(in crate::surface::proof) fn initialize_phase_closer_expansion(
    proof: &SourceProof,
    clause: &StructuralClause,
    phase_start: usize,
    selected: usize,
    certificate: &ProofCertificate,
) -> Option<Vec<ProofTactic>> {
    let tactics = certificate.to_proof_tactics();
    if matches!(proof, SourceProof::Tactic(SmartTactic::Simp)) {
        return (selected == phase_start).then(|| tactics.to_vec());
    }
    let invariant_items = clause.items().iter().collect::<Vec<_>>();
    let layout = initialize_script_layout(proof, &invariant_items, phase_start);
    // A script that names no invariant and hoists no helper is one shared
    // proof of every invariant: its leading smart step stands for the whole
    // phase just as a trailing `simp()` does.
    let leading_whole_phase_site = layout.is_whole_proof() && selected == phase_start;
    if !leading_whole_phase_site && !layout.closers.contains(&selected) {
        return None;
    }
    if layout.invariant_bodies.is_some() {
        return Some(Vec::new());
    }
    Some(
        tactics
            .get(layout.helpers.len()..)
            .unwrap_or_default()
            .to_vec(),
    )
}

pub(in crate::surface::proof) fn verify_loop_initialization_pure_proof(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    loop_index: usize,
    proof: &SourceProof,
    clause: &StructuralClause,
    context: &PlanningExecutionContext,
    invariant_checks: &[CLoopInvariantCheck],
    environment: &ExecutionProofEnvironment<'_>,
) -> Result<ProofCertificate, ClickError> {
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
    let initialization_surface_propositions =
        std::cell::RefCell::new(context.surface_propositions.clone());
    // Generated initialization steps belong to the explicit phase tactic when
    // one exists, or to the enclosing `loop` keyword for an omitted phase.
    // Computing the source statement is only worth it when timings are read.
    let timings_enabled = crate::instrumentation::enabled();
    let initialize_statement_index = if timings_enabled {
        SourceExecutionLayout::new(environment.parsed_function.body())
            .loop_body_entry(loop_index)
            .unwrap_or(0)
    } else {
        0
    };
    let entry_obligations = c_loop_invariant_obligations_at_entry(
        &context.state,
        invariant_checks,
        &assumptions_from_propositions(&context.pure_facts),
    )
    .map_err(|message| {
        ClickError::new(match fresh_loop_binder_name(environment.function_block, clause) {
            Some(name) => format!(
                "`{claim_label}`: loop binder `{name}` is not an enclosing contract binder, so an \
                 invariant that reads it has nothing to read at loop entry; reuse the enclosing \
                 binder's name, whose instance the loop takes over"
            ),
            None => format!("`{claim_label}`: {message}"),
        })
    })?;
    // Expansion lowers a shared initialize proof to optional predicate
    // unfolds followed by one explicit `have` per invariant.  Recognize that
    // surface-certificate shape on the next verification pass and check it
    // directly.  Sending it back through the per-invariant planner would
    // treat the whole certificate as the proof of every individual `have`,
    // recursively duplicate it, and can make a valid first expansion fail.
    let source_certificate = proof.tactics().and_then(|tactics| {
        let invariant_start = tactics.len().checked_sub(invariant_items.len())?;
        // A helper `have` written before the invariants is part of that same
        // expanded shape: the planner keeps it where it was written rather
        // than copying it into every invariant's proof.
        let prefix_is_explicit = tactics[..invariant_start].iter().all(|tactic| {
            matches!(
                tactic,
                ProofTactic::UnfoldPredicate(_) | ProofTactic::Have(_)
            )
        });
        let invariants_match =
            tactics[invariant_start..]
                .iter()
                .zip(&invariant_items)
                .all(|(tactic, item)| {
                    matches!(
                        tactic,
                        ProofTactic::Have(have)
                            if item.proposition() == &have.proposition
                    )
                });
        (prefix_is_explicit && invariants_match)
            .then(|| ProofCertificate::from_proof_tactics(tactics).ok())
            .flatten()
            .filter(|certificate| !certificate.contains_arithmetic_using())
    });
    let source_contains_legacy_arithmetic = source_certificate.is_none()
        && proof
            .tactics()
            .and_then(|tactics| ProofCertificate::from_proof_tactics(tactics).ok())
            .is_some_and(|certificate| certificate.contains_arithmetic_using());
    let layout = initialize_script_layout(proof, &invariant_items, initialize_source_index);
    let selected_source_index =
        selected_tactic_index_for_site(expansion_capture.as_deref(), &initialize_site);
    let (certificate, available) = pure_goal_proof_certificate_gateway_with_checked_result(
        &claim_label,
        || {
            if let Some(certificate) = source_certificate {
                return Ok((certificate, None));
            }
            let mut planning_available = context.pure_facts.clone();
            let mut tactics = Vec::new();
            let mut all_invariants_checked = true;
            // A helper step belongs to the phase, not to one invariant: plan
            // it once, where it was written, and let its fact reach every
            // invariant proof below through `planning_available`.
            for (helper_source_index, helper) in &layout.helpers {
                match helper {
                    ProofTactic::UnfoldPredicate(name) => {
                        planning_available = unfold_available_predicate_facts(
                            environment.predicate_environment,
                            environment.click_function_environment,
                            std::slice::from_ref(name),
                            &planning_available,
                        )
                        .map_err(|message| {
                            ClickError::new(format!("`{claim_label}` initialize prefix: {message}"))
                        })?;
                        tactics.push((*helper).clone());
                    }
                    ProofTactic::Have(have) => {
                        let resolved = crate::surface::lowering::substitute_click_proposition(
                            &have.proposition,
                            &environment.proof_locals,
                        )
                        .map_err(|message| {
                            ClickError::new(format!("`{claim_label}` initialize prefix: {message}"))
                        })?;
                        let helper_claim_label =
                            format!("{claim_label} (loop {loop_index} entry prerequisite)");
                        let planned = plan_fixed_state_pure_goal_certificate(
                            None,
                            &initialize_site,
                            &resolved,
                            &have.proof,
                            &helper_claim_label,
                            tactics.len(),
                            &planning_available,
                            environment.parsed_function.parameters(),
                            environment.arguments,
                            environment.initial_state,
                            &context.state,
                            &recorded_snapshots,
                            environment.predicate_environment,
                            environment.click_function_environment,
                            &context.surface_propositions,
                            None,
                            None,
                            None,
                            environment.theorem_environment,
                            &phase_proof_scope(environment),
                        )?;
                        all_invariants_checked &= planned.certificate_already_checked;
                        if let Some(lowered) = invariant_lowering_under_recorded_guards(
                            &planned.fact,
                            planned.introductions.as_deref(),
                        ) {
                            initialization_surface_propositions
                                .borrow_mut()
                                .record_lowering(&have.proposition, lowered)?;
                        }
                        let step = ProofTactic::Have(ProofHave {
                            proposition: have.proposition.clone(),
                            proof: SourceProof::Script(
                                planned.certificate.to_proof_tactics().to_vec(),
                            ),
                        });
                        if selected_source_index == Some(*helper_source_index) {
                            record_proof_site_tactic_expansion(
                                expansion_capture.as_deref_mut(),
                                &initialize_site,
                                *helper_source_index,
                                std::slice::from_ref(&step),
                            );
                        }
                        tactics.push(step);
                        if !planning_available.contains(&planned.fact) {
                            planning_available.push(planned.fact);
                        }
                    }
                    _ => unreachable!("only `unfold` and `have` steps are hoisted"),
                }
            }
            for (invariant_index, item) in invariant_items.iter().enumerate() {
                let written = item.proposition();
                // Lower the invariant with the frontier's proof locals
                // resolved; the written spelling is what the source proof's
                // `have`s are matched against.
                let resolved = crate::surface::lowering::substitute_click_proposition(
                    written,
                    &environment.proof_locals,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` loop {loop_index} invariant {invariant_index}: {message}"
                    ))
                })?;
                let proposition = &resolved;
                // A phase source certificate normally contains one `have`
                // per invariant and can be checked as a whole.  If one of
                // those bodies still contains the source-only arithmetic
                // request, plan that invariant from its own body instead;
                // passing the entire phase to each per-invariant planner
                // would duplicate every sibling `have`.
                let own_body = (!source_contains_legacy_arithmetic)
                    .then_some(layout.invariant_bodies.as_ref())
                    .flatten()
                    .and_then(|bodies| bodies.get(invariant_index))
                    .copied();
                let invariant_proof = if source_contains_legacy_arithmetic {
                    proof
                        .tactics()
                        .and_then(|tactics| {
                            tactics.iter().find_map(|tactic| match tactic {
                                ProofTactic::Have(have) if have.proposition == *written => {
                                    Some(&have.proof)
                                }
                                _ => None,
                            })
                        })
                        .unwrap_or(proof)
                } else {
                    own_body.map_or(&layout.shared, |(_, body)| body)
                };
                let invariant_claim_label =
                    format!("{claim_label} (loop {loop_index} invariant {invariant_index} entry)");
                let obligation_context =
                    format!("loop {loop_index} invariant {invariant_index} entry");
                let exact_expected_obligation = entry_obligations
                    .iter()
                    .find(|obligation| obligation.context() == Some(&obligation_context));
                let exact_expected_goal =
                    exact_expected_obligation.map(|obligation| obligation.proposition().clone());
                // Stripping already-available antecedents consumes head
                // nodes, so the record for the checked goal starts that
                // many entries in. The kernel recorded the chain while it
                // built this obligation; nothing is re-derived here.
                let checked = exact_expected_goal.as_ref().map(|obligation| {
                    loop_entry_checked_goal_with_stripped(obligation, &planning_available)
                });
                let checked_goal = checked.as_ref().map(|(goal, _)| goal.clone());
                let checked_goal_introductions = checked.as_ref().and_then(|(_, stripped)| {
                    let recorded = exact_expected_obligation?.introductions()?;
                    Some(recorded.get(*stripped..).unwrap_or_default().to_vec())
                });
                // Planning an invariant's entry proof is proof search, not
                // check. Classify it by the `by` clause the search is
                // discharging, exactly as if it were written as a `have`.
                let planned_step = timings_enabled.then(|| {
                    ProofTactic::Have(ProofHave {
                        proposition: written.clone(),
                        proof: invariant_proof.clone(),
                    })
                });
                let _timing = planned_step.as_ref().and_then(|planned_step| {
                    TacticTiming::named_for_tactic(
                        &claim_label,
                        "plan_invariant_entry",
                        planned_step,
                        invariant_index,
                        initialize_source_index,
                        initialize_statement_index,
                    )
                });
                let plan = |expansion_capture: Option<&mut ExpansionCapture>,
                            invariant_proof: &SourceProof| {
                    plan_fixed_state_pure_goal_certificate(
                        expansion_capture,
                        &initialize_site,
                        proposition,
                        invariant_proof,
                        &invariant_claim_label,
                        invariant_index,
                        &planning_available,
                        environment.parsed_function.parameters(),
                        environment.arguments,
                        environment.initial_state,
                        &context.state,
                        &recorded_snapshots,
                        environment.predicate_environment,
                        environment.click_function_environment,
                        &context.surface_propositions,
                        checked_goal.as_ref(),
                        checked_goal.as_ref(),
                        checked_goal_introductions.as_ref(),
                        environment.theorem_environment,
                        &phase_proof_scope(environment),
                    )
                };
                // Nested frontier-loop phase tactics use absolute source
                // indices in the enclosing proof, and a split phase script
                // renumbers what the per-invariant planner sees. The pure
                // planner sees only the proof it is handed, so route no
                // expansion capture into it in either case; the recorder
                // below and the phase merger keep the expansion at the
                // absolute source site.
                let route_capture =
                    environment.frontier_loop_source.is_none() && layout.is_whole_proof();
                let mut planned_own_body_index = own_body.map(|(index, _)| index);
                let routed_capture = if route_capture {
                    expansion_capture.as_deref_mut()
                } else {
                    None
                };
                let direct_plan = match plan(routed_capture, invariant_proof) {
                    Ok(plan) => plan,
                    // An invariant's own `have` body proves the invariant as
                    // written; the entry goal it is checked against can have
                    // been reshaped by the guards lowering introduced. Where
                    // the body alone does not reach that goal, the phase
                    // script as a whole still does, and did before the split.
                    Err(error) if own_body.is_some() => {
                        planned_own_body_index = None;
                        plan(None, &layout.shared).map_err(|_| error)?
                    }
                    Err(error) => return Err(error),
                };
                let PlannedPointPureGoal {
                    fact: planned_fact,
                    certificate: planned_certificate,
                    certificate_already_checked,
                    introductions: planned_introductions,
                } = direct_plan;
                all_invariants_checked &= certificate_already_checked;
                if let Some(lowered) = invariant_lowering_under_recorded_guards(
                    &planned_fact,
                    planned_introductions.as_deref(),
                ) {
                    initialization_surface_propositions
                        .borrow_mut()
                        .record_lowering(written, lowered)?;
                }
                // The certificate keeps the invariant's written spelling:
                // it is what the source names and what expansion prints.
                let step = ProofTactic::Have(ProofHave {
                    proposition: written.clone(),
                    proof: SourceProof::Script(planned_certificate.to_proof_tactics().to_vec()),
                });
                // A smart `have` inside the phase script expands to the same
                // `have` with the planned body: the step this invariant
                // contributes, printed where the source wrote it.
                if planned_own_body_index.is_some()
                    && planned_own_body_index == selected_source_index
                {
                    record_proof_site_tactic_expansion(
                        expansion_capture.as_deref_mut(),
                        &initialize_site,
                        selected_source_index.unwrap_or_default(),
                        std::slice::from_ref(&step),
                    );
                }
                tactics.push(step);
                if !planning_available.contains(&planned_fact) {
                    planning_available.push(planned_fact);
                }
            }
            let certificate = ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` produced an invalid initialization certificate: {error:?}"
                ))
            })?;
            Ok((
                certificate,
                all_invariants_checked.then_some(planning_available),
            ))
        },
        |certificate| {
            if certificate.to_proof_tactics().len() < invariant_items.len() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` certificate has only {} steps for {} invariants",
                    certificate.to_proof_tactics().len(),
                    invariant_items.len()
                )));
            }
            let mut certificate_available = context.pure_facts.clone();
            let invariant_start = certificate.to_proof_tactics().len() - invariant_items.len();
            for (certificate_index, tactic) in certificate.to_proof_tactics().iter().enumerate() {
                // Certificate validation for the initialize phase never reaches
                // the checked drivers' tactic loop, so time each step here in
                // the same format and let `source_site_kind` classify it.
                let _timing = TacticTiming::new(
                    &claim_label,
                    certificate_index,
                    initialize_source_index,
                    tactic,
                    initialize_statement_index,
                );
                if certificate_index < invariant_start
                    && let ProofTactic::UnfoldPredicate(name) = tactic
                {
                    if environment.predicate_environment.get(name).is_none() {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index} names unknown predicate `{name}`"
                        )));
                    }
                    certificate_available = unfold_available_predicate_facts(
                        environment.predicate_environment,
                        environment.click_function_environment,
                        std::slice::from_ref(name),
                        &certificate_available,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index}: {message}"
                        ))
                    })?;
                    continue;
                }
                let ProofTactic::Have(have) = tactic else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` certificate step {certificate_index} is not a pure `have`"
                    )));
                };
                let invariant_index = certificate_index.checked_sub(invariant_start);
                if let Some(invariant_index) = invariant_index {
                    let proposition = invariant_items[invariant_index].proposition();
                    if &have.proposition != proposition {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` certificate step {certificate_index} changed invariant {invariant_index}"
                        )));
                    }
                }
                let step_claim_label = invariant_index
                    .map(|invariant_index| {
                        format!(
                            "{claim_label} (loop {loop_index} invariant {invariant_index} entry)"
                        )
                    })
                    .unwrap_or_else(|| format!("{claim_label} prerequisite {certificate_index}"));
                let surface_propositions = initialization_surface_propositions.borrow();
                // Check structured initialization through the same checked
                // proof object that emitted it, including both/and children.
                // Validation reads the same obligation, the same checked
                // goal, and the same lowering record the planner read, so
                // the certificate is rechecked against the goal it was
                // built for and its introductions reach the same nodes.
                let exact_entry_obligation = invariant_index.and_then(|index| {
                    let obligation_context = format!("loop {loop_index} invariant {index} entry");
                    entry_obligations
                        .iter()
                        .find(|obligation| obligation.context() == Some(&obligation_context))
                });
                let exact_entry_goal = exact_entry_obligation.map(|obligation| {
                    let (goal, stripped) = loop_entry_checked_goal_with_stripped(
                        obligation.proposition(),
                        &certificate_available,
                    );
                    let introductions = obligation
                        .introductions()
                        .map(|recorded| recorded.get(stripped..).unwrap_or_default().to_vec());
                    (goal, introductions)
                });
                let (fact, goal_introductions) = match exact_entry_goal {
                    Some(checked) => checked,
                    None => match surface_propositions
                        .unique_kernel(&have.proposition)
                        .cloned()
                    {
                        Some(fact) => (fact, None),
                        None => {
                            let (fact, recorded) =
                                lower_fixed_state_proposition_with_assumptions_recording_introductions(
                                    &have.proposition,
                                    &assumptions_from_propositions(&certificate_available),
                                    environment.parsed_function.parameters(),
                                    environment.arguments,
                                    environment.initial_state,
                                    &context.state,
                                    None,
                                    &recorded_snapshots,
                                    environment.predicate_environment,
                                    environment.click_function_environment,
                                )
                                .map_err(ClickError::new)?;
                            (fact, Some(recorded))
                        }
                    },
                };
                let root = Proof::for_fixed_state_surface_goal(
                    &step_claim_label,
                    certificate_index,
                    &certificate_available,
                    fact.clone(),
                    have.proposition.clone(),
                    environment.parsed_function.parameters(),
                    environment.arguments,
                    environment.initial_state,
                    &context.state,
                    &recorded_snapshots,
                    &surface_propositions,
                    environment.predicate_environment,
                    environment.click_function_environment,
                    environment.theorem_environment,
                    &[],
                    &[],
                )
                .with_recorded_goal_introductions(goal_introductions)
                .with_surface_local_scope(&phase_proof_scope(environment));
                let SourceProof::Script(tactics) = &have.proof else {
                    return Err(ClickError::new(
                        "invariant initialization requires an explicit proof body",
                    ));
                };
                let checked = root.try_authoritative_linear_script(tactics)?;
                if !checked.is_some_and(|proof| proof.is_complete()) {
                    return Err(ClickError::new(
                        "invariant initialization proof body did not close its goal",
                    ));
                }
                if !certificate_available.contains(&fact) {
                    certificate_available.push(fact);
                }
            }
            Ok(certificate_available)
        },
    )?;
    // The invariants hold at entry when every entry obligation the planner
    // and the certificate checker were given is discharged by the facts the
    // initialization proved. Re-lowering the invariants here instead would
    // derive them from a fact set the planner never saw, and ask for a
    // proposition the retained certificate never proved; `entry_obligations`
    // and `loop_entry_checked_goal` are the one goal function both phases
    // already use.
    for obligation in entry_obligations
        .iter()
        .filter(|obligation| obligation.context().is_some())
    {
        if !loop_entry_obligation_is_discharged(obligation.proposition(), &available) {
            return Err(ClickError::new(format!(
                "`{claim_label}`: missing invariant fact ({})",
                obligation.context().unwrap_or_default()
            )));
        }
    }
    Ok(certificate)
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
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
    let loop_body_statement_index = source_layout.loop_body_entry(loop_index).ok_or_else(|| {
        ClickError::new(format!("`{claim_label}` has no source loop({loop_index})"))
    })?;
    let frontier = ExecutionFrontier {
        position: FrontierPosition::StatementEntry {
            remaining: body.clone().into(),
        },
        region: ExecutionRegionKind::LoopBody,
        in_loop_body: true,
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
    let root = Proof::for_execution_frontier(
        &claim_label,
        0,
        ExecutionProofState::at_entry(
            preservation.state().clone(),
            frontier,
            recorded_snapshots,
            environment.surface_propositions.clone(),
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
        if proof.is_at_region_boundary() {
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
    merge_path_aligned_certificates(&claim_label, paths)
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
    ranking_measures: &[CExpression],
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
    let source_layout = SourceExecutionLayout::new(environment.parsed_function.body());
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
        execution_start_state: Some(preservation.state().clone()),
        next_statement_index: loop_body_statement_index,
        ..ExecutionFrontier::default()
    };
    let mut recorded_snapshots = RecordedSnapshots::new();
    let mut constants = ExecutionProofConstants {
        proof_site: Some(preserve_site),
        invariant_body_context: Some(Arc::new(InvariantBodyContext {
            loop_entry_state: preservation.loop_entry_state().clone(),
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
    {
        let surfaces = if do_while {
            invariant_surfaces.iter().collect::<Vec<_>>()
        } else {
            invariant_surfaces
                .iter()
                .chain(std::iter::once(&loop_condition))
                .collect::<Vec<_>>()
        };
        for surface in surfaces {
            if let Ok(lowered) = lower_fixed_state_proposition(
                surface,
                pure_facts,
                environment.parsed_function.parameters(),
                environment.arguments,
                environment.initial_state,
                preservation.state(),
                None,
                &recorded_snapshots,
                environment.predicate_environment,
                environment.click_function_environment,
            ) {
                let surface = surface_at_snapshot(
                    surface,
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(loop_body_statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?;
                surface_propositions.record_lowering(&surface, &lowered)?;
                loop_head_premises.push(surface);
            }
        }
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
    let root = Proof::for_execution_frontier(
        &claim_label,
        internal_proof_first_index(&program).unwrap_or(0),
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
    let mut leaves = Vec::new();
    advance_preservation_region(
        root,
        &program,
        &[],
        expansion_capture.as_deref_mut(),
        proof_site_for_driver.as_ref(),
        owning_source_index,
        &claim_label,
        &mut leaves,
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
    for leaf in leaves {
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
        if is_break_exit {
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
        let checked = if is_break_exit {
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
        if is_break_exit {
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
        let closer_tactics = if is_break_exit
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
    let certificate = merge_path_aligned_certificates(&claim_label, certificate_paths)?;
    Ok(LoopPreservationProofResult {
        certificate,
        final_exit_candidates,
        break_exits,
        nested_loop_rules,
    })
}

#[cfg(test)]
mod loop_entry_goal_tests {
    use super::*;

    fn variable_is_zero(variable: u64) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(variable))),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        )
    }

    #[test]
    fn only_exactly_available_leading_antecedents_are_stripped() {
        let first = variable_is_zero(1);
        let second = variable_is_zero(2);
        let conclusion = variable_is_zero(3);
        let obligation = Proposition::Implies(
            Box::new(first.clone()),
            Box::new(Proposition::Implies(
                Box::new(second.clone()),
                Box::new(conclusion.clone()),
            )),
        );

        assert_eq!(loop_entry_checked_goal(&obligation, &[]), obligation);
        // A second antecedent is only reachable once the first one is gone:
        // stripping stops at the first antecedent that is not exactly available.
        assert_eq!(
            loop_entry_checked_goal(&obligation, std::slice::from_ref(&second)),
            obligation
        );
        assert_eq!(
            loop_entry_checked_goal(&obligation, std::slice::from_ref(&first)),
            Proposition::Implies(Box::new(second.clone()), Box::new(conclusion.clone()))
        );
        assert_eq!(
            loop_entry_checked_goal(&obligation, &[first, second]),
            conclusion
        );
    }
}
