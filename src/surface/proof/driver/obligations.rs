//! Proof script orchestration; explicit operations remain on Proof.
use super::*;
use crate::surface::proof::driver::ProofDriver;

/// The first requirement the implicit closer could not prepare or prove.
pub(in crate::surface::proof) struct MissedObligation {
    index: usize,
    reason: RequirementMiss,
}

enum RequirementMiss {
    SearchDisabled,
    CannotRaise,
    CannotOpen(String),
    SafetyRaise,
    SafetyOpen(String),
    Search,
}

impl MissedObligation {
    fn classify(&self, error: ClickError) -> ClickError {
        match &self.reason {
            RequirementMiss::SearchDisabled => error,
            RequirementMiss::CannotRaise
                if error.kind() == ClickErrorKind::Proof && error.proof_refusal().is_none() =>
            {
                error.with_safety_preparation_error(
                    "Click could not express the requirement for implicit proof search",
                )
            }
            RequirementMiss::CannotOpen(cause)
                if error.kind() == ClickErrorKind::Proof && error.proof_refusal().is_none() =>
            {
                error.with_safety_preparation_error(&format!(
                    "Click could not open the requirement for implicit proof search: {cause}"
                ))
            }
            RequirementMiss::CannotRaise | RequirementMiss::CannotOpen(_) => error,
            RequirementMiss::SafetyRaise => error.with_safety_preparation_error(
                "Click could not raise the generated statement safety obligation",
            ),
            RequirementMiss::SafetyOpen(cause) => error.with_safety_preparation_error(&format!(
                "Click could not open the generated statement safety obligation: {cause}"
            )),
            RequirementMiss::Search => {
                error.with_proof_refusal(crate::surface::ProofRefusal::ImplicitStatementSearch)
            }
        }
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Closes the back-edge bundle as `close_invariants() by { ... }` with
    /// `close()` on each member. The bundle conjoins its members, balanced for
    /// wide bundles, and each member may open with a spine of guards from
    /// earlier declarations; that fixed structure is descended by checked
    /// `both` and `intro` steps, and every member below it is closed by
    /// `close()` and nothing else. Every step advances this same `Proof`, so
    /// the retained certificate is the explicit proof `click expand` prints
    /// and re-verifies.
    pub(in crate::surface::proof) fn plan_invariant_bundle_closure(
        &self,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let proof = self.proof;
        let result = self.plan_invariant_bundle_member_closure();
        // A search refusal must retain the member it was checking, too. Keep
        // the innermost member: enclosing implication/quantifier scopes must
        // not replace it with the entire guarded bundle.
        if result.is_err() && !matches!(proof.goal(), Some(Proposition::And(_, _))) {
            UNCLOSED_BUNDLE_MEMBER.with(|member| {
                if member.borrow().is_none() {
                    *member.borrow_mut() = proof.bundle_member_spelling();
                }
            });
        }
        let result = result?;
        // A conjunction passes its open child's record up unchanged; any
        // other member that stays open is the one a refusal names, replacing
        // whatever leaf inside it was recorded first.
        if result.is_none() && !matches!(proof.goal(), Some(Proposition::And(_, _))) {
            record_unclosed_bundle_member(proof.bundle_member_spelling());
        }
        Ok(result)
    }

    /// One bundle member, closed by `close()` as the member is spelled: a
    /// declared invariant as written, read at the back edge, and a ranking
    /// member as its `decreases` clause writes it
    /// ([`ranking_descent_surface`]), as a function's exit closes each
    /// `ensures` as written.
    fn close_bundle_member_by_solve(&self) -> Result<Option<Proof<'a>>, ClickError> {
        crate::kernel::search::ProofSearch::try_solve_closure(
            &(self.proof.with_synthesized_bundle_member_surface()),
        )
    }

    /// Establish the alternatives before a source `cases` splits. This is an
    /// ordinary nested proposition proof; the exact kernel split remains a
    /// simple operation and expansion retains the completed `have` body.
    pub(in crate::surface::proof) fn prove_cases_disjunction(
        &self,
        disjunction: &ClickProposition,
    ) -> Result<Proof<'a>, ClickError> {
        let proof = self.proof;
        let kernel = proof.lower_surface_proposition(disjunction, "`cases` disjunction")?;
        if proof.facts().contains(&kernel) {
            return Ok(proof.clone());
        }
        let scope = proof.driver().open_have(disjunction.clone())?;
        let refusal = || {
            scope.body().step_error(format!(
                "`cases` could not prove that its alternatives are exhaustive: `{}`",
                crate::surface::printing::source_click_proposition(disjunction)
            ))
        };
        if let Ok(closed) = scope.driver().apply_step(ProofStep::Known) {
            return closed.join();
        }
        if super::execution_statements::implicit_solve_disabled() {
            return Err(refusal());
        }
        let _timing = crate::surface::proof::timing::TacticTiming::implicit_solve();
        let _origin = crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit solve");
        let Some(closed) = scope.driver().try_solve_closure()? else {
            return Err(
                refusal().with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch)
            );
        };
        closed.join()
    }

    pub(in crate::surface::proof) fn apply_execution_statement_step(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        #[cfg(test)]
        let hidden_before = crate::instrumentation::hidden_prerequisites_on_thread();
        let result = driver_proof.driver().apply_bare_statement_step(step);
        #[cfg(test)]
        if crate::instrumentation::hidden_prerequisites_on_thread() > hidden_before {
            crate::surface::proof::cursor_execution::record_planning_statement_transition(
                driver_proof.context.claim_label(),
                driver_proof.node.depth,
                "step",
            );
        }
        result
    }

    /// Check the written proof immediately against the exact lowered goals.
    /// The kernel owns the scope and retains its completed proof as bound
    /// closure evidence; finalization validates it without reproving it.
    /// Applies `step` with explicit proofs of its generated obligations.
    /// A plain `by` (`entries` is
    /// `None`) proves the one open obligation; `requires` entries each prove
    /// the open obligation their proposition states. `prove` checks one proof
    /// as a `have` at this pre-state, through whichever driver reads the
    /// written body, and returns the joined Proof; `None` as its index means
    /// the plain `by` body.
    ///
    /// Obligations without a written proof are handed to ordinary `solve`.
    pub(in crate::surface::proof) fn apply_step_with_obligation_proofs(
        &self,
        step: ProofStep,
        entries: Option<&[(Option<String>, ClickProposition)]>,
        prove: &mut dyn FnMut(
            &Proof<'a>,
            ClickProposition,
            Option<usize>,
        ) -> Result<Proof<'a>, ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        if !matches!(step, ProofStep::FoldResource(_) | ProofStep::UserTactic(_)) {
            driver_proof.require_execution_frontier("a step's obligation proofs")?;
        }
        let this = if matches!(step, ProofStep::FoldResource(_)) {
            "this `fold`"
        } else {
            "this step"
        };
        let (probe, recorded) = driver_proof.prepare_step(&step);
        // A successful preparation is conditional on every recorded requirement.
        // Keep it private while those requirements are proved at `self`, never
        // in the candidate's post-state. A refusal is not a resumable result.
        let prepared_frontier =
            driver_proof.with_prepared_call_parameters(probe.as_ref().map_err(Clone::clone)?);
        let driver_proof = &prepared_frontier;
        let refusals = recorded.refusals;
        let recorded_requirements = recorded.recorded;
        let open = distinct_requirements(recorded_requirements.clone());
        let spelling = |requirement: &UnresolvedRequirement| -> Result<String, ClickError> {
            Ok(
                match driver_proof.requirement_surface(requirement, &step)? {
                    Some(spelling) => {
                        crate::surface::printing::source_click_proposition(&spelling.surface)
                    }
                    None => format!(
                        "{} (no Surface form: report this as a bug)",
                        driver_proof
                            .execution()
                            .map(|execution| {
                                crate::surface::diagnostics::describe_stated_fact_over_locals(
                                    &requirement.proposition,
                                    &execution.core.state,
                                )
                            })
                            .unwrap_or_else(|| format!("{:?}", requirement.proposition))
                    ),
                },
            )
        };
        let open_list = || -> Result<String, ClickError> {
            Ok(open
                .iter()
                .map(|requirement| spelling(requirement).map(|spelled| format!("`{spelled}`")))
                .collect::<Result<Vec<_>, _>>()?
                .join(", "))
        };
        let mut current = driver_proof.clone();
        let proof = match entries {
            None => {
                let [requirement] = open.as_slice() else {
                    if open.is_empty() {
                        return Err(driver_proof.step_error(format!(
                            "{this}'s `by` is superfluous: it generates no obligation; write it without `by`",
                        )));
                    }
                    let entries = open
                        .iter()
                        .map(|requirement| {
                            spelling(requirement)
                                .map(|spelled| format!("    requires {spelled} by close();"))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .join("\n");
                    return Err(driver_proof.step_error(format!(
                        "a `by` proves its one open obligation, but {this} leaves {} open; write one `requires` entry for each:\n{{\n{entries}\n}}",
                        open.len()
                    )));
                };
                let Some(surface) = driver_proof
                    .requirement_surface(requirement, &step)?
                    .map(|spelling| spelling.surface)
                else {
                    return Err(driver_proof.step_error(format!(
                        "{this}'s open obligation {} cannot be proved by `by`",
                        spelling(requirement)?
                    )));
                };
                let checkpoint = current.checkpoint();
                current = prove(&current, surface, None)?;
                StepProofCertificate::By(Box::new(retained_have_body(
                    &current.certificate_since(&checkpoint)?,
                )?))
            }
            Some(entries) => {
                let mut claimed: Vec<Option<usize>> = vec![None; open.len()];
                let mut proved = Vec::with_capacity(entries.len());
                for (index, (label, proposition)) in entries.iter().enumerate() {
                    let written = crate::surface::printing::source_click_proposition(proposition);
                    let lowered = current.lower_surface_goal(proposition, "`requires` entry")?;
                    let Some(slot) = open.iter().position(|requirement| {
                        driver_proof.written_states_requirement(&lowered, requirement)
                    }) else {
                        let open_now = if open.is_empty() {
                            "it leaves none open".to_string()
                        } else {
                            format!("it leaves open {}", open_list()?)
                        };
                        return Err(driver_proof.step_error(format!(
                            "`requires {written}` matches no obligation {this} leaves open: it does not require it; {open_now}"
                        )));
                    };
                    if let Some(earlier) = claimed[slot] {
                        return Err(driver_proof.step_error(format!(
                            "`requires {written}` proves the same obligation as `requires` entry {}",
                            earlier + 1
                        )));
                    }
                    claimed[slot] = Some(index);
                    let checkpoint = current.checkpoint();
                    current = prove(&current, proposition.clone(), Some(index))?;
                    proved.push(StepRequirementCertificate {
                        label: label.clone(),
                        proposition: proposition.clone(),
                        proof: retained_have_body(&current.certificate_since(&checkpoint)?)?,
                    });
                }
                // The obligations no entry writes go to the implicit `solve`;
                // expansion prints each one it proves as an entry.
                let unwritten = open
                    .iter()
                    .zip(&claimed)
                    .filter(|(_, claimed)| claimed.is_none())
                    .map(|(requirement, _)| requirement)
                    .collect::<Vec<_>>();
                if !unwritten.is_empty() {
                    let result = if implicit_solve_disabled() {
                        Err(MissedObligation {
                            index: 0,
                            reason: RequirementMiss::SearchDisabled,
                        })
                    } else {
                        current
                            .driver()
                            .prove_obligations_by_solve_or_name_the_first_missed(
                                &step, &unwritten,
                            )?
                    };
                    match result {
                        Ok((proved_by_solve, entries)) => {
                            current = proved_by_solve;
                            proved.extend(entries);
                        }
                        Err(missed) => {
                            let position = recorded_requirements
                                .iter()
                                .position(|requirement| {
                                    crate::kernel::proof::propositions_are_alpha_equal(
                                        &requirement.proposition,
                                        &unwritten[missed.index].proposition,
                                    )
                                })
                                .expect("an open requirement came from preparation");
                            return Err(missed.classify(unproved_step_requirement(
                                driver_proof,
                                &step,
                                unwritten[missed.index],
                                refusals[position].clone(),
                            )?));
                        }
                    }
                }
                StepProofCertificate::Requires(proved)
            }
        };
        // Both written and unwritten obligation slots have been discharged.
        let stepped = driver_proof.finish_prepared_step(probe, &current, &recorded_requirements)?;
        Ok(driver_proof.step_proved_successor(stepped, step, proof))
    }

    /// A bare step: generate obligations, then run ordinary implicit `solve`
    /// for each one, recording the proofs so that
    /// expansion prints the step with a `by` or `requires` entries. A step
    /// never searches the proof context: when the implicit `solve` cannot spell
    /// or prove an obligation, the fast path refuses the step at it.
    pub(in crate::surface::proof) fn apply_bare_statement_step(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        self.plan_bare_statement_step(step, true)
    }

    fn plan_bare_statement_step(
        &self,
        step: ProofStep,
        retain_order_bounds: bool,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        // An obligation the implicit `solve` cannot spell or prove refuses the
        // step with the fast path's own diagnostic, naming that obligation.
        let ((probe, recorded), suppliers) =
            if matches!(step, ProofStep::Step) && !implicit_solve_disabled() {
                crate::kernel::call_supplier_selection::capture(|| driver_proof.prepare_step(&step))
            } else {
                (driver_proof.prepare_step(&step), Vec::new())
            };
        if let [head] = suppliers.as_slice()
            && probe.is_ok()
            && recorded.recorded.is_empty()
            && let Some(unfold) = crate::kernel::search::ProofSearch::selected_call_supplier_unfold(
                driver_proof,
                head,
            )
            && let Ok(opened) = driver_proof.driver().apply_step(unfold)
        {
            // The chosen head is only a hint for the certificate. Check the
            // same step after the written unfold with supplier lookup disabled.
            let (attempt, obligations) =
                crate::kernel::call_supplier_selection::without_search(|| {
                    opened.prepare_step(&step)
                });
            if let Ok(stepped) = attempt
                && obligations.recorded.is_empty()
            {
                return Ok(stepped);
            }
        }
        let prepared_frontier =
            driver_proof.with_prepared_call_parameters(probe.as_ref().map_err(Clone::clone)?);
        if recorded.recorded.is_empty() {
            if probe.as_ref().is_ok_and(|candidate| {
                candidate.execution().is_some_and(|execution| {
                    execution.core.has_prepared_fold()
                        || execution.core.has_prepared_tactic_application()
                })
            }) {
                return driver_proof.finish_prepared_step(probe, driver_proof, &[]);
            }
            // With nothing recorded, the probe ran the ordinary checked step.
            return probe;
        }
        let driver_proof = &prepared_frontier;
        let refusals = recorded.refusals;
        if implicit_solve_disabled() {
            return Err(unproved_step_requirement(
                driver_proof,
                &step,
                &recorded.recorded[0],
                refusals[0].clone(),
            )?);
        }
        let recorded = recorded.recorded;
        let open = distinct_requirements(recorded.clone());
        if retain_order_bounds && matches!(step, ProofStep::Step) {
            let timing = crate::surface::proof::timing::TacticTiming::implicit_solve();
            let origin = crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit solve");
            let mut frontier = self.proof.clone();
            let mut retained = false;
            for requirement in &open {
                if requirement.call_site.is_some() {
                    continue;
                }
                if let Some(next) =
                    crate::kernel::search::ProofSearch::retain_computed_shift_divisor_bound(
                        &frontier,
                        &requirement.proposition,
                    )?
                {
                    frontier = next;
                    retained = true;
                    continue;
                }
                let Some(spelling) = driver_proof.requirement_surface(requirement, &step)? else {
                    continue;
                };
                let mut leaves = Vec::new();
                super::proof_object::collect_surface_conjunct_leaves(
                    &spelling.surface,
                    &mut leaves,
                );
                for leaf in &leaves {
                    if let Some(next) =
                        crate::kernel::search::ProofSearch::retain_signed_order_bounds(
                            &frontier, leaf, 3,
                        )
                    {
                        frontier = next;
                        retained = true;
                    }
                }
            }
            drop(origin);
            drop(timing);
            if retained {
                // Reprepare against the facts that appear before the step in
                // the expanded proof. An established bound changes which
                // requirements the statement still needs written proofs for.
                return frontier.driver().plan_bare_statement_step(step, false);
            }
        }
        let open = open.iter().collect::<Vec<_>>();
        let (proved, mut entries) = match driver_proof
            .driver()
            .prove_obligations_by_solve_or_name_the_first_missed(&step, &open)?
        {
            Ok(proved) => proved,
            // Refuse at the obligation the implicit `solve` missed, with
            // the fast path's own diagnostic for it; another open
            // obligation it did prove is not what is wrong.
            Err(missed) => {
                let position = recorded
                    .iter()
                    .position(|requirement| {
                        crate::kernel::proof::propositions_are_alpha_equal(
                            &requirement.proposition,
                            &open[missed.index].proposition,
                        )
                    })
                    .expect("a missed obligation came from preparation");
                return Err(missed.classify(unproved_step_requirement(
                    driver_proof,
                    &step,
                    open[missed.index],
                    refusals[position].clone(),
                )?));
            }
        };
        let stepped = driver_proof.finish_prepared_step(probe, &proved, &recorded)?;
        let proof = if entries.len() == 1 {
            StepProofCertificate::By(Box::new(entries.pop().expect("one entry").proof))
        } else {
            StepProofCertificate::Requires(entries)
        };
        Ok(driver_proof.step_proved_successor(stepped, step, proof))
    }

    /// Proves each requirement at this pre-state, or returns the index of
    /// the first requirement it could not spell or prove.
    pub(in crate::surface::proof) fn prove_obligations_by_solve_or_name_the_first_missed(
        &self,
        step: &ProofStep,
        requirements: &[&UnresolvedRequirement],
    ) -> Result<Result<(Proof<'a>, Vec<StepRequirementCertificate>), MissedObligation>, ClickError>
    {
        let driver_proof = self.proof;
        let _implicit_solve = crate::surface::proof::timing::TacticTiming::implicit_solve();
        let _origin = crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit solve");
        let mut current = driver_proof.clone();
        let mut entries = Vec::with_capacity(requirements.len());
        for (index, requirement) in requirements.iter().enumerate() {
            let Some(spelling) = current.requirement_surface(requirement, step)? else {
                check_verification_deadline()?;
                return Ok(Err(MissedObligation {
                    index,
                    reason: if requirement.statement_safety {
                        RequirementMiss::SafetyRaise
                    } else {
                        RequirementMiss::CannotRaise
                    },
                }));
            };
            let surface = spelling.surface.clone();
            current.debug_assert_spelling_relowers(requirement, &surface);
            let checkpoint = current.checkpoint();
            let have = match current.driver().open_have(surface.clone()) {
                Ok(have) => have,
                Err(error)
                    if error.kind() != crate::surface::ClickErrorKind::Proof
                        || crate::instrumentation::exceeded_verification_limit_context()
                            .is_some() =>
                {
                    return Err(error);
                }
                Err(error) => {
                    check_verification_deadline()?;
                    return Ok(Err(MissedObligation {
                        index,
                        reason: if requirement.statement_safety {
                            RequirementMiss::SafetyOpen(error.raw_summary().to_owned())
                        } else {
                            RequirementMiss::CannotOpen(error.raw_summary().to_owned())
                        },
                    }));
                }
            };
            let Some(closed) = have.driver().try_solve_closure()? else {
                return Ok(Err(MissedObligation {
                    index,
                    reason: RequirementMiss::Search,
                }));
            };
            current = closed.join()?;
            entries.push(StepRequirementCertificate {
                label: None,
                proposition: surface,
                proof: retained_have_body(&current.certificate_since(&checkpoint)?)?,
            });
        }
        Ok(Ok((current, entries)))
    }

    pub(in crate::surface::proof) fn apply_close_invariants_body(
        &self,
        body: &[ProofTactic],
        boundary: Option<&LoopBoundary>,
        implicit_tail: bool,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        driver_proof.require_execution_frontier("`close_invariants() by`")?;
        if body.is_empty() {
            return Err(
                driver_proof.step_error("`close_invariants() by` requires a nonempty proof body")
            );
        }
        if driver_proof
            .execution()
            .is_some_and(|execution| execution.core.frontier.loop_control.is_exit())
        {
            // A `break` leaves the loop with whatever the path established.
            // There is no back edge here and the invariants are not owed, so
            // closing them would certify an obligation the rule never asks
            // for and report success for a path the loop exports as an exit.
            return Err(driver_proof.step_error(
                "`close_invariants` has no back edge on a `break` path: a `break` exits the loop",
            ));
        }
        if !driver_proof.is_at_region_boundary() {
            return Err(
                driver_proof.step_error("`close_invariants() by` requires the loop back edge")
            );
        }
        let ProofContext::Execution(context) = driver_proof.context.as_ref() else {
            return Err(driver_proof.step_error("`close_invariants() by` requires a loop proof"));
        };
        let Some(bundle) = context.constants.invariant_body_context.as_deref() else {
            return Err(driver_proof
                .step_error("`close_invariants() by` requires a loop invariant context"));
        };
        let execution = driver_proof
            .execution()
            .ok_or_else(|| driver_proof.step_error("missing loop execution state"))?;
        if execution.core.region_invariants_close_requested {
            return Err(driver_proof
                .step_error("the invariant bundle was closed more than once on one path"));
        }
        // Internal closure certificates can be replayed on their own. The
        // normal preservation driver already supplies its checked boundary.
        let replay_boundary = if boundary.is_none()
            && !bundle.ranking_measures.is_empty()
            && let Some(condition) = bundle.entry_guard.as_deref()
        {
            Some(driver_proof.check_loop_boundary(
                &bundle.loop_entry_state,
                &bundle.iteration_entry_state,
                bundle.iterations.as_ref().ok_or_else(|| {
                    driver_proof.step_error("loop invariant bundle lost its pass count")
                })?,
                Some(condition),
                &bundle.checks,
                &bundle.binders,
                bundle.structural_measure.as_deref(),
                context.function.composite_resource_definitions(),
                true,
            )?)
        } else {
            None
        };
        let boundary = boundary.or(replay_boundary.as_ref());
        let ranking_measures = boundary.map_or(bundle.ranking_measures.as_slice(), |boundary| {
            boundary.required_ranking_measures(&bundle.ranking_measures)
        });
        let closure_context = if ranking_measures.len() == bundle.ranking_measures.len() {
            driver_proof.context.clone()
        } else {
            let mut context = context.with_tactic_index(context.tactic_index);
            let bundle = Arc::make_mut(&mut context.constants)
                .invariant_body_context
                .as_mut()
                .expect("closure owns its bundle");
            let bundle = Arc::make_mut(bundle);
            bundle.ranking_measures.clear();
            bundle.ranking_surfaces.clear();
            Arc::new(ProofContext::Execution(context))
        };
        let ProofContext::Execution(closure) = closure_context.as_ref() else {
            unreachable!("closure has an execution context");
        };
        let bundle = closure
            .constants
            .invariant_body_context
            .as_deref()
            .expect("closure owns its bundle");
        // The C branches this path took, recorded when it took them. They are
        // read here, before the bundle scope opens, so the closer names this
        // path's decisions and no sibling arm's.
        //
        // Each is named twice, exactly as a declared invariant is: once
        // re-read at iteration entry, where it shares the invariants' own
        // spelling so one arithmetic step can pair the two, and once
        // at the statement that branched, which is the spelling that still
        // holds when the body has since written the cells the condition read.
        // The closer keeps whichever lowers exactly and cites the fact once.
        let mut path_branch_premises = Vec::new();
        for recorded in execution.presentation.path_branch_premises.iter() {
            if let Some(selector) = bundle.iteration_entry_selector.as_ref()
                && let Ok(at_iteration_entry) = surface_at_program_point(recorded, selector)
            {
                path_branch_premises.push(at_iteration_entry);
            }
            path_branch_premises.push(recorded.clone());
        }
        let prepare_timing = crate::instrumentation::OperationTiming::new(
            "surface",
            "close invariants",
            "close invariants: prepare checked bundle",
        );
        let standalone_edge;
        let edge = if let Some(boundary) = boundary {
            boundary.prepared_edge()
        } else {
            standalone_edge = driver_proof
                .state
                .prepare_loop_invariant_edge(
                    &bundle.loop_entry_state,
                    &bundle.iteration_entry_state,
                    bundle.iterations.as_ref().ok_or_else(|| {
                        driver_proof.step_error("loop invariant bundle lost its pass count")
                    })?,
                    &bundle.checks,
                    &bundle.binders,
                    Some(context.function.composite_resource_definitions()),
                )
                .map_err(|error| driver_proof.step_error(error))?;
            &standalone_edge
        };
        let (state, scope) = driver_proof
            .state
            .open_prepared_invariant_body(
                edge,
                &bundle.ranking_measures,
                |goal, introductions| {
                    let both_children = if introductions.len() == 2
                        && bundle.checks.len() == 2
                        && bundle.declared_invariant_surfaces.len() == 2
                    {
                        match goal {
                            Proposition::And(left, right) => Some(std::sync::Arc::new([
                                BothChildPresentation {
                                    kernel: left.as_ref().clone(),
                                    surface: bundle.declared_invariant_surfaces.first().cloned(),
                                    introductions: introductions[0]
                                        .clone()
                                        .unwrap_or_else(|| std::sync::Arc::new(Vec::new())),
                                },
                                BothChildPresentation {
                                    kernel: right.as_ref().clone(),
                                    surface: bundle.declared_invariant_surfaces.get(1).cloned(),
                                    introductions: introductions[1]
                                        .clone()
                                        .unwrap_or_else(|| std::sync::Arc::new(Vec::new())),
                                },
                            ])),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    // The whole bundle's spelling names each quantified
                    // member's binder as its invariant wrote it; the surface
                    // is validated by lowering wherever a proof relies on it.
                    let presentation_timing = crate::instrumentation::OperationTiming::new(
                        "surface", "close invariants", "close invariants: source presentation",
                    );
                    let presentation = PropositionPresentation {
                        surface: crate::surface::proof::surface_synthesis::with_synthesis_binder_names(
                            &bundle.binder_names,
                            || crate::surface::proof::surface_synthesis::synthesize_surface_proposition_at_entry_post_and_state(
                                goal,
                                context.parameter_binding(),
                                context.old_reference_state(&execution.core.frontier, &execution.core.state),
                                &execution.core.state,
                                bundle
                                    .iteration_entry_selector
                                    .as_ref()
                                    .map(|selector| (&bundle.iteration_entry_state, selector)),
                            ),
                        )
                        .map(Arc::new),
                        surface_bindings: PersistentBinderMap::default(),
                        both_children,
                    ..PropositionPresentation::default()
                    };
                    drop(presentation_timing);
                    presentation
                },
            )
            .map_err(|message| driver_proof.step_error(message))?;
        drop(prepare_timing);
        let root = Proof {
            site: driver_proof.site.clone(),
            context: closure_context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
                split_branches: Vec::new(),
            }),
        };
        // The bundle's proof reads the head's pass count as `iterations`.
        let root = match &bundle.iterations {
            Some(count) => root.with_loop_iterations(count),
            None => root,
        };
        if let Some(parent_lineage) = driver_proof.trace_lineage(driver_proof.claim_label()) {
            // Diagnostics cross the scope boundary; certificates remain
            // rooted here. Retain both chains after the lazy lineage is read
            // so another attempt cannot recycle their pointer identities.
            crate::surface::proof_trace::register_scope(
                Arc::as_ptr(&root.node) as usize,
                parent_lineage,
                Box::new((root.node.clone(), driver_proof.node.clone())),
            );
        }
        let mut search = attempt::search_scope("close invariants body");
        let checkpoint = root.checkpoint();
        // A bare `close_invariants()` closes each member with `close()`; an
        // explicit source body runs through the source driver exactly once.
        let _ = take_unclosed_bundle_member();
        // Catch every error here; `?` must not skip the obligation
        // diagnostic below.
        if body == [ProofTactic::Solve]
            && crate::surface::proof::implicit_solve_scope::checked_only()
        {
            return Err(driver_proof.step_error(
                "checked-only verification requires an explicit proof for `close_invariants()`",
            ));
        }
        let attempted = {
            if body == [ProofTactic::Solve] {
                crate::instrumentation::measure_operation(
                    "surface",
                    "close invariants",
                    "close invariants: members",
                    || root.driver().plan_invariant_bundle_closure(),
                )
            } else {
                // A written body that ran every step and still left a goal open
                // names that goal, as the member planner names the member it
                // stopped at.
                let mut unfinished = None;
                let attempted = crate::instrumentation::measure_operation(
                    "surface",
                    "close invariants",
                    "close invariants: explicit body",
                    || {
                        root.driver().try_authoritative_linear_script_leaving_open(
                            body,
                            &mut unfinished,
                            implicit_tail,
                        )
                    },
                );
                if matches!(attempted, Ok(None))
                    && let Some(unfinished) = unfinished
                {
                    record_unclosed_bundle_member(unfinished.bundle_member_spelling());
                }
                attempted
            }
        };
        let attempted = match attempted {
            Ok(attempted) => attempted,
            Err(error) => {
                let error = describe_invariant_closure_error(error);
                // The ranking note continues the reason; it is not a prefix.
                let detail = ranking_member_diagnostic(bundle);
                let error = if detail.is_empty() {
                    error
                } else {
                    error.with_rewritten_place(|reason| Some(format!("{reason}{detail}")))
                };
                return Err(error.with_search_failures(search.finish()));
            }
        };
        let Some(completed) = attempted else {
            // The member planner stops at the first bundle member it cannot
            // close, so that member is the one to name.
            let open_member = take_unclosed_bundle_member()
                .map(|member| format!(": `{member}` remained open"))
                .unwrap_or_default();
            let rejoined = if let Some(cases) = crate::surface::proof::preservation_cases_rejoined()
            {
                format!(
                    ". This path left the `cases` at tactic {cases}, whose arms rejoined at the back edge, and the rejoined path is closed again with only the facts every arm proved, so a fact one arm established is gone here. To keep it, prove the same proposition in every arm, such as the invariants at the next iteration"
                )
            } else {
                String::new()
            };
            let branch_join = if matches!(
                driver_proof.node.step.as_deref(),
                Some(ProofStep::Branch { then_proof, else_proof, .. })
                    if !then_proof.is_pruned_execution_arm() && !else_proof.is_pruned_execution_arm()
            ) {
                ". The obligation is checked after the `branch` join, which keeps only facts both arms agree on. Use `branch ensuring { ... }` to carry a shared fact across the join, or a proof `if` to keep the cases apart"
            } else {
                ""
            };
            let error = root.step_error(format!(
                "closure body did not prove every invariant obligation{open_member}{}{rejoined}{branch_join}",
                ranking_member_diagnostic(bundle)
            ));
            let refusal = if body == [ProofTactic::Solve] {
                crate::surface::ProofRefusal::UnsuccessfulSearch
            } else {
                crate::surface::ProofRefusal::IncompleteProof
            };
            return Err(error
                .with_proof_refusal(refusal)
                .with_search_failures(search.finish()));
        };
        search.succeed();
        let retain_timing = crate::instrumentation::OperationTiming::new(
            "surface",
            "close invariants",
            "close invariants: retain checked body",
        );
        let certificate = completed.certificate_since(&checkpoint)?;
        let state = driver_proof
            .state
            .retain_invariant_body(scope, &completed.state)
            .map_err(|message| driver_proof.step_error(message))?;
        drop(retain_timing);
        Ok(Proof {
            site: driver_proof.site.clone(),
            context: driver_proof.context.clone(),
            state,
            node: ProofNode::step_child(
                &driver_proof.node,
                driver_proof.focused_branch_id(),
                Arc::new(ProofStep::CloseInvariantsBy(Box::new(certificate))),
            ),
        })
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    pub(in crate::surface::proof) fn plan_invariant_bundle_member_closure(
        &self,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        check_verification_deadline()?;
        let Some(goal) = driver_proof.goal() else {
            return Ok(None);
        };
        // Expanded preservation proofs already publish their invariant facts.
        // Check exact availability, including conjunction leaves, before
        // opening the planner's search scope or spelling individual members.
        if let Some(closed) = crate::instrumentation::measure_operation(
            "surface",
            "close invariants",
            "close invariants: exact facts",
            || attempt::candidate_outcome(driver_proof.driver().apply_step(ProofStep::Known)),
        )? {
            return Ok(Some(closed));
        }
        let _planning = crate::instrumentation::OperationTiming::new(
            "surface",
            "close invariants",
            "close invariants: member planning",
        );
        let mut scope = attempt::search_scope("loop invariant bundle closure");
        // The generated invariant bundle can have no Surface form. Its
        // conjunction and implication structure is nevertheless checked by
        // the kernel, so descend that structure directly and retain the
        // ordinary Both/Intro certificate nodes.
        // The bundle is closed member by member, `have m by { ... }` for
        // each and then `known`, as a function's exit closes its
        // `ensures`; expansion writes those `have`s at the back edge. A
        // member's own proof does not take this path again.
        if !IN_BUNDLE_MEMBER_HAVE.with(std::cell::Cell::get)
            && let Some(surfaces) = driver_proof.conjunction_leaf_surfaces(1)
        {
            let mut proof = driver_proof.clone();
            for surface in surfaces {
                let nested = proof.driver().open_have(surface)?;
                let previous = IN_BUNDLE_MEMBER_HAVE.with(|flag| flag.replace(true));
                let closed = nested.driver().plan_invariant_bundle_closure();
                IN_BUNDLE_MEMBER_HAVE.with(|flag| flag.set(previous));
                let Some(closed) = closed? else {
                    return Ok(None);
                };
                proof = closed.join()?;
            }
            if let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
            // A member's `have` publishes its written spelling as lowered,
            // which can differ from the kernel member in form, as a
            // quantified read projected at the back edge does. The bundle
            // then closes member by member from those facts.
            let previous = IN_BUNDLE_MEMBER_HAVE.with(|flag| flag.replace(true));
            let closed = proof.driver().plan_invariant_bundle_closure();
            IN_BUNDLE_MEMBER_HAVE.with(|flag| flag.set(previous));
            return closed;
        }
        if matches!(goal, Proposition::And(_, _)) {
            let (split_proof, split, ids) = driver_proof.split_focused_both()?;
            let marker = split_proof.conjunction_checkpoint(ids)?;
            let Some(left) = split_proof
                .focus_branch(ids[0])?
                .driver()
                .plan_invariant_bundle_closure()?
            else {
                return Ok(None);
            };
            let Some(right) = left
                .focus_branch(ids[1])?
                .driver()
                .plan_invariant_bundle_closure()?
            else {
                return Ok(None);
            };
            let result = attempt::candidate_outcome(right.join_focused_both(&marker, split, ids));
            if matches!(&result, Ok(Some(_))) {
                scope.succeed();
            }
            return result;
        }
        if matches!(goal, Proposition::Implies(_, _)) {
            // Later invariant declarations can have a long prefix of guards
            // from earlier declarations. Introduce that spine iteratively;
            // one native planner frame per guard overflows before a bounded
            // tactic can return, even though the certificate is sequential.
            let mut introduced = driver_proof.clone();
            while matches!(introduced.goal(), Some(Proposition::Implies(_, _))) {
                let Some(next) =
                    attempt::candidate_outcome(introduced.driver().apply_step(ProofStep::Intro))?
                else {
                    return Ok(None);
                };
                introduced = next;
            }
            let result = introduced.driver().plan_invariant_bundle_closure()?;
            if result.is_some() {
                scope.succeed();
                return Ok(result);
            }
            // A leaf the introduced premises contradict, as a guarded member
            // `done implies ...` is on a path whose test said `!done`: the
            // contradiction is between a premise and the context, so the
            // member closes whole, as `have` would close it.
            let whole = self.close_bundle_member_by_solve()?;
            if whole.is_some() {
                scope.succeed();
            }
            return Ok(whole);
        }
        let result = self.close_bundle_member_by_solve()?;
        if result.is_none() {
            // Keep one bounded, lazy diagnostic for the actual kernel leaf.
            // It is recorded only after `close()` has declined; it does not
            // turn a miss into an error.
            let diagnostic =
                driver_proof.step_error("checked loop invariant bundle leaf remained open");
            attempt::record_unclosed_goal("loop invariant bundle leaf", &diagnostic);
        }
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// Close an open resource, retaining any proofs of its restoration facts
    /// as ordinary `have` steps at the end of the block.
    pub(in crate::surface::proof) fn close_scope_with_body_fact_proof(
        &self,
        resource: &ResourceClause,
        restoration: &OpenResourceRestoration,
        close: &dyn Fn(&Proof<'a>) -> Result<Proof<'a>, ClickError>,
    ) -> Result<(Proof<'a>, Option<ProofCertificate>), ClickError> {
        let driver_proof = self.proof;
        if implicit_solve_disabled() {
            return Ok((close(driver_proof)?, None));
        }
        // A named close uses the ordinary prepared instance fold. Keep its
        // successor private until the missing body facts have been proved.
        let named = matches!(restoration, OpenResourceRestoration::Named(_));
        let (probe, recorded) = if named {
            super::super::execution_planning::probe_step_obligations(|| close(driver_proof))
        } else {
            probe_open_obligations(|| close(driver_proof))
        };
        if named && let Err(error) = &probe {
            return Err(error.clone());
        }
        let open = distinct_requirements(
            recorded
                .recorded
                .iter()
                .filter(|requirement| {
                    !named
                        || !driver_proof
                            .facts()
                            .assumptions()
                            .states_required_goal(&requirement.proposition)
                })
                .cloned()
                .collect(),
        );
        if open.is_empty() {
            let closed = if named
                && probe.as_ref().is_ok_and(|candidate| {
                    candidate
                        .execution()
                        .is_some_and(|execution| execution.core.has_prepared_fold())
                }) {
                driver_proof.finish_prepared_step(probe, driver_proof, &recorded.recorded)?
            } else {
                probe?
            };
            return Ok((closed, None));
        }
        let open = open.iter().collect::<Vec<_>>();
        let step = ProofStep::FoldResource(resource.clone());
        let (proved, entries) = match driver_proof
            .driver()
            .prove_obligations_by_solve_or_name_the_first_missed(&step, &open)?
        {
            Ok(proved) => proved,
            Err(missed) => {
                let position = recorded
                    .recorded
                    .iter()
                    .position(|requirement| {
                        crate::kernel::proof::propositions_are_alpha_equal(
                            &requirement.proposition,
                            &open[missed.index].proposition,
                        )
                    })
                    .unwrap_or(0);
                return Err(missed.classify(recorded.refusals[position].clone()));
            }
        };
        let haves = entries
            .into_iter()
            .map(|entry| ProofStep::Have {
                proposition: entry.proposition,
                proof: Box::new(entry.proof),
            })
            .collect();
        let closed = if named {
            driver_proof.finish_prepared_step(probe, &proved, &recorded.recorded)?
        } else {
            close(&proved)?
        };
        Ok((closed, Some(ProofCertificate::from_steps(haves)?)))
    }

    /// Discharge a theorem's retained entry requirements before its main
    /// proof. Explicit leading haves are already in the indexed fact store;
    /// otherwise the ordinary implicit solver produces those same haves.
    pub(in crate::surface::proof) fn discharge_entry_requirements(
        &self,
        surface_goal: &ClickProposition,
        requirements: &super::super::execution_planning::OpenObligationProbe,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        let pending = requirements
            .recorded
            .iter()
            .enumerate()
            .filter(|(_, requirement)| {
                !driver_proof
                    .facts()
                    .assumptions()
                    .states_required_goal(&requirement.proposition)
            })
            .collect::<Vec<_>>();
        if pending.is_empty() {
            return Ok(driver_proof.clone());
        }
        if implicit_solve_disabled() {
            return Err(requirements.refusals[pending[0].0].clone());
        }
        let step = ProofStep::Have {
            proposition: surface_goal.clone(),
            proof: Box::new(ProofCertificate::from_proof_tactics(&[]).expect("empty certificate")),
        };
        let references = pending
            .iter()
            .map(|(_, requirement)| *requirement)
            .collect::<Vec<_>>();
        match driver_proof
            .driver()
            .prove_obligations_by_solve_or_name_the_first_missed(&step, &references)?
        {
            Ok((proved, _)) => Ok(proved),
            Err(missed) => {
                Err(missed.classify(requirements.refusals[pending[missed.index].0].clone()))
            }
        }
    }

    /// Lowering requirements of a proof operation are proved at its input
    /// state. Keep the resulting `have` certificates before the operation,
    /// so expansion uses existing explicit proof syntax without searching.
    pub(in crate::surface::proof) fn with_proved_lowering_requirements<T>(
        &self,
        step: &ProofStep,
        operation: impl Fn(&Proof<'a>) -> Result<T, ClickError>,
    ) -> Result<T, ClickError> {
        let driver_proof = self.proof;
        let fast = || without_implicit_solve(|| operation(driver_proof));
        let (probe, recorded) = probe_open_obligations(fast);
        if probe.is_err()
            && let Some(refusal) = recorded.terminal_lowering_refusal
        {
            return Err(refusal);
        }
        if recorded.recorded.is_empty() {
            return probe;
        }
        let open = distinct_requirements(recorded.recorded.clone());
        let references = open.iter().collect::<Vec<_>>();
        match driver_proof
            .driver()
            .prove_obligations_by_solve_or_name_the_first_missed(step, &references)?
        {
            Ok((proved, _)) => without_implicit_solve(|| operation(&proved)),
            Err(missed) => {
                let position = recorded
                    .recorded
                    .iter()
                    .position(|requirement| {
                        crate::kernel::proof::propositions_are_alpha_equal(
                            &requirement.proposition,
                            &open[missed.index].proposition,
                        )
                    })
                    .expect("a distinct requirement came from the probe");
                Err(missed.classify(recorded.refusals[position].clone()))
            }
        }
    }

    /// Prepare complete back-edge lowering evidence for the loop planner.
    /// Return the checked boundary with the proof that closes its bundle.
    ///
    /// An exact completed closure body supplies both value and safety
    /// evidence. Automatic preservation plans that body through checked
    /// Surface operations; existing evidence is validated without discovery.
    /// Ordinary value facts alone do not replace the lowering's safety evidence.
    pub(in crate::surface::proof) fn prepare_loop_invariant_bundle(
        &self,
        loop_entry_state: &ExecutionState,
        loop_head_state: &ExecutionState,
        head_iterations: &crate::kernel::IntegerTerm,
        condition: Option<&ProgramExpression>,
        invariant_checks: &[LoopInvariantCheck],
        ranking_measures: &[crate::kernel::RankingComponent],
        structural_measure: Option<&str>,
        invariant_surfaces: &[ClickProposition],
        binders: &[crate::kernel::LoopBinder],
        composite_resource_definitions: &[CompositeResourceDefinition],
    ) -> Result<(Proof<'a>, LoopBoundary), ClickError> {
        let driver_proof = self.proof;
        let boundary = driver_proof.check_loop_boundary(
            loop_entry_state,
            loop_head_state,
            head_iterations,
            condition,
            invariant_checks,
            binders,
            structural_measure,
            composite_resource_definitions,
            true,
        )?;
        if !matches!(driver_proof.context.as_ref(), ProofContext::Execution(_)) {
            return Err(
                driver_proof.step_error("loop invariant closure requires an execution proof")
            );
        }
        driver_proof.require_execution_frontier("loop invariant closure")?;
        let execution = driver_proof.execution().ok_or_else(|| {
            driver_proof.step_error("loop invariant closure lost its execution state")
        })?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(
                driver_proof.step_error("loop invariant closure requires a loop-region proof")
            );
        }

        if invariant_surfaces.len() != invariant_checks.len() {
            return Err(driver_proof.step_error(
                "explicit invariant evidence does not align with the invariant bundle",
            ));
        }
        let proof = if execution.core.checked_invariant_lowerings.is_some() {
            driver_proof.clone()
        } else {
            driver_proof.driver().apply_close_invariants_body(
                &[ProofTactic::Solve],
                Some(&boundary),
                true,
            )?
        };
        proof.validate_loop_invariant_bundle(
            invariant_checks,
            boundary.required_ranking_measures(ranking_measures),
        )?;
        Ok((proof, boundary))
    }
}

fn unproved_step_requirement(
    proof: &Proof<'_>,
    step: &ProofStep,
    requirement: &UnresolvedRequirement,
    error: ClickError,
) -> Result<ClickError, ClickError> {
    // Assertion obligations describe the rejected path internally. On failure,
    // retain the assertion's positive source goal, just as direct execution
    // diagnostics do. This rendering runs only after obligation solving fails.
    if let Some(condition) = &requirement.assertion_condition
        && let Some(execution) = proof.execution()
        && let Some(goal) = crate::surface::proof::fact_reasoning::asserted_condition_goal(
            &execution.core.state,
            condition,
        )
    {
        let spelling = crate::surface::diagnostics::describe_stated_fact_over_locals(
            &goal,
            &execution.core.state,
        );
        return Ok(error
            .with_rewritten_place(|reason| {
                let (head, rest) = reason.split_once('\n').unwrap_or((reason, ""));
                Some(if rest.is_empty() {
                    format!("{head}; could not show `{spelling}`")
                } else {
                    format!("{head}; could not show `{spelling}`\n{rest}")
                })
            })
            .with_reported_assertion_goal(Some(goal)));
    }
    // Keep the existing concrete-refinement diagnostic when the ordinary
    // obligation solver cannot establish a named callback contract.
    if crate::surface::diagnostics::concrete_named_contract_fact(&requirement.proposition).is_some()
        && let ProofContext::Execution(context) = proof.context.as_ref()
    {
        let description = crate::surface::diagnostics::describe_pure_fact_with_environment(
            &requirement.proposition,
            context.parameter_binding(),
            context.function_environment,
            Some(context.spec_definitions.predicates),
        );
        return Ok(error.with_rewritten_place(|reason| Some(format!("{reason}; {description}"))));
    }
    let Some(spelling) = proof.requirement_surface(requirement, step)? else {
        return Ok(error);
    };
    let goal = crate::surface::printing::source_click_proposition(&spelling.surface);
    Ok(error
        .with_rewritten_place(|reason| Some(format!("{reason}\n  unproved obligation: `{goal}`"))))
}
