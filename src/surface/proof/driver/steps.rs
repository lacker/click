//! Proof script orchestration; explicit operations remain on Proof.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Checks one explicit proof step and atomically returns the checked
    /// successor with that exact step retained as evidence.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(in crate::surface::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        driver_proof.driver().apply_step_with_origin(step, None)
    }

    /// Applies a step while retaining its source occurrence for any ordered
    /// terminal work the checked transition has to schedule. The source site
    /// affects diagnostics and finalization order only; the certificate node
    /// remains exactly the supplied `ProofStep`.
    pub(in crate::surface::proof::proof_object) fn apply_step_with_origin(
        &self,
        step: ProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Proof<'a>, ClickError> {
        self.observe_step(step, false, |step| {
            self.apply_step_with_origin_inner(step, origin)
        })
    }

    /// The checked opening of a source intro block is explicit even when the
    /// rest of the block contains automation.
    pub(in crate::surface::proof) fn apply_scoped_intro_step(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        let written = !self.proof.site().is_generated();
        self.observe_step(step, written, |step| {
            self.apply_step_with_origin_inner(step, None)
        })
    }

    /// Retain diagnostics, tracing and synchronization for an already prepared
    /// operation without evaluating its inputs again.
    pub(in crate::surface::proof) fn observe_step(
        &self,
        step: ProofStep,
        written: bool,
        apply: impl FnOnce(ProofStep) -> Result<Proof<'a>, ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        let read_checkpoint = crate::surface::proof_trace::enabled_for(driver_proof.claim_label())
            .then(|| {
                driver_proof
                    .focused_branch()
                    .map(|branch| branch.state.facts.assumptions().read_equality_checkpoint())
            })
            .flatten();
        if let Some(execution) = driver_proof.execution() {
            execution
                .core
                .state
                .resources()
                .synchronize_memory_equalities(driver_proof.facts().assumptions());
        }
        let tactic = proof_step_source_name(&step);
        let call_source = crate::surface::proof_trace::enabled_for(driver_proof.claim_label())
            .then(|| driver_proof.trace_call_source(&step))
            .flatten();
        let chosen = (crate::surface::proof_trace::enabled_for(driver_proof.claim_label())
            && crate::surface::proof_trace::smart_origin().is_some())
        .then(|| chosen_step_text(&step))
        .flatten();
        // A trace observes the read-history queries already made by this
        // operation, including publication of a retained application.
        // A `have` is observed when its checked facts enter the enclosing scope.
        let audits_step = crate::surface::proof::raise_lower_audit::enabled()
            && !matches!(&step, ProofStep::Have { .. });
        let run = || apply(step);
        let (result, cell_walks) =
            if crate::surface::proof_trace::enabled_for(driver_proof.claim_label()) {
                crate::kernel::capture_step_cell_walks(TRACED_STEP_CELL_WALKS, run)
            } else {
                (run(), Vec::new())
            };
        let result = result.map_err(|error| {
            driver_proof
                .attach_step_diagnostic(error)
                .with_failed_tactic(tactic)
        });
        if let Ok(next) = &result
            && let Some(execution) = next.execution()
        {
            execution
                .core
                .state
                .resources()
                .synchronize_memory_equalities(next.facts().assumptions());
        }
        let result = result.and_then(|next| {
            // Fact admission or memory synchronization can consume the last
            // unit after the transport checker returned. Its checked delta
            // still carries the exact goal; do not report the outer C goal.
            if tactic == "transport"
                && let Err(error) = check_verification_deadline()
            {
                return Err(driver_proof.attach_transport_budget_diagnostic(error, &next));
            }
            Ok(next)
        });
        if let Ok(next) = &result
            && crate::surface::proof_trace::enabled_for(driver_proof.claim_label())
            && !Arc::ptr_eq(&driver_proof.node, &next.node)
        {
            driver_proof.record_checked_trace_step(
                next,
                tactic,
                call_source,
                chosen,
                8,
                read_checkpoint.as_ref(),
                cell_walks,
            );
        }
        if let Ok(next) = &result
            && crate::surface::proof::raise_lower_census::enabled()
            && !Arc::ptr_eq(&driver_proof.node, &next.node)
        {
            driver_proof.record_raise_lower_census(next, tactic, written);
        }
        if let Ok(next) = &result
            && audits_step
            && !Arc::ptr_eq(&driver_proof.node, &next.node)
        {
            driver_proof.record_raise_lower_audit(next, tactic);
        }
        result
    }

    fn apply_step_with_origin_inner(
        &self,
        step: ProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        #[cfg(test)]
        CHECKED_HAVE_OPERATIONS.with(|count| count.set(count.get() + 1));
        // Diagnostics from this step, and from every scope it opens, name the
        // source occurrence the driver is checking rather than a tree depth.
        // A generated tactic has no source occurrence (`usize::MAX`) and is
        // addressed by nothing, so there is no site to move to for it.
        if let Some(origin) = origin
            && origin.source_index != usize::MAX
            && !driver_proof
                .site()
                .addresses_source_tactic(origin.source_index)
        {
            return driver_proof
                .at_source_tactic(origin.source_index)
                .driver()
                .apply_step_with_origin(step, Some(origin));
        }
        if driver_proof.focused_discharged() {
            return Err(driver_proof.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                proof_step_source_name(&step)
            )));
        }

        // A witness for several binders instantiates them in the order
        // written and is recorded as the one step that was written.
        if let ProofStep::Witness(witness) = &step
            && !witness.is_single()
        {
            let mut current = driver_proof.clone();
            for single in witness.singles() {
                current = current
                    .driver()
                    .apply_step_with_origin_inner(ProofStep::Witness(single), None)?;
            }
            return Ok(Proof {
                site: driver_proof.site.clone(),
                context: driver_proof.context.clone(),
                state: current.state.clone(),
                node: ProofNode::step_child(
                    &driver_proof.node,
                    current.focused_branch_id(),
                    Arc::new(step),
                ),
            });
        }
        if let ProofStep::CloseInvariantsBy(body) = &step {
            return driver_proof.driver().apply_close_invariants_body(
                &body.to_proof_tactics(),
                None,
                false,
            );
        }
        if !super::execution_statements::implicit_solve_disabled()
            && matches!(
                &step,
                ProofStep::UnfoldProposition(_)
                    | ProofStep::UnfoldFunction(_)
                    | ProofStep::UnfoldResource(_)
                    | ProofStep::UnfoldWitnesses { .. }
            )
        {
            // The outer dispatcher records this accepted operation once.
            // Probes and retries must not re-enter its census/trace wrapper.
            return driver_proof
                .driver()
                .with_proved_lowering_requirements(&step, |proof| {
                    proof
                        .driver()
                        .apply_step_with_origin_inner(step.clone(), None)
                });
        }
        if let ProofStep::Have { proposition, proof } = &step {
            return driver_proof.driver().apply_have_step(proposition, proof);
        }
        // A certificate checked step by step, such as an obligation proof in
        // a `step` or `fold` `by` body, carries `both` as its checked arms.
        if matches!(step, ProofStep::Both { .. } | ProofStep::All(_)) {
            return driver_proof
                .driver()
                .apply_all_source(&step.to_proof_tactic(), false);
        }
        // A bare `fold` is checked as a bare step is: its fast path, then the
        // implicit `solve` for each body fact it leaves open.
        if matches!(step, ProofStep::FoldResource(_)) {
            return driver_proof.driver().apply_bare_statement_step(step);
        }
        if let ProofStep::StepProved { step: inner, proof } = &step {
            return match proof {
                StepProofCertificate::By(body) => {
                    driver_proof.driver().apply_step_with_obligation_proofs(
                        inner.as_ref().clone(),
                        None,
                        &mut |proof, proposition, _| {
                            proof.driver().apply_have_step(&proposition, body)
                        },
                    )
                }
                StepProofCertificate::Requires(certificates) => {
                    let entries = certificates
                        .iter()
                        .map(|entry| (entry.label.clone(), entry.proposition.clone()))
                        .collect::<Vec<_>>();
                    driver_proof.driver().apply_step_with_obligation_proofs(
                        inner.as_ref().clone(),
                        Some(&entries),
                        &mut |proof, proposition, index| {
                            let body = &certificates[index.expect("a `requires` entry")].proof;
                            proof.driver().apply_have_step(&proposition, body)
                        },
                    )
                }
            };
        }
        if let ProofStep::ApplyTheorem(application) = &step {
            return driver_proof
                .driver()
                .apply_prepared_theorem(application, false);
        }
        if let ProofStep::ApplyTheoremUsing { application, .. }
        | ProofStep::ApplyPlannedTheorem { application, .. } = &step
            && matches!(
                driver_proof.focused_obligation(),
                Some(Obligation::FunctionOutcome(_))
            )
        {
            let application = application.clone();
            return driver_proof
                .driver()
                .apply_theorem_at_returned_outcome(step, &application);
        }
        driver_proof
            .driver()
            .apply_step_without_outcome_wrapping(step)
    }

    /// Check a planner's selected step, then close its goal with the indexed closer.
    pub(in crate::surface::proof) fn apply_step_then_close(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        self.apply_step(step)?.driver().apply_step(ProofStep::Known)
    }

    /// Apply an ordinary derivation to its named target. Auxiliary transports
    /// use the same `have` scope as a written proof; no transport node remains.
    pub(in crate::surface::proof) fn apply_ordinary_transport_steps(
        &self,
        target: &SyntaxProposition,
        steps: Vec<ProofStep>,
    ) -> Result<Proof<'a>, ClickError> {
        if self.proof.surface_goal() == Some(target) {
            let mut current = self.proof.clone();
            for step in steps {
                if current.focused_discharged() && matches!(step, ProofStep::Known) {
                    continue;
                }
                current = current.driver().apply_step(step)?;
            }
            return Ok(current);
        }
        let certificate = ProofCertificate::from_steps(steps)
            .expect("ordinary transport steps form a certificate");
        self.apply_have_step(target, &certificate)
    }

    pub(in crate::surface::proof) fn apply_step_without_outcome_wrapping(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        if let ProofStep::ArithmeticUsing(premises) = &step {
            return crate::kernel::search::ProofSearch::apply_arithmetic_using(
                driver_proof,
                premises,
            );
        }
        driver_proof
            .driver()
            .apply_step_without_outcome_wrapping_after_wide(step)
    }

    pub(in crate::surface::proof) fn apply_step_without_outcome_wrapping_after_wide(
        &self,
        step: ProofStep,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        if matches!(
            &step,
            ProofStep::Step
                | ProofStep::StepBind(_)
                | ProofStep::StepContract(_)
                | ProofStep::StepCall(_)
        ) {
            return driver_proof.driver().apply_execution_statement_step(step);
        }
        if matches!(&step, ProofStep::UserTactic(_)) {
            return driver_proof.driver().apply_bare_statement_step(step);
        }

        // Expansion must retain the name chosen for an implicit binder. A cold
        // parse can then rename a newly desugared goal before referring to it.
        let step = if matches!(step, ProofStep::Intro)
            && matches!(driver_proof.goal(), Some(Proposition::ForAll { .. }))
        {
            match driver_proof.surface_goal() {
                Some(SyntaxProposition::ForAll { name, .. })
                | Some(SyntaxProposition::RangeAll { item: name, .. })
                    if matches!(name, SurfaceBinder::Generated(_)) =>
                {
                    ProofStep::IntroBinder(name.clone())
                }
                _ => step,
            }
        } else {
            step
        };
        let evidence_step = step.clone();
        let checked_proposition_successor = match &step {
            ProofStep::CheckTerminationLocal(function) => Some(
                driver_proof.apply_termination_check(crate::kernel::TerminationCheck::Local(
                    function.clone(),
                )),
            ),
            ProofStep::CheckTerminationComponent { function, strict } => Some(
                driver_proof.apply_termination_check(crate::kernel::TerminationCheck::Component {
                    function: function.clone(),
                    strict: *strict,
                }),
            ),
            ProofStep::CheckTerminationCallbacks => Some(
                driver_proof.apply_termination_check(crate::kernel::TerminationCheck::Callbacks),
            ),
            ProofStep::ApplyFact(fact) => Some(driver_proof.apply_fact_from_scope(fact)),
            ProofStep::ApplyFactUsing { fact, premises } => {
                Some(driver_proof.apply_fact_using(fact, premises))
            }
            ProofStep::Known => Some(driver_proof.apply_known()),
            ProofStep::CloseBounds(premises) => Some(driver_proof.apply_close_bounds(premises)),
            ProofStep::ArithmeticUsing(_) => {
                return Err(driver_proof
                    .step_error("arithmetic search must expand into ordinary proof steps"));
            }
            ProofStep::Preserve(separation) => Some(driver_proof.apply_preserve(separation)),

            ProofStep::Intro => Some(driver_proof.apply_intro(None)),
            ProofStep::IntroAs(name) => Some(driver_proof.apply_intro(Some(name.into()))),
            ProofStep::IntroBinder(name) => Some(driver_proof.apply_intro(Some(name.clone()))),
            ProofStep::Enumerate => Some(driver_proof.apply_enumerate()),
            ProofStep::CloseUnreachable => Some(driver_proof.apply_close_unreachable()),
            ProofStep::Instantiate {
                quantified,
                arguments,
            } => Some(driver_proof.apply_fixed_state_instantiate(quantified, arguments)),
            ProofStep::Mark(name) => Some(driver_proof.apply_execution_mark(name)),
            _ => None,
        };
        if let Some(successor) = checked_proposition_successor {
            let successor = successor?;
            let successor = if matches!(step, ProofStep::Instantiate { .. }) {
                close_goal_from_added_fact(successor)
            } else {
                successor
            };
            return Ok(Proof {
                site: driver_proof.site.clone(),
                context: driver_proof.context.clone(),
                state: successor,
                node: ProofNode::step_child(
                    &driver_proof.node,
                    driver_proof.focused_branch_id(),
                    Arc::new(evidence_step),
                ),
            });
        }

        let mut transition = match &step {
            ProofStep::Induct {
                parameter,
                hypothesis,
            } => driver_proof.apply_induct(parameter, hypothesis),
            ProofStep::ApplyInduction {
                hypothesis,
                arguments,
            } => driver_proof.apply_induction(hypothesis, arguments),
            ProofStep::ApplyTheoremUsing {
                application,
                premises,
            }
            | ProofStep::ApplyPlannedTheorem {
                application,
                premises,
            } => driver_proof.apply_theorem_using(application, premises),
            ProofStep::UnfoldProposition(target) => {
                driver_proof.apply_local_predicate_unfold(target)
            }
            ProofStep::UnfoldFunction(application) => {
                driver_proof.apply_function_unfold(application)
            }
            ProofStep::UnfoldResource(resource) => {
                // Resolve proof bindings before either the execution or
                // outcome path interprets ordinary resource arguments.
                let source_resource = resource;
                let resource = &driver_proof.resolve_proof_resource_arguments(resource)?;
                if driver_proof.focused_outcome_data().is_some() {
                    driver_proof.apply_outcome_resource_unfold(resource, source_resource)
                } else {
                    driver_proof.apply_execution_resource_unfold(resource, source_resource)
                }
            }
            ProofStep::UnfoldWitnesses { resource, names } => {
                let resource = &driver_proof.resolve_proof_resource_arguments(resource)?;
                driver_proof.apply_execution_resource_unfold_naming_witnesses(resource, names)
            }
            ProofStep::ReleaseView(resource) => {
                let resource = driver_proof.resolve_proof_resource_arguments(resource)?;
                driver_proof.apply_release_view(&resource)
            }
            ProofStep::FoldResource(_) => {
                unreachable!("fold was routed through obligation generation")
            }
            ProofStep::ObserveResource(resource) => {
                driver_proof.apply_execution_resource_observation(resource)
            }
            ProofStep::ObserveSubject(resource) => {
                driver_proof.apply_resource_subject_observation(resource)
            }
            ProofStep::Iterated(tactic) => driver_proof.apply_execution_iterated_step(tactic),
            ProofStep::Choose(choice) => driver_proof.apply_fixed_state_choose(choice),
            ProofStep::LetSatisfy(binding) => driver_proof.apply_let_satisfy(binding),
            ProofStep::Witness(witness) => driver_proof.apply_fixed_state_witness(witness),
            ProofStep::Rewrite(equality) => driver_proof.apply_rewrite(equality),
            _ => Err(driver_proof
                .step_error("this proof step has not yet migrated to the checked `Proof` API")),
        }?;

        // A rewrite changes the cited proposition's state
        // context. Do not let a source-epoch projection survive that
        // boundary and accidentally make a later citation look current.
        if matches!(step, ProofStep::Rewrite(_)) {
            transition.clear_existential_projection();
        }

        let step = match step {
            ProofStep::ApplyPlannedTheorem { application, .. }
                if driver_proof
                    .planned_theorem_replays_bare(&application, &transition.checked_facts) =>
            {
                ProofStep::ApplyTheorem(application)
            }
            ProofStep::ApplyTheoremUsing { application, .. }
                if driver_proof.site().is_generated()
                    && driver_proof
                        .planned_theorem_replays_bare(&application, &transition.checked_facts) =>
            {
                ProofStep::ApplyTheorem(application)
            }
            step => step,
        };
        let state = driver_proof.publish_checked_transition(transition)?;
        let state = if matches!(step, ProofStep::LetSatisfy(_)) {
            close_goal_from_added_fact(state)
        } else {
            state
        };
        let application = match &step {
            ProofStep::ApplyTheorem(application)
            | ProofStep::ApplyTheoremUsing { application, .. }
            | ProofStep::ApplyPlannedTheorem { application, .. } => Some(application.clone()),
            _ => None,
        };
        let applied = Proof {
            site: driver_proof.site.clone(),
            context: driver_proof.context.clone(),
            state,
            node: ProofNode::step_child(
                &driver_proof.node,
                driver_proof.focused_branch_id(),
                Arc::new(step),
            ),
        };
        Ok(match application {
            Some(application) => driver_proof
                .driver()
                .spell_applied_conclusions(&application, applied),
            None => applied,
        })
    }

    pub(in crate::surface::proof) fn apply_step_at(
        &self,
        step: ProofStep,
        source_index: usize,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .apply_step_with_origin(step, Some(ProofStepOrigin { source_index }))
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Checks a theorem application at a returned function outcome.
    ///
    /// Steps after a C return are checked against that return, and a later
    /// return fold accepts only facts the returning path justifies: the
    /// path's own facts and each checked return proposition (a `have` closed
    /// at the outcome, recorded with the facts it was proved under). An
    /// application's conclusion is such a checked fact, so it is recorded the
    /// same way: each spelled conclusion `C` is first proved as
    /// `have C by { <this application>; close(); }` from the facts before the
    /// application. That `have` is the ordinary checked scope, and return
    /// certification checks its completion as it checks a written one: the
    /// facts it was proved under must be justified on the returning path.
    /// This therefore grants nothing a written proof could not. The
    /// application is then checked once more as an ordinary step, publishing
    /// any applied fact no conclusion spells; such a fact has no return
    /// proposition and a later fold relying on it is still refused. A
    /// conclusion whose `have` does not close is left to that ordinary step.
    /// The proof node is the one written application, so an expansion writes
    /// the `apply` alone.
    pub(in crate::surface::proof) fn apply_theorem_at_returned_outcome(
        &self,
        step: ProofStep,
        application: &TheoremApplication,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        let body = ProofCertificate::from_validated_steps(vec![step.clone(), ProofStep::Known]);
        let mut current = driver_proof.clone();
        for conclusion in driver_proof.theorem_application_surface_conclusions(application) {
            check_verification_deadline()?;
            if current
                .lower_surface_proposition(&conclusion, "`apply` conclusion")
                .is_ok_and(|lowered| current.facts().contains(&lowered))
            {
                continue;
            }
            match current.driver().apply_have_step(&conclusion, &body) {
                Ok(next) => current = next,
                Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
                Err(_) => {}
            }
        }
        let applied = current
            .driver()
            .apply_step_without_outcome_wrapping(step.clone())?;
        let branch = applied.focused_branch_id();
        Ok(Proof {
            site: driver_proof.site.clone(),
            context: driver_proof.context.clone(),
            state: applied.state,
            node: ProofNode::step_child(
                &driver_proof.node,
                branch,
                applied.node.step.clone().unwrap_or_else(|| Arc::new(step)),
            ),
        })
    }

    /// A theorem application publishes its conclusions as kernel facts.
    /// Spell each conclusion the way the caller would write it
    /// and record it as a checked `have` closed by `known`, which finds
    /// the fact the application just added. The `apply` keeps its own proof
    /// node: the spelling is an index entry for later premise lookups, not a
    /// step of the proof, and an expansion writes the `apply` alone. A
    /// conclusion that does not spell, or whose spelling does not lower to an
    /// available fact, is left unspelled.
    pub(in crate::surface::proof) fn spell_applied_conclusions(
        &self,
        application: &TheoremApplication,
        applied: Proof<'a>,
    ) -> Proof<'a> {
        let driver_proof = self.proof;
        if applied.is_complete() || applied.focused_discharged() {
            return applied;
        }
        // An applied fact that is the goal under another spelling of the
        // same order claim (`0 <= e` for `e >= 0`) is closed next from the
        // facts this step checked; a spelling step here would hide them.
        if applied.goal().is_some_and(|goal| {
            applied.checked_facts().iter().any(|fact| {
                crate::kernel::proof::fact_reasoning::order_claim_equivalent(fact, goal)
            })
        }) {
            return applied;
        }
        let conclusions = driver_proof.theorem_application_surface_conclusions(application);
        let node = applied.node.clone();
        let mut spelled = applied;
        for conclusion in conclusions {
            let Ok(next) = spelled.driver().apply_step(ProofStep::Have {
                proposition: conclusion,
                proof: Box::new(ProofCertificate::from_validated_steps(vec![
                    ProofStep::Known,
                ])),
            }) else {
                continue;
            };
            spelled = Proof {
                node: node.clone(),
                ..next
            };
        }
        spelled
    }

    /// Applies one explicit `Have` through the same owned scope operations as
    /// a source `have` block. Each body step advances the scope's persistent
    /// child `Proof`; joining publishes only the checked proposition and
    /// retains the body's exact surface operations as evidence. A failed
    /// body leaves this immutable root untouched.
    pub(in crate::surface::proof) fn apply_have_step(
        &self,
        proposition: &SyntaxProposition,
        proof: &ProofCertificate,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        let mut scope = driver_proof
            .driver()
            .open_have_as_written(proposition.clone())?;
        for step in proof.steps() {
            scope = scope.driver().apply_step(step.clone())?;
        }
        scope.join()
    }
}

/// How many read-history walks a traced step captures for its trace.
const TRACED_STEP_CELL_WALKS: usize = 16;
