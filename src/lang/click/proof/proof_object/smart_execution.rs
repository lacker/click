//! Smart execute-until search, fact transport, and theorem selection.

use super::*;

impl<'a> Proof<'a> {
    /// Searches a straight-line prefix up to one named statement by applying
    /// every selected `StepUsing` to the current checked descendant. The
    /// returned fact list is only the prefix's output delta; scope adapters
    /// use it to retain facts introduced inside their owned representation.
    pub(super) fn try_linear_execute_until_descendant(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        let target = self.resolve_statement_target(region)?;
        let Some(current) = self.current_statement_index()? else {
            return Err(self.step_error(format!(
                "`execute_until(statement({target}))` cannot run after execution already reached function exit"
            )));
        };
        if target < current {
            return Err(self.step_error(format!(
                "`execute_until(statement({target}))` cannot move backward from statement({current})"
            )));
        }

        let mut proof = self.clone();
        let mut introduced_facts = Vec::new();
        let mut advanced = false;
        loop {
            match proof.current_statement_index()? {
                Some(current) if current == target => break,
                Some(current) if current < target => {}
                Some(_) | None => return Ok(None),
            }
            // The first statement must be independent of unrelated facts in
            // the inherited root context. After it advances, the descendant
            // owns an explicit output-sized `added_facts` delta; the checked
            // execute selector carries only that delta through later steps.
            let next = if advanced {
                proof.try_indexed_execute_step()?
            } else {
                proof.try_indexed_statement_step()?
            };
            let Some(next) = next else {
                return Ok(None);
            };
            for fact in next.added_facts() {
                if !introduced_facts.contains(fact) {
                    introduced_facts.push(fact.clone());
                }
            }
            proof = next;
            advanced = true;
        }
        Ok(advanced.then_some((proof, introduced_facts)))
    }

    /// Runs the narrow checked `execute_until` search on this Proof and
    /// returns only the already-accepted descendant.
    pub(in crate::lang::click::proof) fn try_linear_execute_until(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<Self>, ClickError> {
        Ok(self
            .try_linear_execute_until_descendant(region)?
            .map(|(proof, _)| proof))
    }

    /// Runs the narrow linear `execute` search over checked descendants.
    /// Straight-line statements and audited terminal C branches advance only
    /// through their Proof operations; a partial path is discarded unless it
    /// reaches function exit.
    pub(super) fn try_linear_execute_descendant(
        &self,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        let mut proof = self.clone();
        let mut introduced_facts = Vec::new();
        let mut advanced = false;
        while !proof.is_at_function_exit() {
            let next = if let Some(next) = proof.try_indexed_execute_step()? {
                next
            } else {
                if !proof.is_at_execution_branch()? {
                    return Ok(None);
                }
                let Some(next) = proof.try_focused_execute_to_exit()? else {
                    return Ok(None);
                };
                next
            };
            for fact in next.added_facts() {
                if !introduced_facts.contains(fact) {
                    introduced_facts.push(fact.clone());
                }
            }
            proof = next;
            advanced = true;
        }
        if !advanced {
            return Ok(None);
        }
        Ok(Some((proof, introduced_facts)))
    }

    /// Returns the already-checked function-exit descendant selected by the
    /// narrow linear `execute` search.
    pub(in crate::lang::click::proof) fn try_linear_execute(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        Ok(self
            .try_linear_execute_descendant()?
            .map(|(proof, _)| proof))
    }

    /// Searches explicit premise forms for one point fact transport.
    ///
    /// Every candidate is checked by applying the corresponding simple step
    /// to this immutable root. Failed descendants are discarded; the
    /// returned `Proof` is the already-checked, deletion-minimized success,
    /// so callers never reconstruct or replay the selected certificate.
    pub(in crate::lang::click::proof) fn search_point_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
    ) -> Result<Self, ClickError> {
        let result_aware = matches!(self.context.as_ref(), ProofContext::Point(_))
            || self.focused_outcome_point().is_some();
        if !result_aware {
            return Err(self.step_error(
                "fact-transport search requires a point proof or a focused outcome goal",
            ));
        }
        self.search_fact_transport_from_candidates(
            source,
            target,
            candidates,
            "post-execution fact transport",
        )
    }

    /// Tries the bounded source-local form of mid-execution fact transport on
    /// this immutable execution Proof. The smart operation checks the empty
    /// candidate and the source's own explicit form; it never scans the
    /// ambient fact set. Richer premise discovery remains on the legacy path
    /// until it has a relevance index rather than an environment-wide scan.
    pub(in crate::lang::click::proof) fn try_execution_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(_) = self.context.as_ref() else {
            return Err(
                self.step_error("execution fact-transport search requires an execution proof")
            );
        };
        let execution = self.execution().ok_or_else(|| {
            self.step_error("execution fact-transport search lost its semantic frontier")
        })?;
        if execution.replay.is_at_function_entry() {
            return Err(self.step_error(
                "`transport` requires a current statement frontier after at least one execution step",
            ));
        }
        if execution.replay.is_at_function_exit() {
            return Ok(None);
        }
        match self.search_fact_transport_from_candidates(
            source,
            target,
            std::iter::once(source.clone()),
            "execution-frontier fact transport",
        ) {
            Ok(proof) => Ok(Some(proof)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    pub(super) fn search_fact_transport_from_candidates(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
        description: &str,
    ) -> Result<Self, ClickError> {
        let apply = |premises: Vec<ClickProposition>| {
            self.apply_step(SimpleProofStep::TransportUsing {
                source: source.clone(),
                target: target.clone(),
                premises,
            })
        };
        let mut selected = Vec::new();
        let mut last_error = None;
        let mut selected_proof = match apply(Vec::new()) {
            Ok(proof) => Some(proof),
            Err(error) => {
                last_error = Some(error);
                check_verification_deadline()?;
                None
            }
        };
        if selected_proof.is_none() {
            for candidate in candidates {
                check_verification_deadline()?;
                if selected.contains(&candidate) {
                    continue;
                }
                selected.push(candidate);
                match apply(selected.clone()) {
                    Ok(proof) => {
                        selected_proof = Some(proof);
                        break;
                    }
                    Err(error) => {
                        last_error = Some(error);
                        check_verification_deadline()?;
                    }
                }
            }
        }
        let Some(mut selected_proof) = selected_proof else {
            return Err(self.step_error(format!(
                "{description} has no explicit surface-premise certificate: {}",
                last_error
                    .as_ref()
                    .map(|error| error.message())
                    .unwrap_or("no candidate was checked")
            )));
        };
        let mut index = 0;
        while index < selected.len() {
            check_verification_deadline()?;
            let mut reduced = selected.clone();
            reduced.remove(index);
            match apply(reduced.clone()) {
                Ok(proof) => {
                    selected = reduced;
                    selected_proof = proof;
                }
                Err(_) => {
                    check_verification_deadline()?;
                    index += 1;
                }
            }
        }
        Ok(selected_proof)
    }

    /// Untrusted smart-tactic query for one explicit theorem-application
    /// candidate on a point proof.
    ///
    /// Requirement selection probes the current persistent fact indexes. It
    /// returns only a `SimpleProofStep`; theorem conclusions and provenance
    /// are created later, if and only if the caller submits that step to
    /// `apply_step` on this same proof.
    pub(in crate::lang::click::proof) fn select_point_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<SimpleProofStep, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("point theorem-application search requires a point proof"));
        };
        self.select_theorem_application_step_at_point(
            application,
            context.parameters,
            context.arguments,
            context.pre_state,
            context.state,
            context.result,
            context.program_point_states,
            context.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.theorem_environment,
        )
    }

    /// Untrusted smart-tactic query for one explicit theorem step at the
    /// current execution frontier. The query can inspect the immutable proof
    /// and return syntax, but only `apply_step` can add the conclusion or
    /// advance provenance.
    pub(in crate::lang::click::proof) fn select_execution_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<SimpleProofStep, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "execution theorem-application search requires an execution-frontier proof",
            ));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let pre_state = execution.replay.old_reference_state(&execution.state);
        self.select_theorem_application_step_at_point(
            application,
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            &execution.state,
            None,
            &execution.replay.program_point_states,
            &execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.theorem_environment,
        )
    }

    /// Tries one bare theorem application against this immutable Proof.
    ///
    /// Selection is context-specific, but every context returns the same
    /// explicit `ApplyTheoremUsing` candidate and submits it to `apply_step`
    /// on this exact root. A selection miss is transactional; once selection
    /// succeeds, rejection by the checker is a loud implementation error
    /// rather than permission to retry through a second semantic path.
    pub(in crate::lang::click::proof) fn try_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<Self>, ClickError> {
        let selected = self.select_theorem_application_step(application);
        let step = match selected {
            Ok(Some(step)) => step,
            Ok(None) => return Ok(None),
            Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
            Err(_) => return Ok(None),
        };
        self.apply_selected_theorem_application(step).map(Some)
    }

    /// Applies one bare theorem application without treating an unavailable
    /// candidate as a smart-search miss. Source adapters that have already
    /// committed to `apply(...)` use this strict form and retain the original
    /// selector diagnostic, while still sharing the sole checked transition.
    pub(in crate::lang::click::proof) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Self, ClickError> {
        let Some(step) = self.select_theorem_application_step(application)? else {
            return Err(self.step_error(
                "theorem application requires a result-sensitive point proof after function exit",
            ));
        };
        self.apply_selected_theorem_application(step)
    }

    pub(super) fn select_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<SimpleProofStep>, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.select_pure_theorem_application_step(application),
            ProofContext::Point(_) => self.select_point_theorem_application_step(application),
            // A focused function-outcome goal is one result-sensitive point
            // context: selection reads the goal-aware view directly.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view_with_effects(OutcomeEffectContext::Replay)
                    .expect("a focused outcome judgment resolves its point view");
                self.select_theorem_application_step_at_point(
                    application,
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.program_point_states,
                    view.surface_propositions,
                    view.predicate_environment,
                    view.click_function_environment,
                    view.theorem_environment,
                )
            }
            ProofContext::Execution(_) if !self.is_at_function_exit() => {
                self.select_execution_theorem_application_step(application)
            }
            // A function-exit execution Proof not focused on one outcome
            // still owns several result-sensitive point contexts; ordered
            // finalization keeps that seam until its paths derive goals.
            ProofContext::Execution(_) => return Ok(None),
        }
        .map(Some)
    }

    pub(super) fn apply_selected_theorem_application(
        &self,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step(step).map_err(|error| {
            self.step_error(format!(
                "theorem search selected a simple candidate that Proof rejected: {}",
                error.message()
            ))
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn select_theorem_application_step_at_point(
        &self,
        application: &TheoremApplication,
        parameters: &[syntax::C0Parameter],
        arguments: &[CExpression],
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
        program_point_states: &ProgramPointStates,
        surface_propositions: &SurfacePropositionMap,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        theorem_environment: &TheoremEnvironment,
    ) -> Result<SimpleProofStep, ClickError> {
        let values = parameter_values(parameters, arguments).map_err(|error| {
            self.step_error(format!(
                "could not bind theorem arguments: {}",
                error.message
            ))
        })?;
        let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
        let application_context = TheoremApplicationContext {
            values: &values,
            array_refs: &array_refs,
            pre_state,
            post_state: state,
            result,
            program_point_states,
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let mut lowering_assumptions = self.facts().assumptions().clone();
        for fact in state
            .resources()
            .observable_facts_assuming_valid(self.facts().assumptions())
        {
            lowering_assumptions = lowering_assumptions.assume_proposition(fact);
        }
        let requirements = lower_theorem_application_requirements_with_assumptions(
            theorem_environment,
            application,
            &application_context,
            &lowering_assumptions,
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower theorem requirements: {message}"))
        })?;

        let mut premises = Vec::new();
        for requirement in requirements {
            if matches!(normalize_proposition(&requirement), SimpProposition::True) {
                continue;
            }
            let matched = self                .facts()                .matching_replay_fact_across_effects(&requirement, &[])
                .ok_or_else(|| {
                    self.step_error(format!(
                        "theorem application `{}` requires an unavailable exact premise: {requirement:?}",
                        application.name
                    ))
                })?;

            // Reuse the established snapshot-surface search for execution
            // proofs, with availability answered by persistent indexes. The
            // canonical fact above comes from the requirement's shape bucket,
            // so sibling snapshot terms remain visible without rebuilding
            // the complete ambient fact vector. The returned form still
            // has to survive `apply_step` below.
            let mut snapshot_surface_error = None;
            if let ProofContext::Execution(_) = self.context.as_ref() {
                let execution = self
                    .execution()
                    .expect("execution proof owns semantic state");
                match checked_surface_comparison_fact_at_point_with_indexed_facts(
                    &execution.replay,
                    &matched,
                    SurfaceFactMatch::CanonicalExact,
                    &self.facts(),
                    &lowering_assumptions,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                ) {
                    Ok(surface) => {
                        if !premises.contains(&surface) {
                            premises.push(surface);
                        }
                        continue;
                    }
                    Err(error) => snapshot_surface_error = Some(error),
                }
            }

            let mut candidates = surface_propositions
                .surfaces(&matched)
                .chain(surface_propositions.surfaces(&requirement))
                .cloned()
                .collect::<Vec<_>>();
            if let Some(candidate) =
                synthesize_surface_proposition(&matched, parameters, arguments, state)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            if let Some(candidate) =
                synthesize_surface_proposition(&requirement, parameters, arguments, state)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            if candidates.is_empty() {
                return Err(self.step_error(format!(
                    "theorem application `{}` has no checked surface form for exact premise `{requirement:?}`",
                    application.name
                )));
            }
            let surface = candidates
                .into_iter()
                // SurfacePropositionMap treats the most recently recorded
                // form as canonical. Prefer it here too; earlier entries
                // can be mechanically valid but over-anchor constants as
                // `at(point, constant)` and produce needlessly unstable
                // certificates.
                .rev()
                .find(|candidate| {
                    let matches_requirement = |lowered: &Proposition| {
                        (lowered.clone()
                            == requirement.clone()
                            || condition_polarity_equivalent(lowered, &requirement))
                            && self                                .facts()                                .replay_available_across_effects(lowered, &[])
                    };
                    let direct = lower_point_proposition_with_assumptions(
                        candidate,
                        &lowering_assumptions,
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        result,
                        program_point_states,
                        predicate_environment,
                        click_function_environment,
                    );
                    direct.as_ref().is_ok_and(matches_requirement)
                })
                .ok_or_else(|| {
                    self.step_error(format!(
                        "theorem application `{}` has no checked surface form for exact premise `{requirement:?}`{}",
                        application.name,
                        snapshot_surface_error
                            .as_ref()
                            .map(|error| format!(": {}", error.message()))
                            .unwrap_or_default(),
                    ))
                })?;
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }

        Ok(SimpleProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises,
        })
    }

    /// Untrusted pure smart-tactic query for one explicit theorem step.
    /// This instantiates the applied theorem's own requirement forms and
    /// probes their lowered forms through the current persistent fact index;
    /// it cannot advance the proof or add the theorem's conclusion.
    pub(in crate::lang::click::proof) fn select_pure_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<SimpleProofStep, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(
                self.step_error("pure theorem-application search requires a proposition goal")
            );
        };
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let program_point_states = ProgramPointStates::new();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            pre_state: &state,
            post_state: &state,
            result: None,
            program_point_states: &program_point_states,
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let requirements = lower_theorem_application_requirements_with_assumptions(
            context.theorem_environment,
            application,
            &application_context,
            self.facts().assumptions(),
            context.predicate_environment,
            context.click_function_environment,
            &unfolded_predicates,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower theorem requirements: {message}"))
        })?;
        let theorem = context
            .theorem_environment
            .get(&application.name)
            .ok_or_else(|| self.step_error(format!("unknown theorem `{}`", application.name)))?;
        let substitutions = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .map(str::to_string)
            .zip(application.arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();

        let mut premises = Vec::new();
        for (requirement, source_requirement) in requirements.into_iter().zip(theorem.requires()) {
            if normalizes_context_free(&requirement) {
                continue;
            }
            let source_surface = source_requirement.proposition().ok_or_else(|| {
                self.step_error(format!(
                    "theorem application `{}` has a non-proposition requirement",
                    application.name
                ))
            })?;
            let surface = substitute_click_proposition(source_surface, &substitutions)
                .map_err(|message| self.step_error(message))?;
            let lowered = self.lower_surface_proposition(&surface, "selected theorem premise")?;
            if lowered.clone() != requirement.clone() || !self.facts().contains(&lowered) {
                return Err(self.step_error(format!(
                    "required exact fact for theorem `{}` is unavailable: {requirement:?}",
                    application.name
                )));
            }
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }
        Ok(SimpleProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises,
        })
    }
}
