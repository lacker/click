//! Smart execute-until search, fact transport, and theorem selection.

use super::*;
use std::collections::BTreeSet;

impl<'a> Proof<'a> {
    /// Runs `execute_until` on checked descendants: the `execute()` search
    /// with a target, which stops before that source statement and follows
    /// one path, refusing where it would have to split. The returned fact
    /// list is only the prefix's output delta; scope adapters use it to
    /// retain facts introduced inside their owned representation.
    pub(super) fn try_execute_until_descendant(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        if *region == CodeRegionRef::BackEdge {
            return self.try_execute_to_back_edge_descendant();
        }
        let target = self.resolve_statement_target(region)?;
        let Some(current) = self.current_statement_index()? else {
            return Err(self.step_error(format!(
                "`execute_until({})` cannot run after execution already reached function exit",
                describe_code_region_ref(region)
            )));
        };
        if target < current {
            return Err(self.step_error(format!(
                "`execute_until({})` cannot move backward from statement({current})",
                describe_code_region_ref(region)
            )));
        }
        if target == current {
            // Reaching the requested frontier is success, including inside
            // a proof branch or resource scope. `None` means unsupported to
            // those drivers and incorrectly declines a valid no-op.
            return Ok(Some((self.clone(), Vec::new())));
        }
        let mut introduced_facts = Vec::new();
        let Some(proof) = self.try_focused_execute_to_exit_within(
            Vec::new(),
            &mut BTreeSet::new(),
            &mut 0,
            Some(&mut introduced_facts),
            Some(target),
        )?
        else {
            return Ok(None);
        };
        Ok(Some((proof, introduced_facts)))
    }

    /// Finish only the current preservation region. Every advance is an
    /// ordinary checked step; reaching the boundary grants no invariant or
    /// termination authority. Refuse branch splits and non-back-edge exits.
    fn try_execute_to_back_edge_descendant(
        &self,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        let frontier = &self
            .execution()
            .ok_or_else(|| self.step_error("`back_edge()` requires a loop preservation frontier"))?
            .core
            .frontier;
        if !frontier.in_loop_body
            || frontier.region != crate::kernel::proof::ExecutionRegionKind::LoopBody
        {
            return Err(self.step_error("`back_edge()` requires the current loop preservation region; it cannot select a branch arm boundary"));
        }
        if frontier.is_at_region_boundary() && !frontier.loop_control.is_exit() {
            return Ok(None);
        }
        let mut proof = self.clone();
        let mut facts = Vec::new();
        let mut retried = BTreeSet::new();
        let mut steps = 0;
        loop {
            let frontier = &proof
                .execution()
                .ok_or_else(|| proof.step_error("execution proof lost its semantic frontier"))?
                .core
                .frontier;
            if frontier.region != crate::kernel::proof::ExecutionRegionKind::LoopBody {
                return Err(proof.step_error("`back_edge()` cannot finish a nested branch or loop region; prove that region separately"));
            }
            if frontier.is_at_region_boundary() {
                if frontier.loop_control.is_exit() {
                    return Err(proof
                        .step_error("`back_edge()` reached a loop exit instead of the back edge"));
                }
                return Ok(Some((proof, facts)));
            }
            if frontier.is_at_function_exit() {
                return Err(proof
                    .step_error("`back_edge()` reached function exit instead of the back edge"));
            }
            proof.charge_execute_step(&mut steps)?;
            if let Some(next) = proof.try_smart_statement_step(ProofStep::Step, &mut retried)? {
                facts.extend(next.added_facts().iter().cloned());
                proof = next;
                retried.clear();
            } else {
                return match proof.apply_step(ProofStep::Step) {
                    Err(error) => Err(error),
                    Ok(_) => Err(proof
                        .step_error("`back_edge()` found no checked advance from this frontier")),
                };
            }
        }
    }

    /// Runs `execute_until` on this Proof and returns only the
    /// already-accepted descendant.
    pub(in crate::surface::proof) fn try_execute_until(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<Self>, ClickError> {
        Ok(self
            .try_execute_until_descendant(region)?
            .map(|(proof, _)| proof))
    }

    /// Runs `execute()` to function exit on checked descendants: one
    /// statement step at a time, splitting at C branches, call outcomes, and
    /// path cases. A partial path is discarded unless it reaches function
    /// exit. The returned fact list is the top-level advances' output delta.
    pub(super) fn try_execute_to_exit_descendant(
        &self,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        if self.is_at_function_exit() {
            return Ok(None);
        }
        // The statement steps below run on behalf of `execute()`, and a
        // refusal names it; the returned descendant carries this proof's own
        // context again, so checkpoints taken before it still apply.
        let proof = self.with_execution_step_tactic_name("execute()");
        // Retrying a refused statement is bounded by the owning smart
        // operation: one retained-have attempt per distinct requirement
        // identity. The set follows this immutable search, rather than a
        // process-global cache, so unrelated proofs cannot affect it.
        let mut retried_requirements = BTreeSet::new();
        let mut introduced_facts = Vec::new();
        let Some(proof) = proof.try_focused_execute_to_exit_within(
            Vec::new(),
            &mut retried_requirements,
            &mut 0,
            Some(&mut introduced_facts),
            None,
        )?
        else {
            return Ok(None);
        };
        Ok(Some((proof.with_context_of(self), introduced_facts)))
    }

    /// Returns the already-checked function-exit descendant selected by the
    /// `execute()` search.
    pub(in crate::surface::proof) fn try_execute_to_exit(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        Ok(self
            .try_execute_to_exit_descendant()?
            .map(|(proof, _)| proof))
    }

    /// Searches explicit premise forms for one fixed-state fact transport.
    ///
    /// Every candidate is checked by applying the corresponding proof step
    /// to this immutable root. Failed descendants are discarded; the
    /// returned `Proof` is the already-checked, deletion-minimized success,
    /// so callers never reconstruct or check the selected certificate.
    pub(in crate::surface::proof) fn search_fixed_state_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
    ) -> Result<Self, ClickError> {
        let result_aware = matches!(self.context.as_ref(), ProofContext::FixedState(_))
            || self.focused_outcome_data().is_some()
            || self.execution_proposition_fixed_state_view().is_some();
        if !result_aware {
            return Err(self.step_error(
                "fact-transport search requires a fixed-state proof, focused outcome goal, or execution proposition scope",
            ));
        }
        self.search_fact_transport_from_candidates(
            source,
            target,
            candidates,
            "post-execution fact transport",
        )
    }

    /// Plans one explicit transport for a proposition scope borrowing an
    /// execution frontier. This is the same checked premise planner used by
    /// source-level `transport`; the returned descendant records the ordinary
    /// `TransportUsing` step, so smart structural closures do not rely on an
    /// implicit frame decision.
    pub(super) fn try_planned_execution_proposition_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        if self.execution_proposition_fixed_state_view().is_none() {
            return Ok(None);
        }
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        let source_kernel = self.lower_surface_proposition_direct(
            source,
            "smart execution-proposition transport source",
        )?;
        let target_kernel = self.lower_surface_proposition_direct(
            target,
            "smart execution-proposition transport target",
        )?;
        let transition_facts = super::cursor_execution::fact_transport_transition_facts(
            &execution.core.effect_facts,
            &source_kernel,
        );
        // Introduced binders belong to this proposition scope, rather than
        // the outer execution frontier. Their existing lexical names let
        // the planner spell selected guards in the generated `using` list;
        // the ordinary transport checker still lowers and checks each one.
        let mut view = execution.view(context);
        view.proof_bindings = self
            .proposition_obligation()
            .map(|goal| &goal.surface_bindings);
        let premises = match plan_explicit_fact_transport(
            source,
            &source_kernel,
            &target_kernel,
            &self.facts().to_vec(),
            &transition_facts,
            context.parameter_binding(),
            view,
            &execution.core.state,
            context.spec_definitions,
        ) {
            Ok(premises) => premises,
            Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
            Err(_) => return Ok(None),
        };
        match self.apply_step(ProofStep::TransportUsing {
            source: source.clone(),
            target: target.clone(),
            premises,
        }) {
            Ok(proof) => Ok(Some(proof)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    /// Tries the bounded source-local form of mid-execution fact transport on
    /// this immutable execution Proof. The smart operation checks the empty
    /// candidate and the source's own explicit form; it never scans the
    /// ambient fact set. Richer premise discovery remains unavailable until
    /// it has a relevance index rather than an environment-wide scan.
    pub(in crate::surface::proof) fn try_execution_fact_transport(
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
        if execution.core.frontier.is_at_function_entry() {
            return Err(self.step_error(
                "`transport` requires a current statement frontier after at least one execution step",
            ));
        }
        if execution.core.frontier.is_at_function_exit() {
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
            self.apply_step(ProofStep::TransportUsing {
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
                    .map(|error| error.raw_summary())
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
    /// candidate on a fixed-state proof.
    ///
    /// Requirement selection probes the current persistent fact indexes. It
    /// returns only a `ProofStep`; theorem conclusions and provenance
    /// are created later, if and only if the caller submits that step to
    /// `apply_step` on this same proof.
    pub(in crate::surface::proof) fn select_fixed_state_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<ProofStep, ClickError> {
        let ProofContext::FixedState(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "fixed-state theorem-application search requires a fixed-state proof",
            ));
        };
        self.select_theorem_application_step_in_fixed_state(
            application,
            context.parameter_binding,
            context.fixed_state,
            context.surface_propositions,
            context.spec_definitions,
            context.theorem_environment,
        )
    }

    /// Untrusted smart-tactic query for one explicit theorem step at the
    /// current execution frontier. The query can inspect the immutable proof
    /// and return syntax, but only `apply_step` can add the conclusion or
    /// advance provenance.
    pub(in crate::surface::proof) fn select_execution_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<ProofStep, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "execution theorem-application search requires an execution-frontier proof",
            ));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let pre_state =
            context.old_reference_state(&execution.core.frontier, &execution.core.state);
        self.select_theorem_application_step_in_fixed_state(
            application,
            context.parameter_binding(),
            FixedStateFrame::new(
                pre_state,
                &execution.core.state,
                None,
                &execution.presentation.recorded_snapshots,
            ),
            &execution.presentation.surface_propositions,
            context.spec_definitions,
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
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_theorem_application(
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
    pub(in crate::surface::proof) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Self, ClickError> {
        let Some(step) = self.select_theorem_application_step(application)? else {
            return Err(self.step_error(
                "theorem application requires a result-sensitive fixed-state proof after function exit",
            ));
        };
        self.apply_selected_theorem_application(step)
    }

    /// The refusal for a requirement an execution-frontier `apply` cannot
    /// discharge: the written clause, what its parameters were bound to, its
    /// instantiation spelled through the proof's names, and for a `viewable`
    /// which memory it reads, so a requirement over the current state never
    /// reads like the `at(iter, …)` fact beside it.
    fn describe_unavailable_execution_requirement(
        &self,
        theorem_environment: &TheoremEnvironment,
        application: &TheoremApplication,
        requirement_index: usize,
        requirement: &Proposition,
    ) -> String {
        let source = theorem_environment
            .get(&application.name)
            .and_then(|theorem| {
                let requirements =
                    crate::surface::proof::pure_theorems::theorem_requirement_propositions(theorem)
                        .ok()?;
                let written = requirements.get(requirement_index)?.clone();
                let bindings = theorem
                    .parameters()
                    .iter()
                    .zip(&application.arguments)
                    .map(|(parameter, argument)| {
                        (
                            parameter.name().to_string(),
                            crate::surface::diagnostics::describe_contract_expression(argument),
                        )
                    })
                    .collect::<Vec<_>>();
                Some((written, bindings))
            });
        let message = match source {
            Some((written, bindings)) => {
                // Spell the instantiation through the frontier's locals, so
                // its terms read as the names the reader wrote.
                let (parameters, arguments) = self.diagnostic_naming_tables();
                let instantiation = crate::surface::diagnostics::describe_stated_fact(
                    requirement,
                    ParameterBinding::new(&parameters, &arguments),
                );
                crate::surface::proof::theorem_application::describe_unavailable_theorem_requirement_spelled(
                    &application.name,
                    requirement_index,
                    &written,
                    &bindings,
                    &format!("`{instantiation}`"),
                )
            }
            None => format!(
                "theorem application `{}` requires an unavailable exact premise: {}",
                application.name,
                crate::surface::proof_diagnostics::render::render_proposition(requirement)
            ),
        };
        format!(
            "{message}{}",
            self.describe_viewable_memory_note(requirement)
        )
    }

    /// For a missing `viewable` requirement, which memory it reads and which
    /// memory the available `viewable` facts of the same range read. The
    /// bounded renderer labels snapshots per rendering, so without this a
    /// requirement over the current state and a fact at `at(iter, …)` print
    /// alike.
    fn describe_viewable_memory_note(&self, requirement: &Proposition) -> String {
        let Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } = requirement
        else {
            return String::new();
        };
        let Some(execution) = self.execution() else {
            return String::new();
        };
        let name_memory = |candidate: &crate::kernel::CMemory| {
            if candidate == execution.core.state.memory() {
                return "the current state".to_string();
            }
            execution
                .presentation
                .recorded_snapshots
                .iter()
                .find(|(_, state)| state.memory() == candidate)
                .map(|(selector, _)| {
                    format!(
                        "`at({}, …)`",
                        crate::surface::diagnostics::describe_snapshot_selector(selector)
                    )
                })
                .unwrap_or_else(|| "an earlier state no proof mark names".to_string())
        };
        let others = self
            .facts()
            .propositions()
            .filter_map(|fact| match fact {
                Proposition::CMemoryLoadable {
                    memory: held,
                    base: held_base,
                    bytes: held_bytes,
                    wide: false,
                } if held_base == base && held_bytes == bytes && held != memory => {
                    Some(name_memory(held))
                }
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut note = format!(
            "\n  the required `viewable` reads the memory of {}",
            name_memory(memory)
        );
        if !others.is_empty() {
            note.push_str(&format!(
                "; the available `viewable` of the same range reads {}",
                others.into_iter().collect::<Vec<_>>().join(" and ")
            ));
        }
        note
    }

    pub(super) fn select_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<ProofStep>, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.select_pure_theorem_application_step(application),
            ProofContext::FixedState(_) => {
                self.select_fixed_state_theorem_application_step(application)
            }
            // A focused function-outcome goal is one result-sensitive
            // fixed-state context: selection reads the goal-aware view directly.
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view_with_effects(OutcomeEffectContext::Frontier)
                    .expect("a focused outcome judgment resolves its fixed-state view");
                self.select_theorem_application_step_in_fixed_state(
                    application,
                    view.parameter_binding,
                    view.fixed_state,
                    view.surface_propositions,
                    view.spec_definitions,
                    view.theorem_environment,
                )
            }
            ProofContext::Execution(_) if !self.is_at_function_exit() => {
                self.select_execution_theorem_application_step(application)
            }
            // A function-exit execution Proof not focused branch on one outcome
            // still owns several result-sensitive fixed-state proof contexts; ordered
            // finalization keeps that seam until its paths derive goals.
            ProofContext::Execution(_) => return Ok(None),
        }
        .map(Some)
    }

    pub(super) fn apply_selected_theorem_application(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step(step).map_err(|error| {
            self.step_error(format!(
                "theorem search selected a simple candidate that Proof rejected: {}",
                error.raw_summary()
            ))
        })
    }

    pub(super) fn select_theorem_application_step_in_fixed_state(
        &self,
        application: &TheoremApplication,
        parameter_binding: ParameterBinding<'_>,
        fixed_state: FixedStateFrame<'_>,
        surface_propositions: &SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'_>,
        theorem_environment: &TheoremEnvironment,
    ) -> Result<ProofStep, ClickError> {
        // Resolve names for semantic checking, but retain the written arguments
        // in the certificate. A match arm's pointer value may have no spelling
        // once its source binding has been replaced with a kernel value.
        let written_application = application;
        let application = &self.resolve_theorem_application(application)?;
        let values = parameter_values(parameter_binding).map_err(|error| {
            self.step_error(format!(
                "could not bind theorem arguments: {}",
                error.message
            ))
        })?;
        let array_refs = array_refs_for_parameters(
            parameter_binding.parameters,
            &values,
            fixed_state.state.memory(),
        );
        let (values, array_refs) =
            contract_environment_at_state(&values, &array_refs, fixed_state.state);
        let integer_values = crate::persistent::PersistentMap::default();
        let algebraic_values = application
            .arguments
            .iter()
            .flat_map(contract_expression_referenced_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(&name)
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect();
        let application_context = TheoremApplicationContext {
            values: &values,
            array_refs: &array_refs,
            algebraic_values: &algebraic_values,
            pre_state: fixed_state.pre_state,
            post_state: fixed_state.state,
            result: fixed_state.result,
            recorded_snapshots: fixed_state.recorded_snapshots,
            integer_values: &integer_values,
            pointer_element_widths: parameter_pointer_element_widths(parameter_binding.parameters),
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let mut lowering_assumptions = self.facts().assumptions().clone();
        for fact in fixed_state
            .state
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
            spec_definitions,
            &unfolded_predicates,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower theorem requirements: {message}"))
        })?;

        let definition = theorem_environment
            .get(&application.name)
            .expect("requirement lowering checked the theorem name");
        let instantiated;
        let theorem = if definition.type_parameters().is_empty() {
            definition
        } else {
            instantiated = instantiate_generic_theorem_application_definition(
                definition,
                application,
                &lowering_assumptions,
                &application_context,
                spec_definitions,
            )
            .map_err(|message| self.step_error(message))?;
            &instantiated
        };
        let source_requirements =
            crate::surface::proof::pure_theorems::theorem_requirement_propositions(theorem)?;
        let source_substitutions = theorem
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_owned())
            .zip(written_application.arguments.iter().cloned())
            .collect();

        let mut premises = Vec::new();
        for (requirement_index, requirement) in requirements.into_iter().enumerate() {
            if matches!(normalize_proposition(&requirement), SimpProposition::True) {
                continue;
            }
            let matched = self
                .facts()
                .matching_fact_across_effects(&requirement, &[])
                .ok_or_else(|| {
                    self.step_error(self.describe_unavailable_execution_requirement(
                        theorem_environment,
                        application,
                        requirement_index,
                        &requirement,
                    ))
                })?;
            // The checker adds a cited range's extent guards to the evidence
            // when they are available and refuses otherwise; propose the
            // range only where it will be accepted.
            if let Some(guard) =
                crate::surface::proof::theorem_application::missing_theorem_extent_guard(
                    &requirement,
                    |guard| self.facts().available_across_effects(guard, &[]),
                )
            {
                return Err(self.step_error(format!(
                    "theorem application `{}` requires a memory range whose extent guard `{}` is not an available fact",
                    application.name,
                    crate::surface::proof_diagnostics::render::render_proposition(&guard),
                )));
            }

            // Prefer the latest recorded spelling of this exact fact. Formal
            // substitution can put a historical array read inside a scalar
            // cast, which lowers internally but cannot be written as Click.
            // This indexed lookup never searches unrelated facts or history;
            // re-lowering checks that the spelling still names this premise.
            if let Ok(surface) = surface_propositions.surface(&matched)
                && let Ok(lowered) =
                    self.lower_surface_proposition(surface, "recorded theorem premise")
                && (lowered == requirement || condition_polarity_equivalent(&lowered, &requirement))
                && self.facts().available_across_effects(&lowered, &[])
            {
                if !premises.contains(surface) {
                    premises.push(surface.clone());
                }
                continue;
            }

            // The theorem's own clause supplies a source form even when its
            // match-bound arguments have no independently synthesizable names.
            if let Some(source_requirement) = source_requirements.get(requirement_index)
                && let Ok(surface) =
                    substitute_click_proposition(source_requirement, &source_substitutions)
                && let Ok(lowered) =
                    self.lower_surface_proposition(&surface, "selected theorem premise")
                && (lowered == requirement || condition_polarity_equivalent(&lowered, &requirement))
                && self.facts().available_across_effects(&lowered, &[])
            {
                if !premises.contains(&surface) {
                    premises.push(surface);
                }
                continue;
            }

            // Reuse the established snapshot-surface search for execution
            // proofs, with availability answered by persistent indexes. The
            // matched fact above comes from the requirement's shape bucket,
            // so sibling terms carrying different memory snapshots remain
            // visible without rebuilding the complete ambient fact vector.
            // The returned form still has to survive `apply_step` below.
            let mut snapshot_surface_error = None;
            if let ProofContext::Execution(context) = self.context.as_ref() {
                let execution = self
                    .execution()
                    .expect("execution proof owns semantic state");
                match checked_surface_comparison_fact_in_state_with_indexed_facts(
                    execution.view(context),
                    &matched,
                    SurfaceFactMatch::CanonicalExact,
                    self.facts(),
                    &lowering_assumptions,
                    parameter_binding,
                    fixed_state.state,
                    spec_definitions,
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
                synthesize_surface_proposition(&matched, parameter_binding, fixed_state.state)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            if let Some(candidate) =
                synthesize_surface_proposition(&requirement, parameter_binding, fixed_state.state)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            if candidates.is_empty() {
                return Err(self.step_error(format!(
                    "theorem application `{}` has no checked surface form for exact premise `{}`",
                    application.name,
                    crate::surface::proof_diagnostics::render::render_proposition(&requirement),
                )));
            }
            let surface = candidates
                .into_iter()
                // SurfacePropositionMap treats the most recently recorded
                // form as preferred. Prefer it here too; earlier entries
                // can be mechanically valid but over-anchor constants as
                // `at(selector, constant)` and produce needlessly unstable
                // certificates.
                .rev()
                .find(|candidate| {
                    let matches_requirement = |lowered: &Proposition| {
                        (lowered.clone()
                            == requirement.clone()
                            || condition_polarity_equivalent(lowered, &requirement))
                            && self                                .facts()                                .available_across_effects(lowered, &[])
                    };
                    let direct = lower_fixed_state_proposition_with_assumptions(
                        candidate,
                        &lowering_assumptions,
                        parameter_binding,
                        fixed_state,
                        spec_definitions,
                    );
                    direct.as_ref().is_ok_and(matches_requirement)
                })
                .ok_or_else(|| {
                    self.step_error(format!(
                        "theorem application `{}` has no checked surface form for exact premise `{}`{}",
                        application.name,
                        crate::surface::proof_diagnostics::render::render_proposition(&requirement),
                        snapshot_surface_error
                            .as_ref()
                            .map(|error| format!(": {}", error.raw_summary()))
                            .unwrap_or_default(),
                    ))
                })?;
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }

        premises.extend(self.integer_argument_guard_premises(
            theorem,
            application,
            &application_context,
            &premises,
        )?);
        Ok(ProofStep::ApplyTheoremUsing {
            application: written_application.clone(),
            premises,
        })
    }

    /// Untrusted pure smart-tactic query for one explicit theorem step.
    /// This instantiates the applied theorem's own requirement forms and
    /// probes their lowered forms through the current persistent fact index;
    /// it cannot advance the proof or add the theorem's conclusion.
    pub(in crate::surface::proof) fn select_pure_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<ProofStep, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(
                self.step_error("pure theorem-application search requires a proposition goal")
            );
        };
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let recorded_snapshots = RecordedSnapshots::new();
        let algebraic_values = application
            .arguments
            .iter()
            .flat_map(contract_expression_referenced_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(&name)
                    .cloned()
                    .or_else(|| {
                        context
                            .structural_induction_setup
                            .as_ref()?
                            .algebraic_values
                            .get(&name)
                            .cloned()
                    })
                    .map(|value| (name, value))
            })
            .collect();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            algebraic_values: &algebraic_values,
            pre_state: &state,
            post_state: &state,
            result: None,
            recorded_snapshots: &recorded_snapshots,
            integer_values: &context.theorem_context.integer_values,
            pointer_element_widths: BTreeMap::new(),
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let requirements = lower_theorem_application_requirements_with_assumptions(
            context.theorem_environment,
            application,
            &application_context,
            self.facts().assumptions(),
            context.spec_definitions,
            &unfolded_predicates,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower theorem requirements: {message}"))
        })?;
        let theorem = context
            .theorem_environment
            .get(&application.name)
            .ok_or_else(|| self.step_error(format!("unknown theorem `{}`", application.name)))?;
        let theorem = instantiate_generic_theorem_application_definition(
            theorem,
            application,
            self.facts().assumptions(),
            &application_context,
            context.spec_definitions,
        )
        .map_err(|message| self.step_error(message))?;
        let substitutions = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .map(str::to_string)
            .zip(application.arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();

        let source_requirements =
            crate::surface::proof::pure_theorems::theorem_requirement_propositions(&theorem)
                .map_err(|error| self.step_error(error.message))?;
        let mut premises = Vec::new();
        for (requirement_index, (requirement, source_surface)) in requirements
            .into_iter()
            .zip(&source_requirements)
            .enumerate()
        {
            // Omit only the requirements the explicit theorem checker can
            // discharge without evidence. Broader context-free planning can
            // prove constructor inequalities, but dropping their written
            // facts here leaves `apply using` with an unchecked premise.
            if matches!(normalize_proposition(&requirement), SimpProposition::True) {
                continue;
            }
            let mut surface = substitute_click_proposition(source_surface, &substitutions)
                .map_err(|message| self.step_error(message))?;
            let mut lowered =
                self.lower_surface_proposition(&surface, "selected theorem premise")?;
            // Kernel spec lowering can retain only an exactly known true left
            // disjunct, avoiding an undefined unused right expression. Cite that
            // same written left fact rather than requiring the whole disjunction
            // to be an exact ambient fact in a pure proof.
            if lowered != requirement
                && let ClickProposition::Or(left, _) = &surface
            {
                let left_lowered =
                    self.lower_surface_proposition(left, "selected left theorem premise")?;
                if left_lowered == requirement && self.facts().contains(&left_lowered) {
                    surface = left.as_ref().clone();
                    lowered = left_lowered;
                }
            }
            if lowered.clone() != requirement.clone() || !self.facts().contains(&lowered) {
                // `Debug` on a kernel proposition dumps the memory snapshots
                // and algebraic schemas it is indexed by; the reader needs the
                // clause and the fact it instantiates to.
                return Err(self.step_error(describe_unavailable_theorem_requirement(
                    &application.name,
                    requirement_index,
                    &surface,
                    &[],
                    &requirement,
                )));
            }
            // The checker adds the range's extent guards to the evidence
            // when they are available and refuses otherwise; propose the
            // range only where it will be accepted.
            if let Some(guard) =
                crate::surface::proof::theorem_application::missing_theorem_extent_guard(
                    &requirement,
                    |guard| self.facts().exact_available_across_effects(guard, &[]),
                )
            {
                return Err(self.step_error(format!(
                    "theorem `{}` requirement {} states a memory range whose extent guard `{}` is not an available fact",
                    application.name,
                    requirement_index + 1,
                    crate::surface::proof_diagnostics::render::render_proposition(&guard),
                )));
            }
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }
        premises.extend(self.integer_argument_guard_premises(
            &theorem,
            application,
            &application_context,
            &premises,
        )?);
        Ok(ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises,
        })
    }

    /// Propose checked source evidence for evaluation of mathematical theorem
    /// arguments. Formal callee requirements alone cannot justify a native
    /// overflow, load or domain condition inside an argument expression.
    fn integer_argument_guard_premises(
        &self,
        theorem: &TheoremDefinition,
        application: &TheoremApplication,
        context: &TheoremApplicationContext<'_>,
        formal_premises: &[ClickProposition],
    ) -> Result<Vec<ClickProposition>, ClickError> {
        let mut premises = Vec::new();
        let arguments = theorem
            .parameters()
            .iter()
            .zip(&application.arguments)
            .filter(|(parameter, argument)| {
                parameter.click_type() == &ClickType::Integer
                    && crate::surface::lowering::lower_contract_integer_to_spec(
                        argument,
                        context.integer_values,
                    )
                    .is_err()
            })
            .map(|(_, argument)| argument)
            .collect::<Vec<_>>();
        if arguments.is_empty() {
            return Ok(premises);
        }
        let spec_definitions = match self.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions,
            ProofContext::FixedState(context) => context.spec_definitions,
            ProofContext::Execution(context) => context.spec_definitions,
        };
        let mut explicit = PureFactContext::new();
        for surface in formal_premises {
            explicit = explicit
                .assume_proposition(self.lower_surface_proposition(surface, "theorem premise")?);
        }
        for argument in arguments {
            // Source forms retain evaluation guards even when evaluation under
            // the ambient context has already discharged and removed them.
            let mut pending = vec![argument];
            while let Some(expression) = pending.pop() {
                match expression {
                    ContractExpression::Call { name, arguments } => {
                        if name == "to_integer" && arguments.len() == 1 {
                            let surface = ClickProposition::Defined {
                                expression: arguments[0].clone(),
                            };
                            if let Ok(lowered) = self
                                .lower_surface_proposition(&surface, "Integer observation guard")
                                && !normalizes_context_free(&lowered)
                                && self.facts().listed_premise_available(&lowered, &[], false)
                            {
                                explicit = explicit.assume_proposition(lowered);
                                premises.push(surface);
                            }
                        } else if matches!(
                            name.as_str(),
                            "truncating_quotient" | "truncating_remainder"
                        ) && arguments.len() == 2
                        {
                            let surface = ClickProposition::Comparison {
                                left: arguments[1].clone(),
                                operator: ComparisonOperator::NotEqual,
                                right: ContractExpression::IntegerLiteral("0".into()),
                            };
                            if let Ok(lowered) =
                                self.lower_surface_proposition(&surface, "Integer divisor guard")
                                && !normalizes_context_free(&lowered)
                                && self.facts().listed_premise_available(&lowered, &[], false)
                            {
                                explicit = explicit.assume_proposition(lowered);
                                premises.push(surface);
                            }
                        }
                        pending.extend(arguments);
                    }
                    ContractExpression::Add(a, b)
                    | ContractExpression::Subtract(a, b)
                    | ContractExpression::Multiply(a, b) => {
                        pending.extend([a.as_ref(), b.as_ref()]);
                    }
                    ContractExpression::Old(value) | ContractExpression::Negate(value) => {
                        pending.push(value)
                    }
                    ContractExpression::At { expression, .. } => pending.push(expression),
                    _ => {}
                }
            }
            let (_, guards) = capture_fixed_state_integer_expression_with_guards(
                argument,
                context.integer_values,
                self.facts().assumptions(),
                ContractEnvironment::new(context.values, context.array_refs),
                FixedStateFrame::new(
                    context.pre_state,
                    context.post_state,
                    context.result,
                    context.recorded_snapshots,
                ),
                spec_definitions,
            )
            .map_err(|message| self.step_error(message))?;
            for guard in guards {
                if normalizes_context_free(&guard) {
                    continue;
                }
                let surface = self.context_surface_propositions()
                    .into_iter().flat_map(|forms| forms.surfaces(&guard))
                    .find(|surface| self.lower_surface_proposition(surface, "Integer argument guard")
                        .is_ok_and(|lowered| lowered == guard && self.facts().listed_premise_available(&lowered, &[], false)))
                    .cloned().ok_or_else(|| self.step_error(format!(
                        "Integer theorem argument needs explicit source evidence for `{}`; cite its evaluation guard with `apply(...) using {{ ... }}`",
                        crate::surface::proof_diagnostics::render::render_proposition(&guard))))?;
                let lowered = self.lower_surface_proposition(&surface, "Integer capture guard")?;
                explicit = explicit.assume_proposition(lowered);
                premises.push(surface);
            }
            // Check the proposed argument evidence before returning a simple
            // candidate. An unsupported source form is a bounded search refusal,
            // never a candidate whose certificate disagrees with the checker.
            capture_fixed_state_integer_expression(
                argument,
                context.integer_values,
                &explicit,
                ContractEnvironment::new(context.values, context.array_refs),
                FixedStateFrame::new(
                    context.pre_state,
                    context.post_state,
                    context.result,
                    context.recorded_snapshots,
                ),
                spec_definitions,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "Integer argument needs explicit evaluation evidence: {message}"
                ))
            })?;
        }
        Ok(premises)
    }

    /// The guarantees of a theorem application as the caller would write
    /// them: each `ensures` of the applied theorem with the application's
    /// arguments substituted for its parameters, in declaration order.
    ///
    /// This spells conclusions; it establishes nothing. The caller retains
    /// one only after matching it against a fact the checked application
    /// added, so an application this cannot spell yields no conclusions
    /// rather than an error. A generic theorem is spelled only in a pure
    /// theorem proof, where its type instance is inferred from the
    /// arguments alone.
    pub(in crate::surface::proof) fn theorem_application_surface_conclusions(
        &self,
        application: &TheoremApplication,
    ) -> Vec<ClickProposition> {
        let Ok(application) = self.resolve_theorem_application(application) else {
            return Vec::new();
        };
        let theorem_environment = match self.context.as_ref() {
            ProofContext::Pure(context) => context.theorem_environment,
            ProofContext::FixedState(context) => context.theorem_environment,
            ProofContext::Execution(context) => context.theorem_environment,
        };
        let Some(theorem) = theorem_environment.get(&application.name) else {
            return Vec::new();
        };
        let theorem = if theorem.type_parameters().is_empty() {
            theorem.clone()
        } else {
            let ProofContext::Pure(context) = self.context.as_ref() else {
                return Vec::new();
            };
            let state = CState::new().with_memory(context.theorem_context.memory.clone());
            let recorded_snapshots = RecordedSnapshots::new();
            let algebraic_values = application
                .arguments
                .iter()
                .flat_map(contract_expression_referenced_names)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .filter_map(|name| {
                    self.local_algebraic_values()
                        .get(&name)
                        .cloned()
                        .or_else(|| {
                            context
                                .structural_induction_setup
                                .as_ref()?
                                .algebraic_values
                                .get(&name)
                                .cloned()
                        })
                        .map(|value| (name, value))
                })
                .collect();
            let application_context = TheoremApplicationContext {
                values: &context.theorem_context.values,
                array_refs: &context.theorem_context.array_refs,
                algebraic_values: &algebraic_values,
                pre_state: &state,
                post_state: &state,
                result: None,
                recorded_snapshots: &recorded_snapshots,
                integer_values: &context.theorem_context.integer_values,
                pointer_element_widths: BTreeMap::new(),
            };
            let Ok(theorem) = instantiate_generic_theorem_application_definition(
                theorem,
                &application,
                self.facts().assumptions(),
                &application_context,
                context.spec_definitions,
            ) else {
                return Vec::new();
            };
            theorem
        };
        if theorem.parameters().len() != application.arguments.len() {
            return Vec::new();
        }
        let substitutions = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .map(str::to_string)
            .zip(application.arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        theorem
            .ensures()
            .iter()
            .filter_map(|ensure| match ensure.ensure() {
                Ensure::Proposition(conclusion) => {
                    substitute_click_proposition(conclusion, &substitutions).ok()
                }
                _ => None,
            })
            .collect()
    }
}
