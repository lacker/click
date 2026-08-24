//! Predicate and resource unfold/fold/observation steps.

use super::*;

impl<'a> Proof<'a> {
    pub(super) fn apply_predicate_unfold(&self, name: &String) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => self.apply_proposition_predicate_unfold(
                name,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                self.node.depth,
            ),
            ProofContext::Point(context) => self.apply_proposition_predicate_unfold(
                name,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                context.tactic_index,
            ),
            // A function-outcome goal unfolds its own path-local facts and
            // delta only: the borrowed execution snapshot is shared by every
            // sibling outcome and must not absorb one path's unfolding.
            ProofContext::Execution(context) if self.focused_outcome_point().is_some() => self
                .apply_proposition_predicate_unfold(
                    name,
                    context.predicate_environment,
                    context.click_function_environment,
                    context.claim_label,
                    context.tactic_index,
                ),
            ProofContext::Execution(_) => self.apply_execution_unfold(name),
        }
    }

    pub(super) fn apply_proposition_predicate_unfold(
        &self,
        name: &String,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        claim_label: &str,
        tactic_index: usize,
    ) -> Result<ProofState, ClickError> {
        let checked = check_unfold_predicate_in_facts(
            &self.facts(),
            name,
            predicate_environment,
            click_function_environment,
            claim_label,
            tactic_index,
        )?;
        let goal = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => {
                let surface = match &goal.surface {
                    Some(surface) => Some(
                        unfold_structural_invariant_proposition(
                            predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))?,
                    ),
                    None => None,
                };
                // Point and outcome certificates replay `unfold` from its
                // retained surface form.  Re-lower that unfolded body
                // against the checked successor facts as part of this same
                // audited step, so resource counts and current memory loads
                // resolve exactly as they do during independent replay.
                // Unfolding only the already-lowered kernel predicate leaves
                // those expressions stranded in the older lowering context.
                let kernel = match (&surface, self.context.as_ref()) {
                    (Some(surface), ProofContext::Point(context)) => {
                        let surface = self.substitute_point_locals_in_proposition(surface)?;
                        lower_point_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            context.parameters,
                            context.arguments,
                            context.pre_state,
                            context.state,
                            context.result,
                            context.program_point_states,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .map_err(|message| self.step_error(message))?
                    }
                    (Some(surface), ProofContext::Execution(_))
                        if self.focused_outcome_point().is_some() =>
                    {
                        let view = self
                            .outcome_point_view()
                            .expect("a focused outcome judgment resolves its point view");
                        let surface = self.substitute_point_locals_in_proposition(surface)?;
                        lower_point_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            view.parameters,
                            view.arguments,
                            view.pre_state,
                            view.state,
                            view.result,
                            view.program_point_states,
                            view.predicate_environment,
                            view.click_function_environment,
                        )
                        .map_err(|message| self.step_error(message))?
                    }
                    _ => unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        std::slice::from_ref(name),
                        &goal.kernel,
                        checked.facts.assumptions(),
                    )
                    .map_err(|message| self.step_error(message))?,
                };
                self.refined_proposition(
                    self.refined_context(checked.facts.clone()),
                    kernel,
                    surface,
                )
            }
            Some(goal @ (Goal::Frontier(_) | Goal::FunctionOutcome(_))) => {
                let mut unfolded = goal.context().unfolded_predicates.clone();
                unfolded.insert(name.clone());
                goal.with_context(GoalContext {
                    facts: checked.facts.clone(),
                    unfolded_predicates: unfolded,
                    execution: goal.context().execution.clone(),
                })
            }
            None => return Err(self.step_error("`unfold` requires an open goal")),
        };
        let goal = {
            let mut unfolded = goal.context().unfolded_predicates.clone();
            unfolded.insert(name.clone());
            goal.with_context(GoalContext {
                facts: goal.context().facts.clone(),
                unfolded_predicates: unfolded,
                execution: goal.context().execution.clone(),
            })
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            goals: self.state.goals.replace_at(self.focused, goal),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    pub(super) fn apply_execution_unfold(&self, name: &String) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`unfold` requires an execution-frontier proof"));
        };
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let checked = check_unfold_predicate_facts(
            &mut execution.replay,
            &execution.state,
            &self.facts(),
            name,
            context.function,
            context.arguments,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        let mut unfolded_predicates = self.focused_goal_unfolds().clone();
        for name in &checked.added_unfolded_predicates {
            unfolded_predicates.insert(name.clone());
        }
        let refined_goal = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => {
                let surface = goal
                    .surface
                    .as_deref()
                    .map(|surface| {
                        unfold_structural_invariant_proposition(
                            context.predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))
                    })
                    .transpose()?;
                let kernel = match &surface {
                    Some(surface) => {
                        let surface = self.substitute_point_locals_in_proposition(surface)?;
                        let pre_state = execution.replay.old_reference_state(&execution.state);
                        lower_point_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            context.parsed_function.parameters(),
                            context.arguments,
                            pre_state,
                            &execution.state,
                            None,
                            &execution.replay.program_point_states,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .map_err(|message| {
                            self.step_error(format!("could not unfold proposition goal: {message}"))
                        })?
                    }
                    None => unfold_predicates_in_proposition(
                        context.predicate_environment,
                        context.click_function_environment,
                        std::slice::from_ref(name),
                        &goal.kernel,
                        checked.facts.assumptions(),
                    )
                    .map_err(|message| self.step_error(message))?,
                };
                Some((kernel, surface))
            }
            _ => None,
        };
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_function_entry_prerequisites,
            function_entry_derivations: checked.added_function_entry_derivations,
            unfolded_predicates: checked.added_unfolded_predicates,
            statement_partition: None,
        };
        let goal_context = GoalContext {
            facts: checked.facts,
            unfolded_predicates,
            execution: Some(Arc::new(execution)),
        };
        let goal = match refined_goal {
            Some((kernel, surface)) => self.refined_proposition(goal_context, kernel, surface),
            None => self
                .focused_goal()
                .expect("execution unfold requires an open goal")
                .with_context(goal_context),
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            // A nested proposition proof stated at this frontier unfolds its
            // own goal through the same checked operation. Other execution
            // goals retain their kind while installing the updated snapshot
            // and unfold delta.
            goals: self.state.goals.replace_at(self.focused, goal),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    pub(super) fn apply_execution_resource_observation(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`observe` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`observe`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(
                self.step_error("`observe` must run before execution reaches function exit")
            );
        }
        let checked = observe_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.state).clone(),
            self.facts().clone(),
            &mut execution.replay.surface_propositions,
            &mut execution.replay.function_entry_derivations,
            &mut execution.replay.function_entry_execution_prerequisites,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.state = checked.state.into();
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_certification_facts,
            function_entry_derivations: checked.added_derivations,
            unfolded_predicates: Vec::new(),
            statement_partition: None,
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .replace_frontier_at(self.focused, checked.facts, execution),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    pub(super) fn apply_execution_resource_unfold(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource `unfold` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("resource `unfold`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(self
                .step_error("resource `unfold` must run before execution reaches function exit"));
        }
        let checked = unfold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.state).clone(),
            self.facts().clone(),
            &mut execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.state = checked.state.into();
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .replace_frontier_at(self.focused, checked.facts, execution),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    pub(super) fn apply_execution_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource `fold` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("resource `fold`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(
                self.step_error("resource `fold` must run before execution reaches function exit")
            );
        }
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        let checked = fold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            context.tactic_index,
            self.facts().clone(),
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            (*execution.state).clone(),
            context.predicate_environment,
            context.click_function_environment,
            &execution.replay.unfolded_predicates,
        )?;
        execution.state = checked.state.into();
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .replace_frontier_at(self.focused, checked.facts, execution),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Applies one source-ordered composite fold to the focused typed outcome.
    /// The result/state snapshot and persistent fact root advance together in
    /// the returned Proof successor; no caller-owned outcome is mutated.
    pub(super) fn apply_outcome_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource `fold` requires an execution proof"));
        };
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("outcome resource `fold` requires a focused outcome goal"));
        };
        let execution = goal.context.execution.as_deref().ok_or_else(|| {
            self.step_error("outcome resource `fold` lost its execution snapshot")
        })?;
        let pre_state = execution.replay.execution_start_state(&execution.state);
        let outcome = CFunctionOutcome::Return {
            value: (*goal.point.result).clone(),
            state: (*goal.point.state).clone(),
        };
        let checked = fold_composite_resource_on_outcome_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            goal.path_index,
            &goal.point.execution_pure_facts,
            self.facts().clone(),
            &goal.point.surface_propositions,
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            outcome,
            context.predicate_environment,
            context.click_function_environment,
            &self.active_unfolded_predicates(),
        )?;
        let CFunctionOutcome::Return { value, state } = checked.outcome else {
            unreachable!("folding a return outcome preserves its outcome kind")
        };
        let mut point = (*goal.point).clone();
        point.result = Arc::new(value);
        point.state = state.into();
        let mut updated = goal.clone();
        updated.point = Arc::new(point);
        updated.context.facts = checked.facts;
        Ok(ProofState {
            locals: self.state.locals.clone(),
            goals: self
                .state
                .goals
                .replace_at(self.focused, Goal::FunctionOutcome(updated)),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }
}
