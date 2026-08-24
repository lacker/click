//! Simple-step dispatch (`apply_step`) and checked frame application.

use super::*;

impl<'a> Proof<'a> {
    /// Checks one explicit simple step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(in crate::lang::click::proof) fn apply_step(
        &self,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, None)
    }

    /// Applies a step while retaining its source occurrence for any ordered
    /// terminal work the checked transition has to schedule. The source site
    /// affects diagnostics and finalization order only; the certificate node
    /// remains exactly the supplied `SimpleProofStep`.
    pub(super) fn apply_step_with_origin(
        &self,
        step: SimpleProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin_mode(step, origin, false)
    }

    /// Applies one step while optionally retaining a closed structural-effect
    /// frontier long enough for enclosing resource scopes to close. That
    /// retained frontier is sealed: only `ProofScope::join_inner` may consume
    /// it, and the outermost resource join retires the goal.
    pub(super) fn apply_step_with_origin_mode(
        &self,
        step: SimpleProofStep,
        origin: Option<ProofStepOrigin>,
        retain_closed_loop_effect_goal: bool,
    ) -> Result<Self, ClickError> {
        if self.focused_discharged() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                simple_step_source_name(&step)
            )));
        }
        if self.focused_loop_effect_closed() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                simple_step_source_name(&step)
            )));
        }

        if let SimpleProofStep::Have { proposition, proof } = &step {
            return self.apply_have_step(proposition, proof);
        }
        if let SimpleProofStep::Step = &step {
            return self.apply_execution_statement_step(step, &[]);
        }
        if let SimpleProofStep::StepUsing(premises) = &step {
            return self.apply_execution_statement_step(step.clone(), premises);
        }

        let next_state = match &step {
            SimpleProofStep::Mark(name) => self.apply_execution_mark(name),
            SimpleProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            SimpleProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            SimpleProofStep::UnfoldPredicate(name) => self.apply_predicate_unfold(name),
            SimpleProofStep::UnfoldResource(resource) => {
                self.apply_execution_resource_unfold(resource)
            }
            SimpleProofStep::FoldResource(resource) => {
                if self.focused_outcome_point().is_some() {
                    self.apply_outcome_resource_fold(resource)
                } else {
                    self.apply_execution_resource_fold(resource)
                }
            }
            SimpleProofStep::ObserveResource(resource) => {
                self.apply_execution_resource_observation(resource)
            }
            SimpleProofStep::Choose(choice) => self.apply_point_choose(choice),
            SimpleProofStep::Witness(witness) => self.apply_point_witness(witness),
            SimpleProofStep::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => self.apply_point_instantiate_using(quantified, argument, premises),
            SimpleProofStep::Extract(proposition) => self.apply_extract(proposition),
            SimpleProofStep::Rewrite(equality) => self.apply_rewrite(equality),
            SimpleProofStep::Assumption => self.apply_assumption(),
            SimpleProofStep::Normalize => self.apply_normalize(),
            SimpleProofStep::Intro => self.apply_intro(),
            SimpleProofStep::Split => self.apply_split(),
            SimpleProofStep::Left => self.apply_left(),
            SimpleProofStep::Right => self.apply_right(),
            SimpleProofStep::Enumerate => self.apply_enumerate(),
            SimpleProofStep::Contradiction(surface) => self.apply_contradiction(surface),
            SimpleProofStep::CloseInvariants => self.apply_close_invariants(),
            SimpleProofStep::FrameUsing { region, premises } => {
                if self.focused_outcome_point().is_some() {
                    self.apply_outcome_frame_using(region.as_ref(), premises)
                } else {
                    self.apply_execution_frame_using(
                        region.as_ref(),
                        premises,
                        origin,
                        retain_closed_loop_effect_goal,
                    )
                }
            }
            _ => {
                Err(self
                    .step_error("this simple step has not yet migrated to the checked `Proof` API"))
            }
        }?;

        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(next_state),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused: self.focused,
                depth: self.node.depth + 1,
            }),
            focused: self.focused,
        })
    }

    /// Applies one explicit `Have` through the same owned scope operations as
    /// a source `have` block. Each body step advances the scope's persistent
    /// child `Proof`; joining publishes only the checked proposition and
    /// retains the body's exact surface operations as provenance. A failed
    /// body leaves this immutable root untouched.
    pub(super) fn apply_have_step(
        &self,
        proposition: &ClickProposition,
        proof: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        let mut scope = self.begin_have(proposition.clone())?;
        for step in proof.steps() {
            scope = scope.apply_step(step.clone())?;
        }
        scope.join()
    }

    pub(super) fn selected_effect_indices(
        &self,
        context: &ExecutionProofContext<'_>,
    ) -> Result<Vec<usize>, ClickError> {
        let selection = match self.focused_goal() {
            Some(Goal::Frontier(FrontierGoal { selection, .. })) => *selection,
            Some(Goal::FunctionOutcome(OutcomeGoal { selection, .. })) => *selection,
            _ => {
                return Err(self.step_error("`frame using` requires an execution effect goal"));
            }
        };
        let effect_count = context.function_block.effects().len();
        let indices = match selection {
            EffectGoalSelection::None => Vec::new(),
            EffectGoalSelection::One(index) if index < effect_count => vec![index],
            EffectGoalSelection::One(index) => {
                return Err(self.step_error(format!(
                    "selected effect goal {index} does not exist; the function has {effect_count} effect clauses"
                )));
            }
            EffectGoalSelection::All => (0..effect_count).collect(),
        };
        if indices.is_empty() {
            return Err(self.step_error("`frame using` has no function effect goal to prove"));
        }
        Ok(indices)
    }

    /// Whether a transitional driver may check and then export this frame
    /// step. Empty mutable function frames stay out of that adapter: their
    /// exact `Proof` meaning differs from the legacy ambient-fact behavior,
    /// so checking one before compatibility replay would apply earlier smart
    /// operations twice. An authoritative Proof unit applies the exact step
    /// directly instead of consulting this compatibility query.
    pub(super) fn supports_checked_execution_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        if !matches!(region, None | Some(CodeRegionRef::Function)) {
            return Ok(true);
        }
        if !premises.is_empty() {
            return Ok(true);
        }
        let effect_indices = self.selected_effect_indices(context)?;
        Ok(effect_indices.iter().all(|index| {
            matches!(
                context.function_block.effects()[*index].effect(),
                Effect::Immutable
            )
        }))
    }

    /// Checks one explicit function-level frame step exactly once and records
    /// private authority for the ordered outcome finalizer. Keep this rule
    /// outlined so its execution-state locals do not enlarge the common
    /// simple-step dispatcher frame; the expansion small-stack test pins that
    /// dispatch budget.
    #[inline(never)]
    pub(super) fn apply_outcome_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`frame using` requires an execution proof"));
        };
        if !matches!(region, None | Some(CodeRegionRef::Function)) {
            return Err(
                self.step_error("a result-aware `frame using` can close only the function effect")
            );
        }
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("result-aware `frame using` requires an outcome goal"));
        };
        let effect_indices = self.selected_effect_indices(context)?;
        let execution = goal.context.execution.as_deref().ok_or_else(|| {
            self.step_error("result-aware `frame using` lost its execution snapshot")
        })?;
        let pre_state = execution.replay.execution_start_state(&execution.state);

        let mut point = (*goal.point).clone();
        let mut frame_facts = Vec::with_capacity(premises.len());
        for surface in premises {
            let fact = point
                .surface_propositions
                .available_kernel_matching(surface, |kernel| self.facts().contains(kernel))
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    self.lower_surface_proposition(surface, "`frame using` premise")
                })?;
            if !self.facts().contains(&fact) {
                return Err(self.step_error(format!(
                    "`frame using` requires an exact available premise: {fact:?}"
                )));
            }
            point.surface_propositions.record_lowering(surface, &fact)?;
            if !frame_facts.contains(&fact) {
                frame_facts.push(fact);
            }
        }

        let mut outcome = CFunctionOutcome::Return {
            value: (*point.result).clone(),
            state: (*point.state).clone(),
        };
        for effect_index in &effect_indices {
            let claim = FunctionClaimRef::Effect(
                *effect_index,
                &context.function_block.effects()[*effect_index],
            );
            let claim_label =
                function_claim_label(context.function_block.signature().name(), &claim);
            check_effect_claim_exact(
                &claim_label,
                goal.path_index,
                &point.effect_facts,
                &frame_facts,
                &claim,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                &outcome,
            )?;
        }

        let mut assumptions = self.facts().assumptions().clone();
        for fact in point.effect_facts.iter() {
            assumptions = assumptions.assume_proposition(fact.proposition().clone());
        }
        let (transitioned, _obligations) =
            crate::kernel::apply_c_function_contract_resource_transition(
                pre_state,
                context.function,
                context.arguments,
                outcome,
                &assumptions,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not apply checked contract resource effect: {message}"
                ))
            })?;
        outcome = transitioned;
        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(self.step_error(
                "checked contract resource effect did not preserve the return outcome",
            ));
        };
        point.result = Arc::new(value);
        point.state = state.into();
        let mut updated = goal.clone();
        updated.selection = EffectGoalSelection::None;
        updated.checked_effects = Arc::new(effect_indices);
        updated.point = Arc::new(point);
        Ok(ProofState {
            locals: self.state.locals.clone(),
            goals: self
                .state
                .goals
                .replace_at(self.focused, Goal::FunctionOutcome(updated)),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(frame_facts),
        })
    }

    #[inline(never)]
    pub(super) fn apply_execution_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
        origin: Option<ProofStepOrigin>,
        retain_closed_loop_effect_goal: bool,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`frame using` requires an execution proof"));
        };
        self.require_execution_frontier("`frame using`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;

        let mut frame_facts = Vec::with_capacity(premises.len());
        for surface in premises {
            let fact = execution
                .replay
                .surface_propositions
                .available_kernel_matching(surface, |kernel| {
                    self.facts()
                        .replay_available_across_effects(kernel, &execution.replay.effect_facts)
                })
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    self.lower_surface_proposition(surface, "`frame using` premise")
                })?;
            if !self
                .facts()
                .replay_available_across_effects(&fact, &execution.replay.effect_facts)
            {
                return Err(self.step_error(format!(
                    "`frame using` requires an exact available premise: {fact:?}"
                )));
            }
            execution
                .replay
                .surface_propositions
                .record_lowering(surface, &fact)?;
            if !frame_facts.contains(&fact) {
                frame_facts.push(fact);
            }
        }
        if execution.replay.loop_effect_goal.is_some() {
            if region.is_some() {
                return Err(
                    self.step_error("a structural effect proof must use unqualified `frame using`")
                );
            }
            let goal = execution
                .replay
                .loop_effect_goal
                .as_ref()
                .expect("the loop effect goal was observed above");
            if goal.closed {
                return Err(self.step_error("the structural effect goal was closed more than once"));
            }
            let mut loop_effect_facts = frame_facts.clone();
            loop_effect_facts.extend(
                execution
                    .replay
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            loop_effect_facts.extend(self.facts().memory_effect_summaries().cloned());
            loop_effect_facts.sort();
            loop_effect_facts.dedup();
            c_loop_effects_hold_at_back_edge(
                &goal.before_state,
                &execution.state,
                std::slice::from_ref(&goal.check),
                &loop_effect_facts,
                &assumptions_from_propositions(&loop_effect_facts),
            )
            .map_err(|message| self.step_error(format!("`frame using` failed: {message}")))?;
            execution
                .replay
                .loop_effect_goal
                .as_mut()
                .expect("the checked loop effect goal remains present")
                .closed = true;
            let goals = if retain_closed_loop_effect_goal {
                self.state
                    .goals
                    .replace_frontier_at(self.focused, self.facts().clone(), execution)
            } else {
                self.state.goals.discharge_at(self.focused)
            };
            return Ok(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(frame_facts),
            });
        }
        if !execution.replay.is_at_function_exit() {
            return Err(self.step_error("`frame using` requires function exit"));
        }
        if let Some(region) = region {
            // Loop effect clauses are declared by frontier-local `loop`
            // tactics. Bind the exact clauses already checked on this replay
            // before resolving labels or validating the qualified frame.
            let frame_function_block =
                (!execution.replay.frontier_loop_clauses.is_empty()).then(|| {
                    context.function_block.with_bound_frontier_loop_clauses(
                        &execution.replay.frontier_loop_clauses.to_vec(),
                    )
                });
            let frame_function_block = frame_function_block
                .as_ref()
                .unwrap_or(context.function_block);
            let resolved = resolve_code_region_ref(
                frame_function_block,
                region,
                context.claim_label,
                context.tactic_index,
            )?;
            if !matches!(resolved, CodeRegion::Function) {
                validate_qualified_frame_code_region(
                    frame_function_block,
                    context.parsed_function,
                    resolved,
                    context.claim_label,
                    origin.map_or(context.tactic_index, |origin| origin.tactic_index),
                )?;
                let origin = origin.unwrap_or(ProofStepOrigin {
                    tactic_index: context.tactic_index,
                    source_index: context.tactic_index,
                });
                execution.replay.defer_checked_post_execution(
                    origin.tactic_index,
                    origin.source_index,
                    PostExecutionTactic::FrameRegion(region.clone()),
                );
                execution.last_step_delta = ExecutionProofStepDelta::default();
                return Ok(ProofState {
                    locals: self.state.locals.clone(),

                    goals: self.state.goals.replace_frontier_at(
                        self.focused,
                        self.facts().clone(),
                        execution,
                    ),
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                });
            }
        }

        let effect_indices = self.selected_effect_indices(context)?;

        let checked_execution = execution.replay.execution().ok_or_else(|| {
            self.step_error("function-exit proof has no checked execution outcomes")
        })?;
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        for effect_index in &effect_indices {
            let claim = FunctionClaimRef::Effect(
                *effect_index,
                &context.function_block.effects()[*effect_index],
            );
            validate_function_frame_tactic(
                checked_execution,
                &claim,
                context.claim_label,
                origin.map_or(context.tactic_index, |origin| origin.tactic_index),
                context.parsed_function.parameters(),
                context.arguments,
                &pre_state,
                &frame_facts,
            )?;
        }

        let origin = origin.unwrap_or(ProofStepOrigin {
            tactic_index: context.tactic_index,
            source_index: context.tactic_index,
        });
        execution.replay.defer_checked_post_execution(
            origin.tactic_index,
            origin.source_index,
            PostExecutionTactic::CheckedFrameUsing {
                authority: CheckedFrameAuthority::new(effect_indices),
                region: region.cloned(),
                premises: premises.to_vec(),
                surface_tactics: None,
            },
        );
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(
                self.focused,
                Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context: GoalContext {
                        facts: self.facts().clone(),
                        unfolded_predicates: self.focused_goal_unfolds().clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
            ),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Applies a planner-selected contextual frame tree directly to this
    /// Proof. The plan carries only Surface operations and branch shape; it
    /// owns no facts, execution state, or semantic successor authority.
    pub(super) fn apply_contextual_frame_plan(
        &self,
        plan: &ContextualFramePlan,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        let ContextualFramePlan::If {
            condition,
            then_plan,
            else_plan,
        } = plan
        else {
            let ContextualFramePlan::Leaf(leaf) = plan else {
                unreachable!()
            };
            return self.apply_contextual_frame_leaf_plan(leaf, origin);
        };
        let (split, record) = self.split_focused_outcome_if(condition.clone())?;
        let advanced = split
            .focus_outcome_arm(&record, 0)?
            .apply_contextual_frame_plan(then_plan, origin)?
            .focus_outcome_arm(&record, 1)?
            .apply_contextual_frame_plan(else_plan, origin)?;
        advanced.join_focused_outcome_if(&record)
    }

    pub(super) fn apply_contextual_frame_leaf_plan(
        &self,
        plan: &ContextualFrameLeafPlan,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        let mut checked = self.clone();
        for have in &plan.haves {
            let scope = checked.begin_have(have.proposition.clone())?;
            let Some(scope) = scope.try_planned_linear_script(&have.tactics)? else {
                return Err(checked.step_error(
                    "contextual frame `have` plan did not complete through checked Proof operations",
                ));
            };
            checked = scope.join()?;
        }
        checked.apply_step_with_origin(
            SimpleProofStep::FrameUsing {
                region: None,
                premises: plan.premises.clone(),
            },
            origin,
        )
    }

    /// Recovers only the latest checked branch shape from persistent Proof
    /// provenance. Contextual-frame search needs this path partition, not a
    /// materialized certificate for the complete derivation.
    pub(super) fn contextual_frame_skeleton(&self) -> ContextualFrameSkeleton {
        let mut node = Some(self.node.as_ref());
        while let Some(current) = node {
            if let Some(step) = current.step.as_deref() {
                if matches!(step, SimpleProofStep::If { .. }) {
                    return ContextualFrameSkeleton::from_steps(std::slice::from_ref(step));
                }
            }
            node = current.parent.as_deref();
        }
        ContextualFrameSkeleton::Leaf
    }

    /// Uses the contextual footprint planner only to select a typed tree of
    /// Surface operations. The plan has performed no semantic transition and
    /// contains no certificate builder or replay-owned proof state.
    pub(super) fn select_contextual_frame_candidate(
        &self,
    ) -> Result<Option<ContextualFramePlan>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let execution_state = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if !execution_state.replay.is_at_function_exit()
            || !execution_state.replay.case_assumptions.is_empty()
        {
            return Ok(None);
        }
        let effect_indices = self.selected_effect_indices(context)?;
        let execution = execution_state.replay.execution().ok_or_else(|| {
            self.step_error("function-exit proof has no checked execution outcomes")
        })?;
        let path_independent_only = self.node.depth == 0
            && (execution.paths().len() > 1
                || execution_state.replay.has_structured_branch_history);
        let available = self.facts().to_vec();
        let pre_state = execution_state
            .replay
            .old_reference_state(&execution_state.state);
        let mut path_derivations = Vec::with_capacity(execution.paths().len());
        for (path_index, path) in execution.paths().iter().enumerate() {
            if !path.obligations().is_empty() {
                return Err(self.step_error(
                    "`frame` cannot plan from an execution path with unresolved obligations",
                ));
            }
            let mut path_facts = available.clone();
            path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let implicit_path_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let mut combined = Vec::new();
            for effect_index in &effect_indices {
                for derivation in plan_effect_clause_derivations(
                    context.claim_label,
                    path_index,
                    path.effect_facts(),
                    &path_facts,
                    &implicit_path_facts,
                    context.function_block.effects()[*effect_index].effect(),
                    context.parsed_function.parameters(),
                    context.arguments,
                    pre_state,
                    path.outcome(),
                )? {
                    if !combined.contains(&derivation) {
                        combined.push(derivation);
                    }
                }
            }
            path_derivations.push(combined);
        }
        let skeleton = self.contextual_frame_skeleton();
        let mut construction_replay = execution_state.replay.clone();
        let mut branch_conditions = Vec::new();
        skeleton.collect_conditions(&mut branch_conditions);
        for condition in &branch_conditions {
            let negated = ClickProposition::Not(Box::new(condition.clone()));
            let mut surface_forms = vec![condition.clone(), negated.clone()];
            for candidate in [
                reverse_surface_comparison(condition),
                reverse_surface_comparison(&negated),
            ]
            .into_iter()
            .flatten()
            {
                if !surface_forms.contains(&candidate) {
                    surface_forms.push(candidate);
                }
            }
            for (path_index, path) in execution.paths().iter().enumerate() {
                let CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                } = path.outcome()
                else {
                    return Err(self.step_error(format!(
                        "execution path {path_index} cannot decide a proof branch without a return outcome"
                    )));
                };
                let mut path_facts = available.clone();
                path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                for surface in &surface_forms {
                    let kernel = lower_outcome_proposition_with_program_points(
                        context.parsed_function.parameters(),
                        context.arguments,
                        pre_state,
                        post_state,
                        result,
                        &path_facts,
                        surface,
                        context.predicate_environment,
                        context.click_function_environment,
                        &execution_state.replay.program_point_states,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not lower execution outcome branch condition: {message}"
                        ))
                    })?;
                    construction_replay
                        .surface_propositions
                        .record_lowering(surface, &kernel)?;
                }
            }
        }
        let path_tactics = lower_certified_frame_path_tactics(
            &mut construction_replay,
            &execution_state.state,
            &available,
            context.parsed_function.parameters(),
            context.arguments,
            context.predicate_environment,
            context.click_function_environment,
            &path_derivations,
        )
        .map_err(|error| {
            self.step_error(format!(
                "smart frame candidate construction failed: could not lower contextual frame plan: {}",
                error.message()
            ))
        })?;
        // A compatibility root created after a legacy branch owns the
        // outcomes but not the branch Proof that partitions them. It may
        // still check one plan shared by every path; a path-dependent plan
        // declines here instead of inventing missing branch lineage.
        contextual_frame_plan(skeleton, path_tactics, path_independent_only).map_err(|message| {
            self.step_error(format!(
                "smart frame candidate construction failed: {message}"
            ))
        })
    }

    /// Reports whether a source-owned terminal frame can advance this exact
    /// checked Proof. This is a capability query only; a false result leaves
    /// the proof unchanged so a larger transactional Proof attempt can
    /// decline without publishing a partial transition.
    pub(in crate::lang::click::proof) fn supports_checked_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        self.supports_checked_execution_frame_using(region, premises)
    }

    /// Applies one source-attributed simple step to this Proof. The source
    /// coordinates schedule already-checked ordered outcome work; they grant
    /// no additional semantic authority.
    pub(in crate::lang::click::proof) fn apply_step_at(
        &self,
        step: SimpleProofStep,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )
    }

    /// Searches for a terminal frame candidate and submits the selected
    /// Surface-operation plan directly to this Proof. Successful search returns
    /// the already-checked descendant; it does not export outcomes or replay
    /// the candidate through a second semantic representation.
    pub(in crate::lang::click::proof) fn try_smart_frame_at(
        &self,
        region: Option<&CodeRegionRef>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(region) = region {
            let step = SimpleProofStep::FrameUsing {
                region: Some(region.clone()),
                premises: Vec::new(),
            };
            return self
                .apply_step_at(step, tactic_index, source_index)
                .map(Some);
        }
        if matches!(
            self.focused_goal(),
            Some(Goal::Frontier(FrontierGoal {
                selection: EffectGoalSelection::None,
                ..
            }))
        ) {
            return Ok(None);
        }
        let step = SimpleProofStep::FrameUsing {
            region: None,
            premises: Vec::new(),
        };
        match self.apply_step_at(step, tactic_index, source_index) {
            Ok(framed) => return Ok(Some(framed)),
            Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
            Err(_) => {}
        }
        // If the exact empty operation cannot prove the selected effect, use
        // contextual search to select explicit premises and leading haves.
        let Some(candidate) = self.select_contextual_frame_candidate()? else {
            return Ok(None);
        };
        let origin = Some(ProofStepOrigin {
            tactic_index,
            source_index,
        });
        match self.apply_contextual_frame_plan(&candidate, origin) {
            Ok(checked) => Ok(Some(checked)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    /// Selects exact premises for a smart loop structural frame from facts
    /// indexed under C names used by that loop body. Candidate work is bounded
    /// by the affected source operation and its relevant indexed facts; no
    /// ambient fact scan or semantic replay participates.
    pub(in crate::lang::click::proof) fn try_smart_loop_effect_frame_at(
        &self,
        body: &CStatement,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let execution = self.execution().ok_or_else(|| {
            self.step_error("smart loop framing requires an execution-frontier Proof")
        })?;
        execution.replay.loop_effect_goal.as_ref().ok_or_else(|| {
            self.step_error("smart loop framing requires a structural effect goal")
        })?;
        let mut dependency_names = BTreeSet::new();
        collect_statement_variable_names(body, &mut dependency_names);
        let mut candidates = BTreeSet::new();
        for name in dependency_names {
            for kernel in execution
                .replay
                .surface_propositions
                .current_c_variable_kernel_facts(&name)
            {
                if self
                    .facts()
                    .replay_available_across_effects(kernel, &execution.replay.effect_facts)
                {
                    candidates.insert(kernel.clone());
                }
            }
        }
        let mut premises = Vec::with_capacity(candidates.len());
        #[cfg(test)]
        SMART_LOOP_EFFECT_FRAME_CANDIDATES.with(|count| count.set(count.get() + candidates.len()));
        for kernel in candidates {
            let Some(surface) = self.loop_effect_surface_premise(&kernel) else {
                continue;
            };
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }
        let selected = SimpleProofStep::FrameUsing {
            region: None,
            premises,
        };
        match self.apply_step_at(selected, tactic_index, source_index) {
            Ok(checked) => Ok(Some(checked)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    pub(super) fn loop_effect_surface_premise(
        &self,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let execution = self.execution()?;
        let matches = |surface: &ClickProposition| {
            let lowered = execution
                .replay
                .surface_propositions
                .available_kernel_matching(surface, |candidate| {
                    self.facts()
                        .replay_available_across_effects(candidate, &execution.replay.effect_facts)
                })
                .cloned()
                .or_else(|| {
                    self.lower_surface_proposition_direct(surface, "smart loop frame premise")
                        .ok()
                });
            lowered.is_some_and(|lowered| {
                lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)
            })
        };
        if let Some(surface) = execution
            .replay
            .surface_propositions
            .surfaces(kernel)
            .find(|surface| matches(surface))
        {
            return Some(surface.clone());
        }
        let surface = synthesize_surface_proposition(
            kernel,
            context.parsed_function.parameters(),
            context.arguments,
            &execution.state,
        )?;
        matches(&surface).then_some(surface)
    }

    // Each primitive rule stays outlined so adding a rule-local proposition
    // payload cannot enlarge every `apply_step` dispatch frame. This is part
    // of the expansion replay stack budget documented in testing-click.md.
    #[inline(never)]
    pub(super) fn apply_assumption(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`assumption` requires a proposition goal")?;
        let available = match self.context.as_ref() {
            ProofContext::Point(_) => {
                self.facts().pure_replay_available(goal) || normalizes_context_free(goal)
            }
            // A judgment stated at a function outcome closes with the same
            // point-level replay availability its legacy point root used.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                self.facts().pure_replay_available(goal) || normalizes_context_free(goal)
            }
            ProofContext::Pure(_) | ProofContext::Execution(_) => self.facts().contains(goal),
        };
        if !available {
            return Err(self
                .step_error("`assumption` requires the exact current goal as an available fact"));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_normalize(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`normalize` requires a proposition goal")?;
        if !normalizes_context_free(goal) {
            return Err(self.step_error("`normalize` goal did not normalize to true"));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    pub(super) fn apply_intro(&self) -> Result<ProofState, ClickError> {
        let goal = self
            .proposition_goal("`intro` requires a proposition goal")?
            .clone();
        let mut surface_bindings = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => goal.surface_bindings.clone(),
            _ => PersistentMap::default(),
        };
        let (goal, introduced, surface_goal) = match goal {
            Proposition::Implies(antecedent, consequent) => (
                *consequent,
                Some(*antecedent),
                match self.surface_goal() {
                    Some(ClickProposition::Implies(_, consequent)) => {
                        Some(consequent.as_ref().clone())
                    }
                    _ => None,
                },
            ),
            Proposition::ForAll { var, body, .. } => {
                let surface_goal = match self.surface_goal() {
                    Some(ClickProposition::ForAll { name, body, .. }) => {
                        surface_bindings = surface_bindings.with_inserted(
                            name.clone(),
                            ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                                Bitvector32Term::Variable(var),
                            ))),
                        );
                        Some(body.as_ref().clone())
                    }
                    _ => None,
                };
                (*body, None, surface_goal)
            }
            Proposition::Not(body) => (
                Proposition::ConditionIs(ConditionTerm::Constant(false), true),
                Some(*body),
                None,
            ),
            other => {
                return Err(self.step_error(format!(
                    "`intro` requires an implication, negation, or universal goal, got {other:?}"
                )));
            }
        };
        let mut facts = self.facts().clone();
        let added_facts = introduced.into_iter().collect::<Vec<_>>();
        for fact in &added_facts {
            facts = facts.with_fact(fact.clone());
        }
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(self.focused, {
                let context = self.refined_context(facts);
                let mut refined = self.refined_proposition(context, goal, surface_goal);
                let Goal::Proposition(refined_goal) = &mut refined else {
                    unreachable!("intro always refines a proposition goal")
                };
                refined_goal.surface_bindings = surface_bindings;
                refined
            }),
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
        })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_split(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`split` requires a proposition goal")?;
        let Proposition::And(left, right) = goal else {
            return Err(
                self.step_error(format!("`split` requires a conjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(left) || !self.facts().contains(right) {
            return Err(self.step_error(format!(
                "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_left(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`left` requires a proposition goal")?;
        let Proposition::Or(left, _) = goal else {
            return Err(
                self.step_error(format!("`left` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(left)
            && !condition_polarity_forms(left)
                .iter()
                .any(|form| self.facts().contains(form))
        {
            return Err(self.step_error(format!(
                "`left` requires its selected disjunct as an exact fact: {left:?}"
            )));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_right(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`right` requires a proposition goal")?;
        let Proposition::Or(_, right) = goal else {
            return Err(
                self.step_error(format!("`right` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(right)
            && !condition_polarity_forms(right)
                .iter()
                .any(|form| self.facts().contains(form))
        {
            return Err(self.step_error(format!(
                "`right` requires its selected disjunct as an exact fact: {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above; instance
    // materialization is local to this rule.
    #[inline(never)]
    pub(super) fn apply_enumerate(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`enumerate` requires a proposition goal")?;
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Err(
                self.step_error("`enumerate` requires a universal goal with constant bounds")
            );
        };
        for (_, instance) in instances {
            if !normalizes_context_free(&instance) && !self.facts().contains(&instance) {
                return Err(self.step_error(
                    "`enumerate` requires each in-range instance as an exact available fact",
                ));
            }
        }
        Ok(self.closed_state())
    }
}
