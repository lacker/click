//! Simple-step dispatch (`apply_step`) and checked frame application.

use super::*;

impl<'a> Proof<'a> {
    /// Checks one explicit proof step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(in crate::surface::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, None)
    }

    /// Applies a step while retaining its source occurrence for any ordered
    /// terminal work the checked transition has to schedule. The source site
    /// affects diagnostics and finalization order only; the certificate node
    /// remains exactly the supplied `ProofStep`.
    pub(super) fn apply_step_with_origin(
        &self,
        step: ProofStep,
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
        step: ProofStep,
        origin: Option<ProofStepOrigin>,
        retain_closed_loop_effect_goal: bool,
    ) -> Result<Self, ClickError> {
        if self.focused_discharged() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                proof_step_source_name(&step)
            )));
        }
        if self.focused_loop_effect_closed() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                proof_step_source_name(&step)
            )));
        }

        if let ProofStep::Have { proposition, proof } = &step {
            return self.apply_have_step(proposition, proof);
        }
        if let ProofStep::Step = &step {
            return self.apply_execution_statement_step(step);
        }

        let checked_proposition_successor = match &step {
            ProofStep::Assumption => Some(self.apply_assumption()),
            ProofStep::Normalize => Some(self.apply_normalize()),
            ProofStep::ArithmeticUsing(premises) => Some(self.apply_arithmetic_using(premises)),
            ProofStep::Intro => Some(self.apply_intro()),
            ProofStep::Split => Some(self.apply_split()),
            ProofStep::Left => Some(self.apply_left()),
            ProofStep::Right => Some(self.apply_right()),
            ProofStep::Enumerate => Some(self.apply_enumerate()),
            ProofStep::Contradiction(surface) => Some(self.apply_contradiction(surface)),
            ProofStep::Extract(proposition) => Some(self.apply_extract(proposition)),
            ProofStep::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => Some(self.apply_fixed_state_instantiate_using(quantified, argument, premises)),
            ProofStep::Mark(name) => Some(self.apply_execution_mark(name)),
            ProofStep::CloseInvariants => Some(self.apply_close_invariants()),
            _ => None,
        };
        if let Some(successor) = checked_proposition_successor {
            return Ok(Self {
                context: self.context.clone(),
                state: successor?,
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: Some(Arc::new(step)),
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth + 1,
                }),
            });
        }

        let transition = match &step {
            ProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            ProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            ProofStep::UnfoldPredicate(name) => self.apply_predicate_unfold(name),
            ProofStep::UnfoldFunction(application) => self.apply_function_unfold(application),
            ProofStep::UnfoldResource(resource) => self.apply_execution_resource_unfold(resource),
            ProofStep::FoldResource(resource) => {
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_fold(resource)
                } else {
                    self.apply_execution_resource_fold(resource)
                }
            }
            ProofStep::ObserveResource(resource) => {
                self.apply_execution_resource_observation(resource)
            }
            ProofStep::Choose(choice) => self.apply_fixed_state_choose(choice),
            ProofStep::Witness(witness) => self.apply_fixed_state_witness(witness),
            ProofStep::Rewrite(equality) => self.apply_rewrite(equality),
            ProofStep::FrameUsing { region, premises } => {
                if self.focused_outcome_data().is_some() {
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
                    .step_error("this proof step has not yet migrated to the checked `Proof` API"))
            }
        }?;

        Ok(Self {
            context: self.context.clone(),
            state: self.publish_checked_transition(transition)?,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth + 1,
            }),
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
        let selection = match self.focused_obligation() {
            Some(Obligation::Frontier(FrontierObligation { selection, .. })) => *selection,
            Some(Obligation::FunctionOutcome(outcome)) => outcome.selection,
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
    /// so this capability query must decline rather than precheck one after
    /// earlier smart operations. An authoritative Proof unit applies the exact
    /// step directly instead of consulting this compatibility query.
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
        // A frontier without an effect goal cannot check a function frame;
        // that is a decline, not a checking error.
        if !self.frontier_owns_effect_goal() {
            return Ok(false);
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
    /// proof-step dispatcher frame; the expansion small-stack test pins that
    /// dispatch budget.
    #[inline(never)]
    pub(super) fn apply_outcome_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`frame using` requires an execution proof"));
        };
        if !matches!(region, None | Some(CodeRegionRef::Function)) {
            return Err(
                self.step_error("a result-aware `frame using` can close only the function effect")
            );
        }
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("result-aware `frame using` requires an outcome goal"));
        };
        let effect_indices = self.selected_effect_indices(context)?;
        let execution = self
            .focused_branch()
            .expect("focused branch exists")
            .state
            .execution
            .as_deref()
            .ok_or_else(|| {
                self.step_error("result-aware `frame using` lost its execution snapshot")
            })?;
        let pre_state = execution
            .core
            .frontier
            .execution_start_state(&execution.core.state);

        let mut data = (*goal.data).clone();
        let mut frame_facts = Vec::with_capacity(premises.len());
        for surface in premises {
            let fact = data
                .surface_propositions
                .available_kernel_matching(surface, |kernel| {
                    self.facts()
                        .available_across_effects(kernel, &execution.core.effect_facts)
                })
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    self.lower_surface_proposition(surface, "`frame using` premise")
                })?;
            // Availability is the same rule a statement step uses for its
            // prerequisites: an available fact across the recorded effects,
            // or a resource-shaped fact derived atomically from the context.
            let available = |fact: &Proposition| {
                self.facts()
                    .available_across_effects(fact, &execution.core.effect_facts)
                    || (matches!(
                        fact,
                        Proposition::CResourceContains { .. }
                            | Proposition::CResourceSeparate { .. }
                            | Proposition::CMemoryLoadable { .. }
                    ) && self
                        .facts()
                        .assumptions()
                        .derive_atomic_proposition(fact)
                        .is_some())
            };
            // An unanchored premise reads at the outcome; a fact observed in
            // an earlier recorded snapshot (a resource's body fact at a
            // call's exit) is the same surface read there. Try each recorded
            // snapshot before rejecting; this is bounded by the recorded
            // snapshots.
            let fact = if available(&fact) {
                fact
            } else {
                execution
                    .presentation
                    .recorded_snapshots
                    .keys()
                    .filter_map(|selector| execution.presentation.recorded_snapshots.get(selector))
                    .filter_map(|snapshot_state| {
                        lower_fixed_state_proposition_with_assumptions(
                            surface,
                            self.facts().assumptions(),
                            context.parsed_function.parameters(),
                            context.arguments,
                            pre_state,
                            snapshot_state,
                            None,
                            &execution.presentation.recorded_snapshots,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .ok()
                    })
                    .find(|candidate| available(candidate))
                    .unwrap_or(fact)
            };
            if !available(&fact) {
                return Err(self.step_error(format!(
                    "outcome `frame using` requires an exact available premise: {surface:?} lowered to {fact:?}"
                )));
            }
            data.surface_propositions.record_lowering(surface, &fact)?;
            if !frame_facts.contains(&fact) {
                frame_facts.push(fact);
            }
        }

        let mut outcome = CFunctionOutcome::Return {
            value: (*data.core.result).clone(),
            state: (*data.core.state).clone(),
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
                &data.core.effect_facts,
                &frame_facts,
                &claim,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                &outcome,
            )?;
        }

        let mut assumptions = self.facts().assumptions().clone();
        for fact in data.core.effect_facts.iter() {
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
        data.core.result = Arc::new(value);
        data.core.state = state.into();
        let mut updated = goal.clone();
        updated.selection = EffectGoalSelection::None;
        updated.checked_effects = Arc::new(effect_indices);
        updated.data = Arc::new(data);
        let branch = self
            .focused_branch()
            .expect("an outcome frame transition requires an open branch")
            .with_obligation(Obligation::FunctionOutcome(updated));
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(branch),
            Vec::new(),
            frame_facts,
        ))
    }

    #[inline(never)]
    pub(super) fn apply_execution_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
        origin: Option<ProofStepOrigin>,
        retain_closed_loop_effect_goal: bool,
    ) -> Result<CheckedFocusedTransition, ClickError> {
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
                .presentation
                .surface_propositions
                .available_kernel_matching(surface, |kernel| {
                    self.facts()
                        .available_across_effects(kernel, &execution.core.effect_facts)
                })
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    self.lower_surface_proposition(surface, "`frame using` premise")
                })?;
            if !self
                .facts()
                .available_across_effects(&fact, &execution.core.effect_facts)
            {
                return Err(self.step_error(format!(
                    "`frame using` requires an exact available premise: {surface:?} lowered to {fact:?}"
                )));
            }
            execution
                .presentation
                .surface_propositions
                .record_lowering(surface, &fact)?;
            if !frame_facts.contains(&fact) {
                frame_facts.push(fact);
            }
        }
        if execution.core.loop_effect_goal.is_some() {
            if region.is_some() {
                return Err(
                    self.step_error("a structural effect proof must use unqualified `frame using`")
                );
            }
            let goal = execution
                .core
                .loop_effect_goal
                .as_ref()
                .expect("the loop effect goal was observed above");
            if goal.closed {
                return Err(self.step_error("the structural effect goal was closed more than once"));
            }
            let mut loop_effect_facts = frame_facts.clone();
            loop_effect_facts.extend(
                execution
                    .core
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            loop_effect_facts.extend(self.facts().memory_effect_summaries().cloned());
            loop_effect_facts.sort();
            loop_effect_facts.dedup();
            c_loop_effects_hold_at_back_edge(
                &goal.before_state,
                &execution.core.state,
                std::slice::from_ref(&goal.check),
                &loop_effect_facts,
                &assumptions_from_propositions(&loop_effect_facts),
            )
            .map_err(|message| self.step_error(format!("`frame using` failed: {message}")))?;
            execution
                .core
                .loop_effect_goal
                .as_mut()
                .expect("the checked loop effect goal remains present")
                .closed = true;
            let branch = if retain_closed_loop_effect_goal {
                let mut state = self.refined_branch_state(self.facts().clone());
                state.execution = Some(Arc::new(execution));
                Some(
                    self.focused_branch()
                        .expect("a retained loop effect transition requires an open branch")
                        .with_state(state),
                )
            } else {
                None
            };
            return Ok(CheckedFocusedTransition::replacing(
                self.state().locals().clone(),
                branch,
                Vec::new(),
                frame_facts,
            ));
        }
        if !execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("`frame using` requires function exit"));
        }
        if let Some(region) = region {
            // Loop effect clauses are declared by frontier-local `loop`
            // tactics. Bind the exact clauses already checked on this check
            // before resolving labels or validating the qualified frame.
            let frame_function_block = (!execution.presentation.frontier_loop_clauses.is_empty())
                .then(|| {
                    context.function_block.with_bound_frontier_loop_clauses(
                        &execution.presentation.frontier_loop_clauses.to_vec(),
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
                execution.presentation.defer_checked_post_execution(
                    origin.tactic_index,
                    origin.source_index,
                    PostExecutionTactic::FrameRegion(region.clone()),
                );
                return Ok(self.checked_execution_transition(
                    self.facts().clone(),
                    false,
                    execution,
                    Vec::new(),
                    Vec::new(),
                ));
            }
        }

        let effect_indices = self.selected_effect_indices(context)?;

        let checked_execution = execution.core.frontier.execution().ok_or_else(|| {
            self.step_error("function-exit proof has no checked execution outcomes")
        })?;
        let pre_state = context
            .old_reference_state(&execution.core.frontier, &execution.core.state)
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
        execution.presentation.defer_checked_post_execution(
            origin.tactic_index,
            origin.source_index,
            PostExecutionTactic::CheckedFrameUsing {
                authority: CheckedFrameAuthority::new(effect_indices),
                region: region.cloned(),
                premises: premises.to_vec(),
                surface_tactics: None,
            },
        );
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(OpenBranch::frontier(
                EffectGoalSelection::None,
                BranchState {
                    facts: self.facts().clone(),
                    unfolded_predicates: self.focused_branch_unfolds().clone(),
                    execution: Some(Arc::new(execution)),
                },
            )),
            Vec::new(),
            Vec::new(),
        ))
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
            ProofStep::FrameUsing {
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
                if matches!(step, ProofStep::If { .. }) {
                    return ContextualFrameSkeleton::from_steps(std::slice::from_ref(step));
                }
            }
            node = current.parent.as_deref();
        }
        ContextualFrameSkeleton::Leaf
    }

    /// Uses the contextual footprint planner only to select a typed tree of
    /// Surface operations. The plan has performed no semantic transition and
    /// contains no certificate builder or parallel proof state.
    pub(super) fn select_contextual_frame_candidate(
        &self,
    ) -> Result<Option<ContextualFramePlan>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let execution_state = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if !execution_state.core.frontier.is_at_function_exit()
            || !execution_state.case_assumptions.is_empty()
        {
            return Ok(None);
        }
        let effect_indices = self.selected_effect_indices(context)?;
        let execution = execution_state.core.frontier.execution().ok_or_else(|| {
            self.step_error("function-exit proof has no checked execution outcomes")
        })?;
        let path_independent_only = self.node.depth == 0
            && (execution.paths().len() > 1 || execution_state.core.has_structured_branch_history);
        let available = self.facts().to_vec();
        let pre_state = context
            .old_reference_state(&execution_state.core.frontier, &execution_state.core.state);
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
        let mut construction_surface = execution_state.surface_propositions.clone();
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
                    let kernel = lower_outcome_proposition_with_recorded_snapshots(
                        context.parsed_function.parameters(),
                        context.arguments,
                        pre_state,
                        post_state,
                        result,
                        &path_facts,
                        surface,
                        context.predicate_environment,
                        context.click_function_environment,
                        &execution_state.recorded_snapshots,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not lower execution outcome branch condition: {message}"
                        ))
                    })?;
                    construction_surface.record_lowering(surface, &kernel)?;
                }
            }
        }
        let path_tactics = lower_certified_frame_path_tactics(
            &mut construction_surface,
            &execution_state.core.frontier,
            &execution_state.core.effect_facts,
            &execution_state.recorded_snapshots,
            context,
            &execution_state.core.state,
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

    /// Applies one source-attributed proof step to this Proof. The source
    /// coordinates schedule already-checked ordered outcome work; they grant
    /// no additional semantic authority.
    pub(in crate::surface::proof) fn apply_step_at(
        &self,
        step: ProofStep,
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
    /// the already-checked descendant; it does not export outcomes or check
    /// the candidate through a second semantic representation.
    pub(in crate::surface::proof) fn try_smart_frame_at(
        &self,
        region: Option<&CodeRegionRef>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(region) = region {
            let step = ProofStep::FrameUsing {
                region: Some(region.clone()),
                premises: Vec::new(),
            };
            return self
                .apply_step_at(step, tactic_index, source_index)
                .map(Some);
        }
        if matches!(
            self.focused_obligation(),
            Some(Obligation::Frontier(FrontierObligation {
                selection: EffectGoalSelection::None,
                ..
            }))
        ) {
            return Ok(None);
        }
        let step = ProofStep::FrameUsing {
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
    /// ambient fact scan or semantic check participates.
    pub(in crate::surface::proof) fn try_smart_loop_effect_frame_at(
        &self,
        body: &CStatement,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let execution = self.execution().ok_or_else(|| {
            self.step_error("smart loop framing requires an execution-frontier Proof")
        })?;
        execution.core.loop_effect_goal.as_ref().ok_or_else(|| {
            self.step_error("smart loop framing requires a structural effect goal")
        })?;
        let mut dependency_names = BTreeSet::new();
        collect_statement_variable_names(body, &mut dependency_names);
        let mut candidates = BTreeSet::new();
        // The body's C variables denote kernel values here: a local's current
        // value or a parameter's argument. Context facts about those values
        // are the frame's candidate premises; the checked frame decides.
        let mut value_keys = Vec::new();
        for name in &dependency_names {
            for kernel in execution
                .presentation
                .surface_propositions
                .current_c_variable_kernel_facts(name)
            {
                if self
                    .facts()
                    .available_across_effects(kernel, &execution.core.effect_facts)
                {
                    candidates.insert(kernel.clone());
                }
            }
            let ProofContext::Execution(context) = self.context.as_ref() else {
                continue;
            };
            let value = execution
                .core
                .state
                .locals()
                .object_values()
                .find(|(local, _)| local == name)
                .map(|(_, value)| format!("{value:?}"))
                .or_else(|| {
                    context
                        .parsed_function
                        .parameters()
                        .iter()
                        .position(|parameter| parameter.name() == name)
                        .and_then(|index| context.arguments.get(index))
                        .map(|argument| format!("{argument:?}"))
                });
            if let Some(value) = value {
                for key in kernel_variable_keys(&value) {
                    if !value_keys.contains(&key) {
                        value_keys.push(key);
                    }
                }
            }
        }
        if !value_keys.is_empty() {
            for fact in self.facts().to_vec() {
                if !matches!(
                    fact,
                    Proposition::ConditionIs(_, _)
                        | Proposition::And(_, _)
                        | Proposition::CMemoryLoadable { .. }
                        | Proposition::CResourceSeparate { .. }
                ) || candidates.contains(&fact)
                {
                    continue;
                }
                let rendered = format!("{fact:?}");
                if value_keys.iter().any(|key| rendered.contains(key.as_str())) {
                    // A conjunction invariant is available leaf by leaf.
                    fn leaves(fact: &Proposition, out: &mut Vec<Proposition>) {
                        match fact {
                            Proposition::And(left, right) => {
                                leaves(left, out);
                                leaves(right, out);
                            }
                            fact => out.push(fact.clone()),
                        }
                    }
                    let mut atoms = Vec::new();
                    leaves(&fact, &mut atoms);
                    for atom in atoms {
                        if self
                            .facts()
                            .available_across_effects(&atom, &execution.core.effect_facts)
                        {
                            candidates.insert(atom);
                        }
                    }
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
        let selected = ProofStep::FrameUsing {
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
                .presentation
                .surface_propositions
                .available_kernel_matching(surface, |candidate| {
                    self.facts()
                        .available_across_effects(candidate, &execution.core.effect_facts)
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
            .presentation
            .surface_propositions
            .surfaces(kernel)
            .find(|surface| matches(surface))
        {
            return Some(surface.clone());
        }
        if let Some(surface) = synthesize_surface_proposition(
            kernel,
            context.parsed_function.parameters(),
            context.arguments,
            &execution.core.state,
        ) && matches(&surface)
        {
            return Some(surface);
        }
        // A fact about an earlier value of a body variable denotes at the
        // recorded entry of the statement that read it.
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
            kind: ProgramPointKind::Entry,
        };
        let candidates = super::super::smart_closures::synthesize_surface_at_recorded_snapshots(
            kernel,
            context.parsed_function.parameters(),
            context.arguments,
            &execution.presentation.recorded_snapshots,
            &anchor,
        );
        candidates.into_iter().find(|surface| matches(surface))
    }

    // Each primitive rule stays outlined so adding a rule-local proposition
    // payload cannot enlarge every `apply_step` dispatch frame. This is part
    // of the expansion check stack budget documented in testing-click.md.
    #[inline(never)]
    pub(super) fn apply_assumption(&self) -> Result<KernelProofHandle, ClickError> {
        let context = match self.context.as_ref() {
            ProofContext::FixedState(_) => PropositionAssumptionContext::Pure,
            ProofContext::Execution(_) => PropositionAssumptionContext::Materialized,
            ProofContext::Pure(_) => PropositionAssumptionContext::Exact,
        };
        self.state
            .apply_assumption(context)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`assumption` requires a proposition goal")
                }
                PropositionCloseError::Unavailable => self.step_error(
                    "`assumption` requires the current goal as an available semantic fact",
                ),
                _ => unreachable!("kernel returned an unrelated assumption error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_normalize(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_normalize().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`normalize` requires a proposition goal")
            }
            PropositionCloseError::DoesNotNormalize => {
                self.step_error("`normalize` goal did not normalize to true")
            }
            _ => unreachable!("kernel returned an unrelated normalize error"),
        })
    }

    #[inline(never)]
    pub(super) fn apply_arithmetic_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<KernelProofHandle, ClickError> {
        let premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "`arithmetic using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        self.state
            .apply_arithmetic(&premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`arithmetic` requires a proposition goal")
                }
                PropositionCloseError::ArithmeticPremiseUnavailable(index) => self.step_error(
                    format!("`arithmetic using` premise {index} is not exactly available"),
                ),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::UnsupportedGoal,
                ) => self.step_error(
                    "`arithmetic` requires an atomic signed-affine int32 comparison goal",
                ),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::UnsupportedPremise(
                        index,
                    ),
                ) => self.step_error(format!(
                    "`arithmetic using` premise {index} is not a signed-affine int32 comparison"
                )),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::GoalMayBeUndefined,
                ) => self.step_error(
                    "`arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises",
                ),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::DoesNotFollow,
                ) => self.step_error(
                    "the current goal does not follow from exactly the listed arithmetic premises",
                ),
                _ => unreachable!("kernel returned an unrelated arithmetic error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    pub(super) fn apply_intro(&self) -> Result<KernelProofHandle, ClickError> {
        self.state
            .apply_intro(|current, introduction| {
                let mut surface_bindings = current.surface_bindings.clone();
                let surface = match (introduction, current.surface.as_deref()) {
                    (
                        PropositionIntroduction::Implication,
                        Some(ClickProposition::Implies(_, consequent)),
                    ) => Some(Arc::new(consequent.as_ref().clone())),
                    (
                        PropositionIntroduction::Universal { variable },
                        Some(ClickProposition::ForAll { name, body, .. }),
                    ) => {
                        surface_bindings = surface_bindings.with_inserted(
                            name.clone(),
                            ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                                Bitvector32Term::Variable(variable),
                            ))),
                        );
                        Some(Arc::new(body.as_ref().clone()))
                    }
                    _ => None,
                };
                PropositionPresentation {
                    surface,
                    surface_bindings,
                }
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`intro` requires a proposition goal")
                }
                PropositionCloseError::ExpectedIntroduction(goal) => self.step_error(format!(
                    "`intro` requires an implication, negation, or universal goal, got {goal:?}"
                )),
                _ => unreachable!("kernel returned an unrelated intro error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_split(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_split().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`split` requires a proposition goal")
            }
            PropositionCloseError::ExpectedConjunction(goal) => {
                self.step_error(format!("`split` requires a conjunction goal, got {goal:?}"))
            }
            PropositionCloseError::MissingConjuncts(left, right) => self.step_error(format!(
                "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
            )),
            _ => unreachable!("kernel returned an unrelated split error"),
        })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_left(&self) -> Result<KernelProofHandle, ClickError> {
        self.apply_disjunct(true, "left")
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_right(&self) -> Result<KernelProofHandle, ClickError> {
        self.apply_disjunct(false, "right")
    }

    fn apply_disjunct(
        &self,
        take_left: bool,
        step_name: &str,
    ) -> Result<KernelProofHandle, ClickError> {
        self.state
            .apply_disjunct(take_left)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error(format!("`{step_name}` requires a proposition goal"))
                }
                PropositionCloseError::ExpectedDisjunction(goal) => self.step_error(format!(
                    "`{step_name}` requires a disjunction goal, got {goal:?}"
                )),
                PropositionCloseError::MissingDisjunct(selected) => self.step_error(format!(
                    "`{step_name}` requires its selected disjunct as an exact fact: {selected:?}"
                )),
                _ => unreachable!("kernel returned an unrelated disjunction error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above; instance
    // materialization is local to this rule.
    #[inline(never)]
    pub(super) fn apply_enumerate(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_enumerate().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`enumerate` requires a proposition goal")
            }
            PropositionCloseError::ExpectedFiniteUniversal => {
                self.step_error("`enumerate` requires a universal goal with constant bounds")
            }
            PropositionCloseError::MissingFiniteInstance => self.step_error(
                "`enumerate` requires each in-range instance as an exact available fact",
            ),
            _ => unreachable!("kernel returned an unrelated enumerate error"),
        })
    }
}

/// The kernel variable identities named in a rendered kernel value, as
/// substrings that identify them in a rendered proposition. Candidate
/// selection only; every selected premise is still checked.
fn kernel_variable_keys(rendered_value: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut rest = rendered_value;
    while let Some(start) = rest.find("Variable(Variable(") {
        let after = &rest[start + "Variable(Variable(".len()..];
        let digits: String = after.chars().take_while(char::is_ascii_digit).collect();
        if !digits.is_empty() {
            let key = format!("Variable(Variable({digits}))");
            if !keys.contains(&key) {
                keys.push(key);
            }
        }
        rest = after;
    }
    keys
}
