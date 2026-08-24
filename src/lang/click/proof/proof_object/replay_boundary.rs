//! The transitional replay adapter boundary: entering `Proof` from a
//! `ProofReplayContext` execution frontier and exporting checked
//! results back into replay-owned state. Scheduled for deletion by
//! `issues/replay-smell.md`; keep doomed adapters co-located here.

use super::*;

impl<'a> Proof<'a> {
    /// Creates an execution-frontier proof whose C state, replay metadata,
    /// facts, and provenance are structurally shared by checked descendants.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_execution_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        execution: ProofReplayContext,
        function_block: &'a FunctionBlock,
        function: &'a CFunction,
        parsed_function: &'a syntax::C0Function,
        arguments: &'a [CExpression],
        function_environment: &'a CExecutionEnvironment,
        resource_environment: &'a ResourceEnvironment,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let effect_goals = match execution.replay.proof_site.as_ref() {
            Some(ProofSite::FunctionClaim {
                claim: CProofClaim::Grouped,
                ..
            }) if !function_block.effects().is_empty() => EffectGoalSelection::All,
            Some(ProofSite::FunctionClaim {
                claim: CProofClaim::Effect(index),
                ..
            }) => EffectGoalSelection::One(*index),
            _ => EffectGoalSelection::None,
        };
        Self::for_execution_frontier_with_effect_goals(
            claim_label,
            tactic_index,
            execution,
            effect_goals,
            function_block,
            function,
            parsed_function,
            arguments,
            function_environment,
            resource_environment,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        )
    }

    /// Constructs an execution-frontier proof with an explicit effect-goal
    /// selection. The ordered outcome drain uses `EffectGoalSelection::None`:
    /// at the drain boundary the function frame has already been consumed
    /// into deferred checked authority, so the reconstructed frontier goal no
    /// longer carries effect obligations.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_execution_frontier_with_effect_goals(
        claim_label: &'a str,
        tactic_index: usize,
        execution: ProofReplayContext,
        effect_goals: EffectGoalSelection,
        function_block: &'a FunctionBlock,
        function: &'a CFunction,
        parsed_function: &'a syntax::C0Function,
        arguments: &'a [CExpression],
        function_environment: &'a CExecutionEnvironment,
        resource_environment: &'a ResourceEnvironment,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path,
        } = execution;
        Self {
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label,
                tactic_index,
                function_block,
                function,
                parsed_function,
                arguments,
                function_environment,
                resource_environment,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),

                goals: ProofGoals::root(Goal::Frontier(FrontierGoal {
                    selection: effect_goals,
                    context: GoalContext {
                        facts: ProofFacts::from_ordered(&pure_facts),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(ExecutionProofState {
                            state: state.into(),
                            replay: *replay,
                            branch_path,
                            branch_surface_facts: PersistentOrderedSet::default(),
                            branch_decisions: PersistentSequence::default(),
                            outcome_branch_decisions: Arc::new(Vec::new()),
                            last_step_delta: ExecutionProofStepDelta::default(),
                            has_empty_execution_branch_leaf: false,
                        })),
                    },
                })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        }
    }

    /// Derives one structural loop-effect obligation from an already checked
    /// preservation path. The new root shares the path's facts and execution
    /// snapshot; only the explicitly declared effect goal and its diagnostic
    /// source site are installed.
    pub(in crate::lang::click::proof) fn start_loop_effect_goal<'b>(
        &'b self,
        claim_label: &'b str,
        site: ProofSite,
        before_state: &CState,
        check: &CLoopEffectCheck,
    ) -> Result<Proof<'b>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a loop effect requires an execution proof"));
        };
        self.require_execution_frontier("a loop effect")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("a loop effect lost its preservation state"))?;
        execution.replay.proof_site = Some(site);
        execution.replay.loop_effect_goal = Some(LoopEffectReplayGoal {
            before_state: before_state.clone(),
            check: check.clone(),
            closed: false,
        });
        execution.replay.proof_certificate_builder = ProofCertificateBuilder::default().into();
        execution.last_step_delta = ExecutionProofStepDelta::default();

        Ok(Proof {
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label,
                tactic_index: 0,
                function_block: context.function_block,
                function: context.function,
                parsed_function: context.parsed_function,
                arguments: context.arguments,
                function_environment: context.function_environment,
                resource_environment: context.resource_environment,
                predicate_environment: context.predicate_environment,
                click_function_environment: context.click_function_environment,
                theorem_environment: context.theorem_environment,
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),
                goals: ProofGoals::root(Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context: GoalContext {
                        facts: self.facts().clone(),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(execution)),
                    },
                })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        })
    }

    pub(in crate::lang::click::proof) fn into_execution_context(
        self,
    ) -> Result<ProofReplayContext, ClickError> {
        #[cfg(test)]
        EXECUTION_CONTEXT_EXPORTS.with(|exports| exports.set(exports.get() + 1));
        #[cfg(test)]
        COLLECTED_EXECUTION_CONTEXT_EXPORT_LABELS.with(|labels| {
            if let Some(labels) = labels.borrow_mut().as_mut() {
                labels.push(self.context.claim_label().to_string());
            }
        });
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("proof does not own an execution frontier"));
        }
        let missing = format!(
            "`{}` proof step {}: execution-frontier successor lost its semantic state",
            self.context.claim_label(),
            self.node.depth
        );
        // This is a legacy compatibility/export boundary, not a semantic
        // transition. A smart tactic may legitimately retain any ancestor or
        // successor; materializing the selected checked state must therefore
        // not require unique ownership of the Proof.
        let execution = self
            .goal_execution()
            .cloned()
            .ok_or_else(|| ClickError::new(missing))?;
        let execution = Arc::unwrap_or_clone(execution);
        Ok(ProofReplayContext {
            state: execution.state.into_value(),
            pure_facts: self.facts().to_vec(),
            replay: Box::new(execution.replay),
            branch_path: execution.branch_path,
        })
    }

    /// Borrows the terminal execution data needed by claim finalization
    /// without exporting it into a mutable replay context.
    pub(in crate::lang::click::proof) fn finalization_view(
        &self,
    ) -> Result<ProofFinalizationView<'_>, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("proof does not own an execution frontier"));
        }
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        Ok(ProofFinalizationView {
            state: &execution.state,
            facts: self.facts().to_vec(),
            replay: &execution.replay,
            branch_path: &execution.branch_path,
            outcome_branch_decisions: execution.outcome_branch_decisions.as_ref(),
        })
    }

    /// Records one source-ordered outcome operation on this terminal Proof.
    /// This is cursor metadata only: the operation's semantic transition is
    /// applied later to each typed `FunctionOutcome` goal by finalization.
    /// When expansion selected this source occurrence, the retained prefix is
    /// serialized solely to seed that requested capture.
    pub(in crate::lang::click::proof) fn defer_post_execution_source_tactic(
        &self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
        expansion_capture: Option<&mut ExpansionCapture>,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("post-execution tactic scheduling")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        if !execution.replay.is_at_function_exit() {
            return Err(
                self.step_error("post-execution tactics can be scheduled only at function exit")
            );
        }
        if begin_tactic_expansion_capture(expansion_capture, source_index, &execution.replay) {
            execution.replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                source_index,
                post_execution_index: execution.replay.post_execution_tactics.len(),
                branch_skeleton: ProofCertificate::from_steps(surface_branch_skeleton(
                    self.certificate().steps(),
                ))
                .to_proof_tactics(),
            });
        }
        execution
            .replay
            .defer_post_execution(tactic_index, source_index, tactic);
        let mut state = (*self.state).clone();
        state.goals =
            state
                .goals
                .replace_execution_at(self.focused, self.facts().clone(), execution);
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(state),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Semantic facts introduced by the most recently accepted step.
    /// Enclosing proof infrastructure can incorporate this output-sensitive
    /// delta without traversing or cloning the proof's complete fact set.
    pub(in crate::lang::click::proof) fn added_facts(&self) -> &[Proposition] {
        self.state.added_facts.as_ref()
    }

    /// Exact semantic facts selected or established by the latest step, in
    /// step-defined order. This lets enclosing surface bookkeeping record the
    /// checker-owned forms without re-lowering them.
    pub(in crate::lang::click::proof) fn checked_facts(&self) -> &[Proposition] {
        self.state.checked_facts.as_ref()
    }
}
