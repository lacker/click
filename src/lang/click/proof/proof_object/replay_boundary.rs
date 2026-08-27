//! The transitional replay adapter boundary: entering `Proof` from a
//! entry execution state and exporting checked
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
        execution: ExecutionProofState,
        pure_facts: Vec<Proposition>,
        constants: ExecutionProofConstants,
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
        let effect_goals = match constants.proof_site.as_ref() {
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
            pure_facts,
            constants,
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
        execution: ExecutionProofState,
        pure_facts: Vec<Proposition>,
        constants: ExecutionProofConstants,
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
                constants: Arc::new(constants),
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),

                goals: ProofGoals::root(Goal::Frontier(FrontierGoal {
                    selection: effect_goals,
                    context: GoalContext {
                        facts: ProofFacts::from_ordered(&pure_facts),
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
                constants: Arc::new(ExecutionProofConstants {
                    proof_site: Some(site),
                    ..(*context.constants).clone()
                }),
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

    /// Starts one source tactic on a threaded execution Proof: the step delta
    /// of the previous checked transition is cleared. This is the one rule
    /// shared by every source driver, so a source tactic's certificate step
    /// depends on the proof state and not on which tactic textually preceded
    /// it. The delta remains meaningful inside one smart search, where
    /// consecutive statement transitions legitimately feed each other.
    pub(in crate::lang::click::proof) fn start_source_tactic(self) -> Result<Self, ClickError> {
        let (proof, ()) = self.edit_frontier_in_place(|state, execution, _| {
            Self::clear_step_delta(state, execution);
        })?;
        Ok(proof)
    }

    fn clear_step_delta(state: &mut ProofState, execution: &mut ExecutionProofState) {
        state.added_facts = Arc::new(Vec::new());
        state.checked_facts = Arc::new(Vec::new());
        execution.last_step_delta = ExecutionProofStepDelta::default();
    }

    /// Transitional cursor edit for the in-place interpreter conversion:
    /// runs one bookkeeping closure over the focused frontier's replay
    /// cursor, with read access to the frontier's C state and fact context,
    /// and retains the edited cursor on a successor that adds no provenance
    /// node. It grants no semantic authority: the interpreter uses it for
    /// the surface-scope, expansion capture, and deferral bookkeeping it
    /// previously performed on the loose replay tuple. Deleted with
    /// `TacticReplayState` in phase 2.
    pub(in crate::lang::click::proof) fn edit_replay_cursor<R>(
        self,
        edit: impl FnOnce(&mut TacticReplayState, &CState, &ProofFacts) -> R,
    ) -> Result<(Self, R), ClickError> {
        self.edit_frontier_in_place(|_, execution, facts| {
            edit(&mut execution.replay, &execution.state, facts)
        })
    }

    /// Edits the focused frontier goal's execution snapshot in place. The
    /// proof is consumed so a uniquely owned snapshot is edited without a
    /// per-tactic clone; a shared snapshot is copied on write.
    fn edit_frontier_in_place<R>(
        self,
        edit: impl FnOnce(&mut ProofState, &mut ExecutionProofState, &ProofFacts) -> R,
    ) -> Result<(Self, R), ClickError> {
        let Some(Goal::Frontier(goal)) = self.focused_goal().cloned() else {
            return Err(self.step_error("replay cursor editing requires an execution frontier"));
        };
        let missing = self.step_error("execution-frontier proof lost its semantic state");
        let Self {
            context,
            state,
            node,
            focused,
        } = self;
        let mut proof_state = Arc::unwrap_or_clone(state);
        // Release the goal map's reference first so the execution snapshot
        // is unique whenever this proof was.
        proof_state.goals = ProofGoals {
            open: proof_state.goals.open.without_key(&focused),
            next_id: proof_state.goals.next_id,
        };
        let FrontierGoal {
            selection,
            context: goal_context,
        } = goal;
        let GoalContext {
            facts,
            unfolded_predicates,
            execution,
        } = goal_context;
        let mut execution = Arc::unwrap_or_clone(execution.ok_or(missing)?);
        let result = edit(&mut proof_state, &mut execution, &facts);
        proof_state.goals = ProofGoals {
            open: proof_state.goals.open.with_inserted(
                focused,
                Goal::Frontier(FrontierGoal {
                    selection,
                    context: GoalContext {
                        facts,
                        unfolded_predicates,
                        execution: Some(Arc::new(execution)),
                    },
                }),
            ),
            next_id: proof_state.goals.next_id,
        };
        Ok((
            Self {
                context,
                state: Arc::new(proof_state),
                node,
                focused,
            },
            result,
        ))
    }

    /// Borrows the terminal execution data needed by claim finalization
    /// without exporting it into a mutable replay context.
    pub(in crate::lang::click::proof) fn finalization_view(
        &self,
    ) -> Result<ProofFinalizationView<'_>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("proof does not own an execution frontier"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        Ok(ProofFinalizationView {
            state: &execution.state,
            facts: self.facts().to_vec(),
            replay: &execution.replay,
            frontier: &execution.frontier,
            execution,
            context,
            unfolded_predicates: &execution.unfolded_predicates,
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
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("post-execution tactics require an execution proof"));
        };
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        if !execution.frontier.is_at_function_exit() {
            return Err(
                self.step_error("post-execution tactics can be scheduled only at function exit")
            );
        }
        let branch_skeleton = || {
            ProofCertificate::from_steps(surface_branch_skeleton(self.certificate().steps()))
                .to_proof_tactics()
        };
        // A tactic nested in a deferred `if` arm is drained at a flattened
        // position no deferral can know; its capture matches by tactic
        // index alone (`DeferredTacticCapture::NESTED`).
        let selected = expansion_capture
            .as_deref()
            .and_then(|capture| capture.source_index)
            .filter(|selected| *selected != source_index)
            .and_then(|selected| nested_deferred_tactic_by_source(&tactic, selected));
        if let Some((nested_tactic_index, nested_source_index)) = selected {
            if begin_tactic_expansion_capture(
                expansion_capture,
                nested_source_index,
                &execution.replay,
                context.constants.proof_site.as_ref(),
            ) {
                execution.replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                    tactic_index: nested_tactic_index,
                    source_index: nested_source_index,
                    post_execution_index: DeferredTacticCapture::NESTED,
                    branch_skeleton: branch_skeleton(),
                });
            }
        } else if begin_tactic_expansion_capture(
            expansion_capture,
            source_index,
            &execution.replay,
            context.constants.proof_site.as_ref(),
        ) {
            execution.replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                source_index,
                post_execution_index: execution.replay.post_execution_tactics.len(),
                branch_skeleton: branch_skeleton(),
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

/// The `(tactic_index, source_index)` of the tactic with `source_index`
/// nested in the arms of a deferred `if`, at any depth.
fn nested_deferred_tactic_by_source(
    tactic: &PostExecutionTactic,
    source_index: usize,
) -> Option<(usize, usize)> {
    let PostExecutionTactic::If {
        then_tactics,
        else_tactics,
        ..
    } = tactic
    else {
        return None;
    };
    then_tactics.iter().chain(else_tactics).find_map(|nested| {
        if nested.source_index == source_index {
            Some((nested.tactic_index, nested.source_index))
        } else {
            nested_deferred_tactic_by_source(&nested.tactic, source_index)
        }
    })
}
