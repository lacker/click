//! Where an execution proof begins and how its snapshot is edited: the
//! root constructors from an entry execution state, derived roots for loop
//! effects and post-execution tactics, and the in-place edit of the focused branch
//! frontier's execution.

use super::*;

impl<'a> Proof<'a> {
    /// Creates an execution-frontier proof whose C state, check metadata,
    /// facts, and provenance are structurally shared by checked descendants.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_execution_frontier(
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
    pub(in crate::surface::proof) fn for_execution_frontier_with_effect_goals(
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
            state: KernelProofObject::root(
                ProofLocals::default(),
                OpenBranch::frontier(
                    effect_goals,
                    BranchState {
                        facts: ProofFacts::from_ordered(&pure_facts),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(execution)),
                    },
                ),
            ),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
        }
    }

    /// Derives one structural loop-effect obligation from an already checked
    /// preservation path. The new root shares the path's facts and execution
    /// snapshot; only the explicitly declared effect goal and its diagnostic
    /// source site are installed.
    pub(in crate::surface::proof) fn start_loop_effect_proof<'b>(
        &'b self,
        claim_label: &'b str,
        site: ProofSite,
        before_state: &CState,
        check: &CLoopEffectCheck,
        whole_loop_effect_facts: &[Proposition],
    ) -> Result<Proof<'b>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a loop effect requires an execution proof"));
        };
        self.require_execution_frontier("a loop effect")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("a loop effect lost its preservation state"))?;
        execution.core.loop_effect_goal = Some(LoopEffectGoal {
            before_state: before_state.clone(),
            check: check.clone(),
            whole_loop_effect_facts: whole_loop_effect_facts.to_vec(),
            closed: false,
        });
        execution.presentation.surface_record = SurfaceRecord::default();
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
            state: KernelProofObject::root(
                ProofLocals::default(),
                OpenBranch::frontier(
                    EffectGoalSelection::None,
                    BranchState {
                        facts: self.facts().clone(),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(execution)),
                    },
                ),
            ),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
        })
    }

    /// Starts one source tactic on a threaded execution Proof by clearing the
    /// checked and newly added facts reported for the preceding step.
    pub(in crate::surface::proof) fn start_source_tactic(self) -> Result<Self, ClickError> {
        let state = self.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(self.with_kernel_state(state))
    }

    /// Edits only the focused execution frontier's opaque Surface metadata.
    /// The kernel preserves the checked execution core, facts, obligation,
    /// and proof deltas and never exposes them to the callback.
    pub(in crate::surface::proof) fn edit_execution_presentation<R>(
        self,
        edit: impl FnOnce(&mut ExecutionProofPresentation) -> R,
    ) -> Result<(Self, R), ClickError> {
        let Self {
            context,
            state,
            node,
        } = self;
        let (state, result) = state.edit_frontier_presentation(edit).map_err(|error| {
            let message = match error {
                ExecutionUpdateError::NotFrontier => {
                    "construction cursor editing requires an execution frontier"
                }
                ExecutionUpdateError::MissingExecution => {
                    "execution-frontier proof lost its semantic state"
                }
                ExecutionUpdateError::ClosedLoopEffect
                | ExecutionUpdateError::NotLoopBody
                | ExecutionUpdateError::InvariantsAlreadyClosed
                | ExecutionUpdateError::LoopEffectNotClosed => {
                    unreachable!("presentation editing checks only frontier ownership")
                }
            };
            ClickError::new(message)
        })?;
        Ok((
            Self {
                context,
                state,
                node,
            },
            result,
        ))
    }

    /// Borrows a checked execution frontier without exporting mutable proof
    /// state. Planning uses this at statement and region boundaries.
    pub(in crate::surface::proof) fn execution_view(
        &self,
    ) -> Result<ProofExecutionView<'_>, ClickError> {
        self.proof_execution_view(false)
    }

    /// Borrows the function-exit frontier accepted by claim finalization.
    pub(in crate::surface::proof) fn finalization_view(
        &self,
    ) -> Result<ProofExecutionView<'_>, ClickError> {
        self.proof_execution_view(true)
    }

    fn proof_execution_view(
        &self,
        require_function_exit: bool,
    ) -> Result<ProofExecutionView<'_>, ClickError> {
        #[cfg(test)]
        FINALIZATION_VIEW_CONSTRUCTIONS.with(|count| count.set(count.get() + 1));
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("proof does not own an execution frontier"));
        };
        let checked = if require_function_exit {
            self.state.finalization()
        } else {
            self.state.execution_view()
        }
        .ok_or_else(|| {
            self.step_error(if require_function_exit {
                "execution proof lost its terminal state"
            } else {
                "execution proof lost its checked frontier"
            })
        })?;
        let execution = checked.execution();
        Ok(ProofExecutionView {
            state: &execution.core.state,
            facts: checked.facts().to_vec(),
            frontier: &execution.core.frontier,
            execution,
            context,
            unfolded_predicates: &execution.core.unfolded_predicates,
            branch_path: &execution.presentation.branch_path,
            outcome_provenance: execution.presentation.outcome_provenance.as_ref(),
        })
    }

    /// Records one source-ordered outcome operation on this terminal Proof.
    /// This is cursor metadata only: the operation's semantic transition is
    /// applied later to each typed `FunctionOutcome` goal by finalization.
    /// When expansion selected this source occurrence, the retained prefix is
    /// serialized solely to seed that requested capture.
    pub(in crate::surface::proof) fn defer_post_execution_source_tactic(
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
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        if !execution.core.frontier.is_at_function_exit() {
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
        let deferred_tactic_capture =
            if let Some((nested_tactic_index, nested_source_index)) = selected {
                if begin_tactic_expansion_capture(
                    expansion_capture,
                    nested_source_index,
                    &execution.presentation.expansion,
                    context.constants.proof_site.as_ref(),
                ) {
                    Some(DeferredTacticCapture {
                        tactic_index: nested_tactic_index,
                        source_index: nested_source_index,
                        post_execution_index: DeferredTacticCapture::NESTED,
                        branch_skeleton: branch_skeleton(),
                    })
                } else {
                    None
                }
            } else if begin_tactic_expansion_capture(
                expansion_capture,
                source_index,
                &execution.presentation.expansion,
                context.constants.proof_site.as_ref(),
            ) {
                Some(DeferredTacticCapture {
                    tactic_index,
                    source_index,
                    post_execution_index: execution.presentation.post_execution_tactics.len(),
                    branch_skeleton: branch_skeleton(),
                })
            } else {
                None
            };
        let Self {
            context,
            state,
            node,
        } = self.clone();
        let (state, ()) = state
            .edit_frontier_presentation(|presentation| {
                if let Some(capture) = deferred_tactic_capture {
                    presentation.expansion.deferred_tactic_capture = Some(capture);
                }
                presentation.defer_post_execution(tactic_index, source_index, tactic);
            })
            .map_err(|error| match error {
                ExecutionUpdateError::NotFrontier => self
                    .step_error("post-execution tactic scheduling requires an execution frontier"),
                ExecutionUpdateError::MissingExecution => {
                    self.step_error("execution proof lost its terminal state")
                }
                ExecutionUpdateError::ClosedLoopEffect
                | ExecutionUpdateError::NotLoopBody
                | ExecutionUpdateError::InvariantsAlreadyClosed
                | ExecutionUpdateError::LoopEffectNotClosed => {
                    unreachable!("presentation scheduling checks only frontier ownership")
                }
            })?;
        Ok(Self {
            context,
            state,
            node,
        })
    }

    /// Semantic facts introduced by the most recently accepted step.
    /// Enclosing proof infrastructure can incorporate this output-sensitive
    /// delta without traversing or cloning the proof's complete fact set.
    pub(in crate::surface::proof) fn added_facts(&self) -> &[Proposition] {
        self.state().added_facts()
    }

    /// Exact semantic facts selected or established by the latest step, in
    /// step-defined order. This lets enclosing surface bookkeeping record the
    /// checker-owned forms without re-lowering them.
    pub(in crate::surface::proof) fn checked_facts(&self) -> &[Proposition] {
        self.state().checked_facts()
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
