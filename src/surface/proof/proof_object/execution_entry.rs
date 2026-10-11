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
        mut execution: ExecutionProofState,
        pure_facts: impl PropositionSource,
        constants: ExecutionProofConstants,
        function_block: &'a FunctionBlock,
        function: &'a CFunction,
        parsed_function: &'a syntax::C0Function,
        arguments: &'a [CExpression],
        function_environment: &'a CExecutionEnvironment,
        resource_environment: &'a ResourceEnvironment,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        // The proof root is the entry's own fact lineage when the execution
        // has not left its checked entry, so later facts descend from it.
        let facts = execution
            .core
            .entry_facts_at_entry()
            .cloned()
            .unwrap_or_else(|| ProofFacts::from_source(&pure_facts));
        // A fresh premise lineage cannot reuse contexts checked under the
        // previous root. Compatible derived roots retain the original base
        // so newly added ambient facts remain visible as a suffix.
        if !execution
            .presentation
            .outcome_fact_root
            .as_ref()
            .is_some_and(|root| facts.introduced_since(root).is_some())
        {
            execution.presentation.outcome_fact_root = Some(Arc::new(facts.clone()));
            execution.presentation.checked_leaf_facts = None;
            for provenance in execution.presentation.outcome_provenance.iter_mut() {
                provenance.checked_leaf_facts = None;
            }
        }
        Self {
            site: ProofStepSite::default(),
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label,
                tactic_index,
                function_block,
                function,
                parsed_function,
                arguments,
                function_environment,
                resource_environment,
                spec_definitions,
                theorem_environment,
                step_tactic_name: "step()",
                constants: Arc::new(constants),
            })),
            state: KernelProofObject::root(
                ProofLocals::default(),
                OpenBranch::frontier(BranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: Some(Arc::new(execution)),
                }),
            ),
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
                split_branches: Vec::new(),
            }),
        }
    }

    pub(in crate::surface::proof) fn prepare_entry_interface(&self) -> Result<Self, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(self.clone());
        };
        if !execution.core.frontier.is_at_function_entry()
            || execution.core.frontier.entry_member_prefix
        {
            return Ok(self.clone());
        }
        let mut execution = execution.clone();
        execution
            .core
            .materialize_function_entry()
            .map_err(|message| self.step_error(message))?;
        let state = self
            .state
            .publish_checked_frontier_transition(
                self.facts().clone(),
                execution,
                Vec::new(),
                Vec::new(),
            )
            .map_err(|_| self.step_error("entry interface lost its execution frontier"))?;
        Ok(self.with_kernel_state(state))
    }

    /// Starts the `source_index`th source tactic on a threaded execution
    /// Proof by clearing the checked and newly added facts reported for the
    /// preceding step, and by addressing this occurrence in diagnostics so
    /// every scope it opens reports where the user wrote it.
    pub(in crate::surface::proof) fn start_source_tactic(
        self,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let state = self.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(self.at_source_tactic(source_index).with_kernel_state(state))
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
            site,
        } = self;
        let (state, result) = state.edit_frontier_presentation(edit).map_err(|error| {
            let message = match error {
                ExecutionUpdateError::NotFrontier => {
                    "construction cursor editing requires an execution frontier"
                }
                ExecutionUpdateError::MissingExecution => {
                    "execution-frontier proof lost its semantic state"
                }
                ExecutionUpdateError::NotLoopBody
                | ExecutionUpdateError::InvariantsAlreadyClosed => {
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
                site,
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
            facts: checked.facts(),
            frontier: &execution.core.frontier,
            execution,
            context,
            unfolded_predicates: &execution.core.unfolded_predicates,
            branch_path: &execution.presentation.branch_path,
            outcome_provenance: &execution.presentation.outcome_provenance,
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
        let branch_skeleton = || -> Result<Vec<ProofTactic>, ClickError> {
            Ok(
                ProofCertificate::from_steps(surface_branch_skeleton(self.certificate().steps()))?
                    .to_proof_tactics(),
            )
        };
        if let Some(capture) = expansion_capture.as_deref()
            && capture.batch.is_some()
            && context.constants.proof_site.as_ref() == Some(&capture.site)
        {
            let mut selected = Vec::new();
            fn collect(
                tactic: &PostExecutionTactic,
                index: usize,
                source: usize,
                capture: &ExpansionCapture,
                selected: &mut Vec<(usize, usize)>,
            ) {
                if capture.selects(&capture.site, source) {
                    selected.push((index, source));
                }
                if let PostExecutionTactic::If {
                    then_tactics,
                    else_tactics,
                    ..
                } = tactic
                {
                    for nested in then_tactics.iter().chain(else_tactics) {
                        collect(
                            &nested.tactic,
                            nested.tactic_index,
                            nested.source_index,
                            capture,
                            selected,
                        );
                    }
                }
            }
            collect(&tactic, tactic_index, source_index, capture, &mut selected);
            let skeleton = if selected.is_empty() {
                None
            } else {
                Some(
                    execution
                        .presentation
                        .expansion
                        .batch_branch_skeleton
                        .clone()
                        .map_or_else(|| branch_skeleton().map(Arc::new), Ok)?,
                )
            };
            let post_index = execution.presentation.post_execution_tactics.len();
            let (state, ()) = self
                .state
                .clone()
                .edit_frontier_presentation(|presentation| {
                    if let Some(skeleton) = skeleton {
                        presentation.expansion.batch_branch_skeleton = Some(skeleton.clone());
                        for (index, source) in selected {
                            presentation.expansion.batch_deferred_captures.insert(
                                source,
                                DeferredTacticCapture {
                                    tactic_index: index,
                                    source_index: source,
                                    post_execution_index: if source == source_index {
                                        post_index
                                    } else {
                                        DeferredTacticCapture::NESTED
                                    },
                                    branch_skeleton: skeleton.clone(),
                                    can_expand_execution_prefix: matches!(
                                        &tactic,
                                        PostExecutionTactic::Simp
                                            | PostExecutionTactic::SimpUsing(_)
                                            | PostExecutionTactic::Have(_)
                                    ),
                                },
                            );
                        }
                    }
                    presentation.defer_post_execution(tactic_index, source_index, tactic);
                })
                .map_err(|_| self.step_error("batch capture lost its terminal frontier"))?;
            return Ok(Self {
                state,
                ..self.clone()
            });
        }
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
                        branch_skeleton: Arc::new(branch_skeleton()?),
                        can_expand_execution_prefix: false,
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
                    branch_skeleton: Arc::new(branch_skeleton()?),
                    can_expand_execution_prefix: matches!(
                        &tactic,
                        PostExecutionTactic::Simp
                            | PostExecutionTactic::SimpUsing(_)
                            | PostExecutionTactic::Have(_)
                    ),
                })
            } else {
                None
            };
        let Self {
            context,
            state,
            node,
            site,
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
                ExecutionUpdateError::NotLoopBody
                | ExecutionUpdateError::InvariantsAlreadyClosed => {
                    unreachable!("presentation scheduling checks only frontier ownership")
                }
            })?;
        Ok(Self {
            context,
            state,
            node,
            site,
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
