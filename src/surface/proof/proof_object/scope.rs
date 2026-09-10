//! `ProofScope`: scoped proof construction over a parent `Proof`.

use super::*;

impl<'a> ProofScope<'a> {
    pub(in crate::surface::proof) fn is_complete(&self) -> bool {
        self.body.is_complete()
    }

    #[cfg(test)]
    pub(in crate::surface::proof) fn body(&self) -> &Proof<'a> {
        &self.body
    }

    /// Attributes the next checked execution operation inside this scope to
    /// its own source tactic without changing the enclosing scope root.
    pub(in crate::surface::proof) fn with_execution_tactic_index(
        &self,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.body = self.body.with_execution_tactic_index(tactic_index)?;
        Ok(next)
    }

    /// Opens another composite resource from this scope's current checked
    /// body. The returned nested scope can only rejoin through `join_nested`,
    /// which checks that it descends from this exact body.
    pub(in crate::surface::proof) fn begin_open(
        &self,
        resource: ResourceClause,
        source_index: usize,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.body.begin_open(resource, source_index)
    }

    /// Opens one proposition subproof at the current scope body's frontier.
    ///
    /// The returned scope is rooted at this scope's current checked body. It
    /// can only be incorporated back through `join_nested`, which verifies
    /// that exact ancestry before advancing the outer scope.
    pub(in crate::surface::proof) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.body.begin_have(proposition)
    }

    /// Incorporates one completed proposition or resource scope rooted at the
    /// current body as the outer scope's next checked structural node.
    ///
    /// This is the scope analogue of `Proof::apply_step`: callers cannot
    /// replace the body with an unrelated checked proof or skip intervening
    /// nodes. The nested join owns its exact `Have` certificate and exposes
    /// only that operation's output-sized fact delta to the outer scope.
    pub(in crate::surface::proof) fn join_nested(
        &self,
        nested: ProofScope<'a>,
    ) -> Result<Self, ClickError> {
        if !Arc::ptr_eq(&nested.root.context, &self.body.context)
            || !nested.root.state.shares_state_with(&self.body.state)
            || !Arc::ptr_eq(&nested.root.node, &self.body.node)
        {
            return Err(self
                .root
                .step_error("nested proof scope is not rooted at the current scope body"));
        }
        let body = nested.join()?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("nested proof scope produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self
                .root
                .step_error("nested proof scope did not produce one direct checked successor"));
        }
        let mut next = self.clone();
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Applies one checked step inside the nested body. Failed
    /// candidates leave the enclosing scope value unchanged.
    pub(in crate::surface::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step_with_origin(step, None)?;
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Opens the C branch at this scope body's frontier as an in-`Proof`
    /// sibling split. The returned proof advances by focusing each recorded
    /// arm; `join_execution_split` accepts the direct joined successor.
    pub(in crate::surface::proof) fn split_execution_branch(
        &self,
    ) -> Result<(Proof<'a>, ExecutionSplit<'a>), ClickError> {
        self.body.split_focused_execution_branch()
    }

    /// Opens a proof-level case split at this scope body's frontier. The
    /// returned proof advances by focusing each recorded case;
    /// `join_execution_if_terminal` accepts the direct joined successor.
    pub(in crate::surface::proof) fn split_execution_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Proof<'a>, ExecutionProofCaseSplit<'a>), ClickError> {
        self.body.split_focused_execution_if(condition)
    }

    /// Joins the two completed cases of an in-`Proof` case split as the next
    /// direct structural node of this scope, with the same provenance check
    /// as `join_execution_split`.
    pub(in crate::surface::proof) fn join_execution_if_terminal(
        &self,
        advanced: &Proof<'a>,
        record: &ExecutionProofCaseSplit<'a>,
    ) -> Result<Self, ClickError> {
        let body = advanced.join_focused_execution_if_terminal(record)?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("case split join produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self
                .root
                .step_error("case split join did not produce one direct checked successor"));
        }
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Joins an advanced in-`Proof` execution split as the next direct
    /// structural node of this scope. The split's marker identity prevents
    /// a region searched from a sibling scope from being spliced here, and
    /// only the audited join's output-sized fact delta is exposed.
    pub(in crate::surface::proof) fn join_execution_split(
        &self,
        advanced: &Proof<'a>,
        record: &ExecutionSplit<'a>,
        empty: bool,
        ensuring: Option<Vec<ProofAssertion>>,
    ) -> Result<Self, ClickError> {
        let body = advanced.join_focused_execution_split(record, empty, ensuring)?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("execution branch join produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self
                .root
                .step_error("execution branch join did not produce one direct checked successor"));
        }
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Applies an already-expanded logical C branch inside this resource
    /// scope without constructing or comparing a parallel certificate.
    /// Whether the scope body's frontier is the C `if` whose condition is
    /// `surface_condition`.
    pub(in crate::surface::proof) fn frontier_is_execution_branch(
        &self,
        surface_condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        self.body.frontier_is_execution_branch(surface_condition)
    }

    pub(in crate::surface::proof) fn apply_expanded_execution_if(
        &self,
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
    ) -> Result<Self, ClickError> {
        let body = self
            .body
            .apply_expanded_execution_if(condition, then_steps, else_steps)?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("expanded execution branch produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self.root.step_error(
                "expanded execution branch did not produce one direct checked successor",
            ));
        }
        #[cfg(test)]
        CHECKED_EXPANDED_EXECUTION_IFS.with(|count| count.set(count.get() + 1));
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(next)
    }

    pub(in crate::surface::proof) fn checkpoint(&self) -> ProofCheckpoint<'a> {
        self.body.checkpoint()
    }

    pub(in crate::surface::proof) fn certificate_since(
        &self,
        checkpoint: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        self.body.certificate_since(checkpoint)
    }

    /// Applies a source-owned proof step inside the scope. Terminal steps use
    /// the site only to schedule already-checked ordered outcome work.
    pub(in crate::surface::proof) fn apply_step_at(
        &self,
        step: ProofStep,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step_with_origin(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )?;
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Runs the narrow linear `execute` search inside this scope.
    ///
    /// Each selected statement is checked and retained by
    /// `Proof::try_statement_step`; the search never mutates a second
    /// semantic context or reconstructs steps from its aftermath. A partial
    /// advance is discarded unless the checked descendant reaches function
    /// exit, so unsupported frontiers return a bounded miss to the caller.
    pub(in crate::surface::proof) fn try_linear_execute(&self) -> Result<Option<Self>, ClickError> {
        let Some((body, added_facts)) = self.body.try_linear_execute_descendant()? else {
            return Ok(None);
        };
        let mut introduced_facts = self.introduced_facts.clone();
        for fact in added_facts {
            if !introduced_facts.contains(&fact) {
                introduced_facts.push(fact);
            }
        }
        let mut next = self.clone();
        next.introduced_facts = introduced_facts;
        next.body = body;
        Ok(Some(next))
    }

    /// Runs bare theorem-application search on the scope's current checked
    /// body and retains only the accepted explicit theorem step. Function-exit
    /// applications remain outcome-local ordered-finalization operations.
    pub(in crate::surface::proof) fn try_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<Self>, ClickError> {
        if self.body.is_at_function_exit() {
            return Ok(None);
        }
        let Some(body) = self.body.try_theorem_application(application)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs bare fact-transport search on the scope's current checked body.
    /// Failed candidate descendants are discarded by `Proof`; the enclosing
    /// scope receives only the successful retained `TransportUsing` node.
    pub(in crate::surface::proof) fn try_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        if self.body.is_at_function_exit() {
            return Ok(None);
        }
        let Some(body) = self.body.try_execution_fact_transport(source, target)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the narrow straight-line `execute_until` search on checked
    /// descendants and stops before the selected source statement.
    pub(in crate::surface::proof) fn try_linear_execute_until(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<Self>, ClickError> {
        let Some((body, added_facts)) = self.body.try_linear_execute_until_descendant(region)?
        else {
            return Ok(None);
        };
        let mut introduced_facts = self.introduced_facts.clone();
        for fact in added_facts {
            if !introduced_facts.contains(&fact) {
                introduced_facts.push(fact);
            }
        }
        let mut next = self.clone();
        next.introduced_facts = introduced_facts;
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the small shared smart closure search inside the nested proof.
    /// Every accepted candidate still advances through `Proof::apply_step`.
    pub(in crate::surface::proof) fn try_direct_logical_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_direct_logical_closure()? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the migrated `simp` search inside the nested proof and retains
    /// the accepted descendant directly.
    /// Whether execution inside the scope reached function exit.
    pub(in crate::surface::proof) fn is_at_function_exit(&self) -> bool {
        self.body.is_at_function_exit()
    }

    /// Schedules an ordered outcome operation written inside the scope
    /// body after execution reached function exit; the body's deferred
    /// operations follow the scope through its join to finalization.
    pub(in crate::surface::proof) fn defer_post_execution_source_tactic(
        &self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
        expansion_capture: Option<&mut ExpansionCapture>,
    ) -> Result<Self, ClickError> {
        let body = self.body.defer_post_execution_source_tactic(
            tactic_index,
            source_index,
            tactic,
            expansion_capture,
        )?;
        let mut next = self.clone();
        next.body = body;
        Ok(next)
    }

    pub(in crate::surface::proof) fn try_simp_closure(&self) -> Result<Option<Self>, ClickError> {
        let Some(mut body) = self.body.try_simp_closure()? else {
            return Ok(None);
        };
        // At an outcome or in a pure proof a bare assumption may cite an ambient
        // fact the certificate cannot spell, so a derivation from spelled
        // premises is preferred. Mid-execution, an available fact is its own spelling:
        // `assumption();` checks by re-checking the judgment, and the
        // frontier derivation exists for what the direct closer cannot
        // prove, not to replace what it can.
        let mid_execution = matches!(self.body.context.as_ref(), ProofContext::Execution(_))
            && self.body.focused_outcome_data().is_none();
        if body.node.depth == 1
            && matches!(body.node.step.as_deref(), Some(ProofStep::Assumption))
            && !mid_execution
            && let Some(checkable) = self.body.try_simp_closure_after_direct(true)?
        {
            body = checkable;
        }
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_simp_closure_with_surfaces(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self
            .body
            .try_simp_closure_with_surfaces(introduced_surfaces)?
        else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Runs one supported source script inside the owned nested body and
    /// retains its already-checked descendant.
    pub(in crate::surface::proof) fn try_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_linear_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Checks a source body after its enclosing driver has selected Proof as
    /// the authority for this scope. Explicit failures remain checked errors
    /// through every nested scope and logical arm.
    pub(in crate::surface::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_authoritative_linear_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Applies a planner-selected recursive script inside this owned scope,
    /// retaining the checked body descendant without materializing a
    /// certificate.
    pub(in crate::surface::proof) fn try_planned_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_planned_linear_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Smart-only compatibility wrapper retained for focused branch regressions.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_linear_smart_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_linear_smart_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Closes a completed nested proof and makes its checked proposition
    /// available in the enclosing proof while retaining the exact body.
    pub(in crate::surface::proof) fn join(self) -> Result<Proof<'a>, ClickError> {
        self.join_inner()
    }

    /// The enclosing-frontier bookkeeping of a checked execution `have`,
    /// shared in meaning with `check_mid_execution_have`: lowering and
    /// certificate fact recording.
    fn carry_have_into_frontier(
        execution: &mut ExecutionProofState,
        proposition: &ClickProposition,
        kernel: &Proposition,
    ) -> Result<(), ClickError> {
        execution
            .presentation
            .surface_propositions
            .record_lowering(proposition, kernel)?;
        execution
            .presentation
            .surface_record
            .certificate_facts
            .insert(kernel.clone());
        Ok(())
    }

    fn join_inner(self) -> Result<Proof<'a>, ClickError> {
        match *self.structure {
            ProofScopeStructure::Have {
                proposition,
                kernel,
                retained_body,
            } => {
                if !self.body.is_complete() {
                    return Err(self
                        .root
                        .step_error("cannot close `have`: nested proof is incomplete"));
                }
                let body = self.body.certificate();
                let mut facts = self.root.facts().clone();
                facts = facts.with_kernel_checked_fact(kernel.clone());
                let mut checked_facts = vec![kernel.clone()];
                if let Some((_, body_kernel)) = &retained_body {
                    facts = facts.with_kernel_checked_fact(body_kernel.clone());
                    checked_facts.push(body_kernel.clone());
                }
                let mut obligation =
                    self.root.focused_obligation().cloned().ok_or_else(|| {
                        self.root.step_error("`have` scope goal is no longer open")
                    })?;
                let execution = match (self.root.context.as_ref(), &obligation) {
                    // A `have` at an execution frontier publishes what the
                    // shared mid-execution law publishes: the proposition's
                    // lowering, its certificate fact, and any function-entry
                    // authority the checked fact or an explicit theorem
                    // application establishes for later statement checks.
                    (ProofContext::Execution(_), Obligation::Frontier(_)) => {
                        let mut execution = self
                            .root
                            .branch_execution()
                            .cloned()
                            .map(Arc::unwrap_or_clone)
                            .ok_or_else(|| {
                                self.root
                                    .step_error("`have` scope lost its execution frontier")
                            })?;
                        Self::carry_have_into_frontier(&mut execution, &proposition, &kernel)?;
                        if let Some((body_surface, body_kernel)) = &retained_body {
                            Self::carry_have_into_frontier(
                                &mut execution,
                                body_surface,
                                body_kernel,
                            )?;
                        }
                        Some(Arc::new(execution))
                    }
                    _ => self
                        .root
                        .focused_branch()
                        .expect("the checked scope has an open focused branch")
                        .state
                        .execution
                        .clone(),
                };
                if let Obligation::FunctionOutcome(outcome) = &obligation {
                    let mut updated = outcome.clone();
                    let mut data = (*updated.data).clone();
                    data.surface_propositions
                        .record_lowering(&proposition, &kernel)?;
                    updated.data = Arc::new(data);
                    obligation = Obligation::FunctionOutcome(updated);
                }
                let state = self
                    .root
                    .state
                    .publish_checked_focused_transition(
                        obligation,
                        facts,
                        execution,
                        checked_facts.clone(),
                        checked_facts,
                    )
                    .map_err(|_| self.root.step_error("`have` scope goal is no longer open"))?;
                Ok(Proof {
                    site: self.root.site.clone(),
                    context: self.root.context.clone(),
                    state,
                    node: Arc::new(ProofNode {
                        parent: Some(self.root.node.clone()),
                        step: Some(Arc::new(ProofStep::Have {
                            proposition,
                            proof: Box::new(body),
                        })),
                        focused_branch: self.root.focused_branch_id(),
                        depth: self.root.node.depth + 1,
                    }),
                })
            }
            ProofScopeStructure::Open {
                resource,
                source_index,
                preserve_exposed_body,
            } => {
                let ProofContext::Execution(context) = self.root.context.as_ref() else {
                    unreachable!("an open scope can only be created from an execution Proof")
                };
                let body = self.body.certificate();
                let mut execution = self
                    .body
                    .branch_execution()
                    .cloned()
                    .map(Arc::unwrap_or_clone)
                    .ok_or_else(|| {
                        self.root
                            .step_error("open scope body lost its execution frontier")
                    })?;
                let mut facts = self.body.facts().clone();
                if execution.core.frontier.is_at_function_exit() {
                    execution.presentation.defer_post_execution(
                        context.tactic_index,
                        source_index,
                        PostExecutionTactic::CloseOpen {
                            resource: resource.clone(),
                            preserve_exposed_body,
                        },
                    );
                } else {
                    let before_facts = facts.clone();
                    let pre_state = context
                        .old_reference_state(&execution.core.frontier, &execution.core.state)
                        .clone();
                    let checked = close_open_resource_for_proof(
                        context.resource_environment,
                        &resource,
                        context.claim_label,
                        context.tactic_index,
                        facts,
                        context.parsed_function.parameters(),
                        context.arguments,
                        &pre_state,
                        (*execution.core.state).clone(),
                        context.predicate_environment,
                        context.click_function_environment,
                        &execution.core.unfolded_predicates,
                        preserve_exposed_body,
                    )?;
                    let selected = lower_resource_clause_at_state(
                        &resource,
                        context.parsed_function.parameters(),
                        context.arguments,
                        &checked.state,
                    )?;
                    execution
                        .core
                        .record_resource_rewrite(
                            context.function,
                            context.arguments,
                            &before_facts,
                            &selected,
                            &checked.state,
                            &checked.facts,
                        )
                        .map_err(|message| {
                            self.root.step_error(format!(
                                "kernel rejected checked resource close: {message}"
                            ))
                        })?;
                    facts = checked.facts;
                    execution.core.state = checked.state.into();
                }
                let state = self
                    .body
                    .state
                    .publish_checked_frontier_transition(
                        facts,
                        execution,
                        self.introduced_facts.clone(),
                        self.introduced_facts,
                    )
                    .map_err(|error| match error {
                        ExecutionUpdateError::NotFrontier
                        | ExecutionUpdateError::MissingExecution => self
                            .root
                            .step_error("open scope body lost its execution frontier"),
                        ExecutionUpdateError::NotLoopBody
                        | ExecutionUpdateError::InvariantsAlreadyClosed => {
                            unreachable!("open-scope publication checks only frontier ownership")
                        }
                    })?;
                // The successor's goal map came from the scope body, whose
                // cursor may have moved through a decided branch.
                let focused_branch = self.body.focused_branch_id();
                Ok(Proof {
                    site: self.root.site.clone(),
                    context: self.root.context.clone(),
                    state,
                    node: Arc::new(ProofNode {
                        parent: Some(self.root.node.clone()),
                        step: Some(Arc::new(ProofStep::Open {
                            resource,
                            proof: Box::new(body),
                        })),
                        focused_branch,
                        depth: self.root.node.depth + 1,
                    }),
                })
            }
        }
    }
}
