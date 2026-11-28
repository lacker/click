//! `ProofScope`: scoped proof construction over a parent `Proof`.

use super::*;

fn spell_resource_clause(resource: &ResourceClause, message: &str) -> String {
    match resource {
        ResourceClause::Named { resource, .. }
        | ResourceClause::Quantified { resource, .. }
        | ResourceClause::Conditional { resource, .. } => spell_resource_clause(resource, message),
        ResourceClause::Declared { name, .. } => {
            let spelling = crate::surface::describe_resource_clause(resource);
            message.replace(
                &format!("{name}(...)"),
                spelling.strip_prefix("view ").unwrap_or(&spelling),
            )
        }
        _ => message.to_string(),
    }
}

impl<'a> ProofScope<'a> {
    pub(in crate::surface::proof) fn is_complete(&self) -> bool {
        self.body.is_complete()
    }

    /// Retains the source body's completion, weakened only by the implication
    /// prefix consumed when this exact entry obligation was selected.
    pub(in crate::surface::proof) fn completed_loop_entry_goal(
        &self,
    ) -> Result<crate::kernel::proof::CheckedProposition, ClickError> {
        let (goal, prefix_len) = self
            .loop_entry_goal
            .as_ref()
            .ok_or_else(|| self.root.step_error("scope is not a loop entry judgment"))?;
        self.body
            .completed_proposition()?
            .with_implication_prefix(goal.proposition(), *prefix_len)
            .ok_or_else(|| {
                self.root
                    .step_error("completed body does not match its loop entry judgment")
            })
    }

    pub(in crate::surface::proof) fn goal(&self) -> Option<&Proposition> {
        self.body.goal()
    }

    /// The selected nested proof, also retained when a written check fails.
    /// Borrowing its persistent handle preserves the exact goal and context
    /// without rebuilding them from the enclosing execution frontier.
    pub(in crate::surface::proof) fn body(&self) -> &Proof<'a> {
        &self.body
    }

    /// Scope a checked introduction before publishing this nested proof.
    pub(in crate::surface::proof) fn finish_generated_intro(
        mut self,
        parent: &Proof<'a>,
        introduced: &Proof<'a>,
    ) -> Result<Self, ClickError> {
        self.body = parent.finish_generated_intro(introduced, self.body)?;
        Ok(self)
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

    /// Associates the checked lowering metadata reported by a refused
    /// requirement with an already-open `have` body.
    ///
    /// The requirement is checked against the body's actual lowered kernel
    /// goal before any presentation is installed.  This keeps a synthesized
    /// spelling from becoming proof authority: a mismatch is rejected while
    /// the scope (including its semantic state and lineage) remains
    /// unchanged.  The introduction chain is presentation-only and may be
    /// absent when the lowering did not record one.
    pub(in crate::surface::proof) fn with_reported_goal_introductions(
        &self,
        reported: &Proposition,
        introductions: Option<crate::kernel::LoweringIntroductions>,
    ) -> Result<Self, ClickError> {
        let actual = self.body.goal().ok_or_else(|| {
            self.root
                .step_error("reported requirement has no proposition goal")
        })?;
        if !crate::kernel::proof::propositions_are_alpha_equal(actual, reported) {
            return Err(self
                .root
                .step_error("synthesized `have` goal does not match its reported requirement"));
        }
        let Some(introductions) = introductions else {
            return Ok(self.clone());
        };
        // Walk the focused introduction path, rather than collecting every
        // quantifier in the proposition. A quantifier in an unrelated
        // connective branch is not reachable by `intro` and must not be used
        // to bind a reported introduction.
        let contradiction_goal = Proposition::condition_is(OldConditionTerm::Constant(false), true);
        let mut cursor = actual;
        let introductions = introductions
            .into_iter()
            .map(|introduction| match introduction {
                crate::kernel::LoweringIntroduction::PathFactGuard
                | crate::kernel::LoweringIntroduction::ObligationGuard
                | crate::kernel::LoweringIntroduction::WrittenImplication => {
                    let Proposition::Implies(_, body) = cursor else {
                        return Err(self.root.step_error(
                            "reported introductions do not match the nested `have` path",
                        ));
                    };
                    cursor = body;
                    Ok(introduction)
                }
                crate::kernel::LoweringIntroduction::WrittenNegation
                | crate::kernel::LoweringIntroduction::ComparisonNegation => {
                    let Proposition::Not(_) = cursor else {
                        return Err(self.root.step_error(
                            "reported introductions do not match the nested `have` path",
                        ));
                    };
                    // Negation is the end of the reported head chain.
                    cursor = &contradiction_goal;
                    Ok(introduction)
                }
                crate::kernel::LoweringIntroduction::WrittenUniversal {
                    name,
                    pointer,
                    integer,
                    ..
                } => {
                    let Proposition::ForAll {
                        var: variable,
                        sort,
                        body,
                        ..
                    } = cursor
                    else {
                        return Err(self.root.step_error(
                            "reported introductions do not match the nested `have` binders",
                        ));
                    };
                    let expected = match sort {
                        crate::kernel::Sort::Integer => (false, true),
                        crate::kernel::Sort::ProgramInt32
                        | crate::kernel::Sort::ProgramInt64
                        | crate::kernel::Sort::ProgramInteger(_)
                        | crate::kernel::Sort::Algebraic(_) => (false, false),
                        crate::kernel::Sort::ProgramPointer(_)
                        | crate::kernel::Sort::ProgramObjectPointer(_, _) => (true, false),
                        _ => {
                            return Err(self.root.step_error(
                                "reported introductions use an unsupported `have` binder sort",
                            ));
                        }
                    };
                    if (pointer, integer) != expected {
                        return Err(self.root.step_error(
                            "reported introductions use inconsistent `have` binder flags",
                        ));
                    }
                    cursor = body;
                    Ok(crate::kernel::LoweringIntroduction::WrittenUniversal {
                        name,
                        variable: **variable,
                        pointer,
                        integer,
                    })
                }
            })
            .collect::<Result<crate::kernel::LoweringIntroductions, ClickError>>()?;
        if matches!(
            cursor,
            Proposition::Implies(_, _) | Proposition::Not(_) | Proposition::ForAll { .. }
        ) {
            return Err(self
                .root
                .step_error("reported introductions omit a reachable nested `have` step"));
        }
        let mut next = self.clone();
        next.body = next
            .body
            .with_recorded_goal_introductions(Some(introductions));
        Ok(next)
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
        self.require_nested_root(&nested)?;
        let body = nested.join()?;
        self.join_nested_result(body)
    }

    /// Incorporate the direct successor produced by the nested scope's close.
    pub(in crate::surface::proof) fn join_nested_result(
        &self,
        body: Proof<'a>,
    ) -> Result<Self, ClickError> {
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("nested proof scope produced a root without lineage"));
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

    pub(in crate::surface::proof) fn require_nested_root(
        &self,
        nested: &ProofScope<'a>,
    ) -> Result<(), ClickError> {
        if !Arc::ptr_eq(&nested.root.context, &self.body.context)
            || !nested.root.state.shares_state_with(&self.body.state)
            || !Arc::ptr_eq(&nested.root.node, &self.body.node)
        {
            return Err(self
                .root
                .step_error("nested proof scope is not rooted at the current scope body"));
        }
        Ok(())
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
        condition: SyntaxProposition,
    ) -> Result<(Proof<'a>, ExecutionProofCaseSplit<'a>), ClickError> {
        self.body.split_focused_execution_if(condition)
    }

    /// Checks a model match on this body's exact marker, then retains its
    /// direct checked successor. The ordinary match driver owns the arms,
    /// their certificates, and their join; the scope still owns its close.
    pub(in crate::surface::proof) fn try_execution_match(
        &self,
        ensuring: bool,
        source_index: usize,
        advance: impl FnOnce(Proof<'a>) -> Driven<Proof<'a>>,
    ) -> Driven<Self> {
        let prepared = self.body.prepare_execution_match(ensuring, source_index)?;
        let marker = prepared.checkpoint();
        let body = match advance(prepared)? {
            Ok(body) => body,
            Err(decline) => return Ok(Err(decline)),
        };
        if !body
            .node
            .parent
            .as_ref()
            .is_some_and(|parent| Arc::ptr_eq(parent, &marker.node))
            || !matches!(body.node.step.as_deref(), Some(ProofStep::Match { .. }))
            || !Arc::ptr_eq(&body.context, &marker.context)
            || body.focused_branch_id() != marker.node.focused_branch
        {
            return Err(self.root.step_error(
                "model match did not produce one direct checked successor of this scope body",
            ));
        }
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(Ok(next))
    }

    /// Joins the two completed cases of an in-`Proof` case split as the next
    /// direct structural node of this scope, with the same lineage check
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
                .step_error("case split join produced a root without lineage"));
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
                .step_error("execution branch join produced a root without lineage"));
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

    pub(in crate::surface::proof) fn note_trace_join_continuation_arm(&self, arm: Option<usize>) {
        self.body.note_trace_join_continuation_arm(arm);
    }

    /// Applies an already-expanded logical C branch inside this resource
    /// scope without constructing or comparing a parallel certificate.
    /// Whether the scope body's frontier is the C `if` whose condition is
    /// `surface_condition`.
    pub(in crate::surface::proof) fn frontier_is_execution_branch(
        &self,
        surface_condition: &SyntaxProposition,
    ) -> Result<bool, ClickError> {
        self.body.frontier_is_execution_branch(surface_condition)
    }

    /// Incorporate the direct branch successor after the driver runs its arms.
    pub(in crate::surface::proof) fn with_completed_execution_if(
        &self,
        body: Proof<'a>,
    ) -> Result<Self, ClickError> {
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("expanded execution branch produced a root without lineage"));
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

    /// Runs the migrated `solve` search inside the nested proof and retains
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

    /// Closes without scheduling proofs. Missing resource-body facts are
    /// reported through the ordinary obligation channel for the driver.
    /// Closes a completed nested proof and makes its checked proposition
    /// available in the enclosing proof while retaining the exact body.
    pub(in crate::surface::proof) fn join(self) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("join");
        #[cfg(test)]
        CHECKED_HAVE_OPERATIONS.with(|count| count.set(count.get() + 1));
        self.join_inner()
    }

    /// Retain a completed search descendant of this proposition scope.
    pub(in crate::surface::proof) fn join_with_completed_body(
        mut self,
        body: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        if !matches!(self.structure.as_ref(), ProofScopeStructure::Have { .. }) {
            return Err(self.root.step_error("expected a proposition scope"));
        }
        body.certificate_since(&self.body.checkpoint())?;
        self.body = body;
        self.join()
    }

    /// The enclosing-frontier bookkeeping of a checked execution `have`:
    /// lowering and certificate fact recording.
    fn carry_have_into_frontier(
        execution: &mut ExecutionProofState,
        proposition: &SyntaxProposition,
        kernel: &Proposition,
    ) -> Result<(), ClickError> {
        execution
            .presentation
            .surface_propositions
            .record_lowering(proposition, kernel)?;
        execution
            .presentation
            .surface_record
            .retained_have_facts
            .push(Arc::new(kernel.clone()));
        Ok(())
    }

    fn join_inner(self) -> Result<Proof<'a>, ClickError> {
        // Entry lowering threads the original guarded judgments into later
        // declarations. Keep that exact checked judgment as well as the body
        // proved after discharging its prefix; otherwise a later declaration
        // exposes an already-proved internal guard to the user's `intro`.
        let entry_completion = self
            .loop_entry_goal
            .as_ref()
            .filter(|(_, prefix_len)| *prefix_len != 0)
            .map(|_| self.completed_loop_entry_goal())
            .transpose()?;
        match *self.structure {
            ProofScopeStructure::Have {
                proposition,
                kernel,
            } => {
                if !self.body.is_complete() {
                    return Err(self
                        .root
                        .step_error("cannot close `have`: nested proof is incomplete"));
                }
                let body = self.body.certificate();
                let mut facts = self.root.facts().clone();
                facts = facts.with_kernel_checked_have(kernel.clone());
                let mut checked_facts = vec![kernel.clone()];
                if let Some(completion) = entry_completion {
                    let guarded = completion.proposition();
                    facts = facts.with_kernel_checked_fact(guarded.clone());
                    checked_facts.push(guarded.clone());
                }

                let mut obligation =
                    self.root.focused_obligation().cloned().ok_or_else(|| {
                        self.root.step_error("`have` scope goal is no longer open")
                    })?;
                // A pure proof has no frontier or outcome to spell the fact
                // on; its proof locals carry the spelling instead.
                let mut local_spelling = None;
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
                let mut execution = execution;
                match &obligation {
                    Obligation::FunctionOutcome(outcome) => {
                        let completion = self.body.completed_proposition()?;
                        let mut retained = execution
                            .as_ref()
                            .ok_or_else(|| {
                                self.root
                                    .step_error("return proof lost its execution evidence")
                            })?
                            .as_ref()
                            .clone();
                        retained
                            .core
                            .record_return_proposition(
                                outcome.path_index,
                                completion,
                                self.root.facts(),
                            )
                            .map_err(|message| self.root.step_error(message))?;
                        execution = Some(Arc::new(retained));
                        let mut updated = outcome.clone();
                        let mut data = (*updated.data).clone();
                        data.surface_propositions
                            .record_lowering(&proposition, &kernel)?;
                        updated.data = Arc::new(data);
                        obligation = Obligation::FunctionOutcome(updated);
                    }
                    // A `have` inside a proposition scope (under `intro`, or
                    // a nested `have`) is spelled for the premise lookups
                    // later steps of that scope make, exactly as one at the
                    // scope's outcome or frontier is: a later `solve` can then
                    // cite it by its written form. The spelling is an index
                    // entry, not authority; a lookup still requires the kernel
                    // fact to be present.
                    Obligation::Proposition(goal) => {
                        if let Some(data) = &goal.outcome {
                            let mut updated = goal.clone();
                            let mut data = (**data).clone();
                            data.surface_propositions
                                .record_lowering(&proposition, &kernel)?;
                            updated.outcome = Some(Arc::new(data));
                            obligation = Obligation::Proposition(updated);
                        } else if let Some(frontier) = &execution {
                            let mut updated = (**frontier).clone();
                            updated
                                .presentation
                                .surface_propositions
                                .record_lowering(&proposition, &kernel)?;
                            execution = Some(Arc::new(updated));
                        } else {
                            local_spelling = Some((proposition.clone(), kernel.clone()));
                        }
                    }
                    Obligation::Frontier(_) => {}
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
                let trace_source =
                    crate::surface::proof_trace::enabled_for(self.root.claim_label())
                        .then(|| crate::surface::printing::source_click_proposition(&proposition));
                let mut successor = Proof {
                    site: self.root.site.clone(),
                    context: self.root.context.clone(),
                    state,
                    node: ProofNode::step_child(
                        &self.root.node,
                        self.root.focused_branch_id(),
                        Arc::new(ProofStep::Have {
                            proposition,
                            proof: Box::new(body),
                        }),
                    ),
                };
                if let Some((surface, kernel)) = &local_spelling {
                    successor = successor.with_local_surface_fact(surface, kernel)?;
                }
                if crate::surface::proof::raise_lower_audit::enabled() {
                    for fact in successor.state().checked_facts() {
                        if !fact.is_kernel_authority() {
                            successor.record_raise_lower_proposition("fact", fact, "have");
                        }
                    }
                    if let Some(goal) = successor.goal() {
                        successor.record_raise_lower_proposition("goal", goal, "have");
                    }
                }
                if let Some(source) = trace_source {
                    let location = self
                        .root
                        .site()
                        .path()
                        .unwrap_or_else(|| "checked have".into());
                    let node = crate::surface::proof_trace::trace_node_key(&successor.node);
                    let fact = successor.checked_trace_fact(kernel);
                    crate::surface::proof_trace::record(
                        node,
                        crate::surface::proof_trace::TraceStep {
                            header: format!("{location}: have {source}"),
                            source_tactic_path: self.root.site().source_tactic_path(),
                            call_source: None,
                            facts: vec![fact],
                            more_facts: 0,
                            frontier: None,
                            load: None,
                            read_equalities: Vec::new(),
                            read_context_changed: false,
                            transport: None,
                            resources: Vec::new(),
                            more_resources: 0,
                            origin: crate::surface::proof_trace::smart_origin(),
                            chosen: None,
                            forgotten_cells: Vec::new(),
                            history_stops: Vec::new(),
                        },
                    );
                    crate::surface::proof_trace::record_body(
                        node,
                        crate::surface::proof_trace::TraceBody {
                            lineage: trace_path_lineage(
                                &self.body.node,
                                self.body.focused_branch_id(),
                            ),
                            _retained: Box::new(self.body.node.clone()),
                        },
                    );
                }
                Ok(successor)
            }
            ProofScopeStructure::Open {
                ref resource,
                source_index,
                ref restoration,
            } => self.close_open_scope_from(&self.body, resource, source_index, restoration),
        }
    }

    /// Closes this `with` scope from `body`, this scope's body or one that
    /// has gone on to prove a body fact the closing fold leaves open; the
    /// recorded scope keeps this scope's own body. At function exit the
    /// close is deferred until the outcome proof.
    pub(in crate::surface::proof) fn close_open_scope_from(
        &self,
        body: &Proof<'a>,
        resource: &ResourceClause,
        source_index: usize,
        restoration: &OpenResourceRestoration,
    ) -> Result<Proof<'a>, ClickError> {
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("a resource scope can only be created from an execution Proof")
        };
        let body_certificate = self.body.certificate();
        let deferred = body.is_at_function_exit();
        let state = if !deferred && let OpenResourceRestoration::Named(instance) = restoration {
            if body.holds_open_instance(instance)? {
                body.state.clone()
            } else {
                body.restore_open_instance(resource, instance)?.state
            }
        } else {
            let mut execution = body
                .branch_execution()
                .cloned()
                .map(Arc::unwrap_or_clone)
                .ok_or_else(|| {
                    self.root
                        .step_error("with block lost its execution frontier")
                })?;
            let mut facts = body.facts().clone();
            if deferred {
                // Terminal matches already route deferred operations to their
                // lexical arms. Other scopes need their close to mark the end
                // of any operations they added after execution.
                let retain_deferred_body = self.root.branch_execution().is_some_and(|root| {
                    execution.presentation.post_execution_tactics.len()
                        > root.presentation.post_execution_tactics.len()
                }) && !ends_in_terminal_match(body_certificate.steps());
                execution.presentation.defer_post_execution(
                    context.tactic_index,
                    source_index,
                    PostExecutionTactic::CloseOpen {
                        resource: resource.clone(),
                        restoration: Some(restoration.clone()),
                        retain_deferred_body,
                    },
                    Some(body.state.locals().values.clone()),
                );
            } else if let OpenResourceRestoration::Declared {
                preserve_exposed_body,
            } = restoration
            {
                let before_facts = facts.clone();
                let pre_state = context
                    .old_reference_state(&execution.core.frontier, &execution.core.state)
                    .clone();
                let checked = close_open_resource_for_proof(
                    context.resource_environment,
                    resource,
                    context.claim_label,
                    context.tactic_index,
                    facts.clone(),
                    context.parameter_binding(),
                    &pre_state,
                    (*execution.core.state).clone(),
                    context.spec_definitions,
                    *preserve_exposed_body,
                )?;
                let lowered = lower_resource_clause_at_state(
                    resource,
                    context.parameter_binding(),
                    &checked.state,
                )?;
                // The `with(...)` clause spells no access, so it lowers
                // as owned, but the head returns to the closed state
                // with the access it was opened with. Record the head as
                // the state holds it, so a viewed open closes through the
                // same evidence an owned one does; the deferred close at
                // function exit already folds against the state.
                let selected = checked
                    .state
                    .resources()
                    .facts()
                    .iter()
                    .find(|fact| fact.resource() == lowered.resource())
                    .cloned()
                    .unwrap_or(lowered);
                let recorded = execution.core.record_resource_rewrite(
                    context.function,
                    context.arguments,
                    &before_facts,
                    &selected,
                    &checked.state,
                    &checked.facts,
                );
                recorded.map_err(|message| {
                    self.root.step_error(format!(
                        "kernel rejected checked resource close: {}",
                        spell_resource_clause(resource, &message)
                    ))
                })?;
                facts = checked.facts;
                execution.core.state = checked.state.into();
            }
            body.state
                .publish_checked_frontier_transition(
                    facts,
                    execution,
                    self.introduced_facts.clone(),
                    self.introduced_facts.clone(),
                )
                .map_err(|error| match error {
                    ExecutionUpdateError::NotFrontier | ExecutionUpdateError::MissingExecution => {
                        self.root
                            .step_error("with block lost its execution frontier")
                    }
                    ExecutionUpdateError::NotLoopBody
                    | ExecutionUpdateError::InvariantsAlreadyClosed => {
                        unreachable!("open-scope publication checks only frontier ownership")
                    }
                })?
        };
        // The successor's goal map came from the scope body, whose
        // cursor may have moved through a decided branch.
        let focused_branch = body.focused_branch_id();
        Ok(Proof {
            site: self.root.site.clone(),
            context: self.root.context.clone(),
            state,
            node: ProofNode::step_child(
                &self.root.node,
                focused_branch,
                Arc::new(ProofStep::Open {
                    resource: resource.clone(),
                    proof: Box::new(body_certificate),
                    deferred_tail: None,
                }),
            ),
        })
    }
}

impl<'a> Proof<'a> {
    /// The membership implication must be the next head after opening a
    /// written range binder. Leave any intervening lowering guard explicit.
    pub(in crate::surface::proof) fn opens_scoped_range(&self, introduced: &Self) -> bool {
        matches!(
            self.surface_goal(),
            Some(SyntaxProposition::RangeAll { .. })
        ) && matches!(self.goal(), Some(Proposition::ForAll { .. }))
            && introduced.proposition_obligation().is_some_and(|goal| {
                matches!(goal.kernel(), Proposition::Implies(_, _))
                    && matches!(
                        goal.introductions.head(),
                        None | Some(crate::kernel::LoweringIntroduction::WrittenImplication)
                    )
            })
    }

    /// Retain a generated introduction over the checked continuation that
    /// finished its goal. A written range's scope also opens its membership
    /// guard, so absorb that introduction when the continuation took it.
    pub(in crate::surface::proof) fn finish_generated_intro(
        &self,
        introduced: &Self,
        completed: Self,
    ) -> Result<Self, ClickError> {
        let range = self.opens_scoped_range(introduced);
        let continuation = completed.certificate_since(&introduced.checkpoint())?;
        let body = if range {
            match continuation.steps() {
                [ProofStep::Intro, body @ ..] => ProofCertificate::from_steps(body.to_vec())?,
                [ProofStep::IntroBlock { binder: None, body }] => body.as_ref().clone(),
                // If search proved the entire membership implication, retain
                // that proof as a fact inside the scope opened by the guard.
                // Recheck the shortened goal before publishing the replacement.
                _ => {
                    let Some(proposition) = introduced.surface_goal().cloned() else {
                        return Ok(completed);
                    };
                    let tactics = [
                        ProofTactic::Have(ProofHave {
                            proposition: proposition.clone(),
                            proof: SourceProof::Script(continuation.to_proof_tactics()),
                        }),
                        ProofTactic::ApplyFact(proposition),
                        ProofTactic::Known,
                    ];
                    let opened = introduced.driver().apply_step(ProofStep::Intro)?;
                    let Some(Some(closed)) = attempt::candidate_outcome(
                        opened.driver().try_generated_linear_script(&tactics),
                    )?
                    else {
                        return Ok(completed);
                    };
                    return self.finish_scoped_intro(introduced, &opened, closed);
                }
            }
        } else {
            continuation
        };
        self.retain_scoped_intro(introduced, body, completed)
    }

    /// Retain a checked binder or premise, its optional range guard, and
    /// the body as a single scoped step.
    pub(in crate::surface::proof) fn finish_scoped_intro(
        &self,
        introduced: &Self,
        opened: &Self,
        completed: Self,
    ) -> Result<Self, ClickError> {
        let body = completed.certificate_since(&opened.checkpoint())?;
        self.retain_scoped_intro(introduced, body, completed)
    }

    fn retain_scoped_intro(
        &self,
        introduced: &Self,
        body: ProofCertificate,
        mut completed: Self,
    ) -> Result<Self, ClickError> {
        let opening = introduced.certificate_since(&self.checkpoint())?;
        let binder = match opening.steps() {
            [ProofStep::Intro] => None,
            [ProofStep::IntroAs(name)] => Some(SurfaceBinder::Written(name.clone())),
            [ProofStep::IntroBinder(binder)] => Some(binder.clone()),
            _ => return Err(self.step_error("scoped intro did not record its introduction")),
        };
        completed.state = completed.state.with_locals(self.state.locals().clone());
        completed.node = ProofNode::step_child(
            &self.node,
            self.focused_branch_id(),
            Arc::new(ProofStep::IntroBlock {
                binder,
                body: Box::new(body),
            }),
        );
        Ok(completed)
    }

    /// Retain a completed descendant of this focused proposition goal as a `have`.
    /// The checked descendant supplies the evidence; its certificate is only
    /// serialized evidence and is never executed again.
    ///
    /// `conclusions` are the completed application's other guarantees as the
    /// caller would write them, in the order the application produced them.
    /// An application adds every guarantee of its theorem, so each one the
    /// completed step actually added is retained beside the goal as its own
    /// `have` over the same body. Nothing is checked again: a conclusion is
    /// published only when it is one of the facts the checked step reported
    /// adding, matched in one ordered pass.
    pub(in crate::surface::proof) fn retain_completed_goal(
        &self,
        completed: &Self,
        conclusions: &[SyntaxProposition],
    ) -> Result<Self, ClickError> {
        if !Arc::ptr_eq(&self.context, &completed.context)
            || self.focused_branch_id() != completed.focused_branch_id()
            || !completed.focused_discharged()
        {
            return Err(
                self.step_error("completed application does not belong to this proposition goal")
            );
        }
        let body = completed.certificate_since(&self.checkpoint())?;
        let proposition = self
            .surface_goal()
            .cloned()
            .ok_or_else(|| self.step_error("completed application has no source goal"))?;
        let kernel = self
            .goal()
            .cloned()
            .ok_or_else(|| self.step_error("completed application has no kernel goal"))?;
        let mut lowered = self.lower_surface_proposition(&proposition, "retained application")?;
        if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, &kernel) {
            // A bare spelling can still name a fact from an enclosing,
            // earlier state. This goal belongs to the current fixed-state
            // frontier; validate its actual source meaning before refusing
            // the stale recorded spelling. The exact judgment check remains.
            lowered =
                self.lower_surface_proposition_direct(&proposition, "retained application")?;
        }
        if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, &kernel) {
            return Err(
                self.step_error("retained application source does not match its checked goal")
            );
        }
        let branch = self
            .focused_branch()
            .ok_or_else(|| self.step_error("application parent has no open branch"))?;
        let state = self
            .state
            .publish_checked_focused_transition(
                self.focused_obligation().cloned().unwrap(),
                self.facts().with_kernel_checked_fact(kernel.clone()),
                branch.state.execution.clone(),
                vec![kernel.clone()],
                vec![kernel],
            )
            .map_err(|_| self.step_error("application parent has no open goal"))?;
        let mut retained = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(
                &self.node,
                self.focused_branch_id(),
                Arc::new(ProofStep::Have {
                    proposition,
                    proof: Box::new(body.clone()),
                }),
            ),
        };

        // The step reports its added facts in conclusion order, omitting any
        // the context already held, so one forward pass pairs each written
        // conclusion with the fact it produced.
        let mut added = completed.state.added_facts().iter().peekable();
        for conclusion in conclusions {
            let Some(fact) = added.peek() else {
                break;
            };
            let Ok(lowered) = self.lower_surface_proposition(conclusion, "retained application")
            else {
                continue;
            };
            if &lowered != *fact {
                continue;
            }
            added.next();
            if retained.facts().contains(&lowered) {
                continue;
            }
            let branch = retained
                .focused_branch()
                .ok_or_else(|| self.step_error("application parent has no open branch"))?;
            let state = retained
                .state
                .publish_checked_focused_transition(
                    retained.focused_obligation().cloned().unwrap(),
                    retained.facts().with_kernel_checked_fact(lowered.clone()),
                    branch.state.execution.clone(),
                    vec![lowered.clone()],
                    vec![lowered],
                )
                .map_err(|_| self.step_error("application parent has no open goal"))?;
            retained = Self {
                site: retained.site.clone(),
                context: retained.context.clone(),
                state,
                node: ProofNode::step_child(
                    &retained.node,
                    retained.focused_branch_id(),
                    Arc::new(ProofStep::Have {
                        proposition: conclusion.clone(),
                        proof: Box::new(body.clone()),
                    }),
                ),
            };
        }
        Ok(retained)
    }
}

#[path = "../driver/scopes.rs"]
mod driver;
