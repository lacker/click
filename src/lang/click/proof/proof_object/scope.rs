//! `ProofScope`: scoped proof construction over a parent `Proof`.

use super::*;

impl<'a> ProofScope<'a> {
    pub(in crate::lang::click::proof) fn is_complete(&self) -> bool {
        self.body.is_complete() || self.body.focused_loop_effect_closed()
    }

    #[cfg(test)]
    pub(in crate::lang::click::proof) fn body(&self) -> &Proof<'a> {
        &self.body
    }

    /// Attributes the next checked execution operation inside this scope to
    /// its own source tactic without changing the enclosing scope root.
    pub(in crate::lang::click::proof) fn with_execution_tactic_index(
        &self,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.body = self.body.with_execution_tactic_index(tactic_index)?;
        Ok(next)
    }

    /// Attaches the explicit source script proving a `have` scope so its
    /// join can carry the script's standard-theorem authority.
    pub(in crate::lang::click::proof) fn with_have_script(
        mut self,
        tactics: &[ProofTactic],
    ) -> Self {
        if let ProofScopeStructure::Have { script, .. } = self.structure.as_mut() {
            *script = Some(tactics.to_vec());
        }
        self
    }

    /// Opens another composite resource from this scope's current checked
    /// body. The returned nested scope can only rejoin through `join_nested`,
    /// which checks that it descends from this exact body.
    pub(in crate::lang::click::proof) fn begin_open(
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
    pub(in crate::lang::click::proof) fn begin_have(
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
    pub(in crate::lang::click::proof) fn join_nested(
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
        // A nested resource may contain the terminal structural-effect frame.
        // Close its representation without retiring that sealed frontier;
        // only the outermost resource join owns final discharge.
        let body = nested.join_inner(false)?;
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
    pub(in crate::lang::click::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step_with_origin_mode(
            step,
            None,
            matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }),
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

    /// Opens the C branch at this scope body's frontier as an in-`Proof`
    /// sibling split. The returned proof advances by focusing each recorded
    /// arm; `join_execution_split` accepts the direct joined successor.
    pub(in crate::lang::click::proof) fn split_execution_branch(
        &self,
    ) -> Result<(Proof<'a>, ExecutionSplit<'a>), ClickError> {
        self.body.split_focused_execution_branch()
    }

    /// Opens a proof-level case split at this scope body's frontier. The
    /// returned proof advances by focusing each recorded case;
    /// `join_execution_if_terminal` accepts the direct joined successor.
    pub(in crate::lang::click::proof) fn split_execution_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Proof<'a>, ExecutionProofCaseSplit<'a>), ClickError> {
        self.body.split_focused_execution_if(condition)
    }

    /// Joins the two completed cases of an in-`Proof` case split as the next
    /// direct structural node of this scope, with the same provenance check
    /// as `join_execution_split`.
    pub(in crate::lang::click::proof) fn join_execution_if_terminal(
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
    pub(in crate::lang::click::proof) fn join_execution_split(
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
    pub(in crate::lang::click::proof) fn frontier_is_execution_branch(
        &self,
        surface_condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        self.body.frontier_is_execution_branch(surface_condition)
    }

    pub(in crate::lang::click::proof) fn apply_expanded_execution_if(
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

    pub(in crate::lang::click::proof) fn checkpoint(&self) -> ProofCheckpoint<'a> {
        self.body.checkpoint()
    }

    pub(in crate::lang::click::proof) fn certificate_since(
        &self,
        checkpoint: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        self.body.certificate_since(checkpoint)
    }

    /// Applies an already-expanded branch-shaped contextual frame through the
    /// same typed outcome-partition plan used by smart frame search. The
    /// source driver supplies only Surface operations; no certificate is
    /// constructed or interpreted at this compatibility boundary.
    pub(in crate::lang::click::proof) fn apply_contextual_frame_tactics_at(
        &self,
        condition: ClickProposition,
        then_tactics: Vec<ProofTactic>,
        else_tactics: Vec<ProofTactic>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let Ok(then_leaf) = ContextualFrameLeafPlan::from_surface_tactics(then_tactics) else {
            return Ok(None);
        };
        let Ok(else_leaf) = ContextualFrameLeafPlan::from_surface_tactics(else_tactics) else {
            return Ok(None);
        };
        let plan = ContextualFramePlan::If {
            condition,
            then_plan: Box::new(ContextualFramePlan::Leaf(then_leaf)),
            else_plan: Box::new(ContextualFramePlan::Leaf(else_leaf)),
        };
        let body = self.body.apply_contextual_frame_plan(
            &plan,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )?;
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Applies a source-owned proof step inside the scope. Terminal steps use
    /// the site only to schedule already-checked ordered outcome work.
    pub(in crate::lang::click::proof) fn apply_step_at(
        &self,
        step: ProofStep,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step_with_origin_mode(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
            matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }),
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

    /// Checks one proof-level `if` within a loop-effect resource-scope tree.
    /// The callbacks must retire their selected sibling goal, either by
    /// closing a terminal leaf or by recursively joining another `if`. This
    /// operation owns the split and structured join; the source driver only
    /// selects the two already-lowered arm certificates.
    pub(in crate::lang::click::proof) fn apply_loop_effect_if<Then, Else>(
        scopes: &[Self],
        current: Self,
        condition: ClickProposition,
        apply_then: Then,
        apply_else: Else,
    ) -> Result<Proof<'a>, ClickError>
    where
        Then: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
        Else: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
    {
        Self::validate_loop_effect_open_scopes(scopes)?;
        let inner = scopes
            .last()
            .expect("the nonempty leading scope chain has an inner scope");
        if !Arc::ptr_eq(&current.root.context, &inner.root.context)
            || !current.root.state.shares_state_with(&inner.root.state)
            || !Arc::ptr_eq(&current.root.node, &inner.root.node)
        {
            return Err(inner
                .root
                .step_error("loop-effect branch cursor left its innermost open scope"));
        }
        let mut then_scope = current.clone();
        let mut else_scope = current.clone();
        current.body.apply_execution_if_with(
            condition,
            |then_body| {
                then_scope.body = then_body;
                apply_then(then_scope)
            },
            |else_body| {
                else_scope.body = else_body;
                apply_else(else_scope)
            },
        )
    }

    /// Checks one logical `cases` scope within a loop-effect resource tree.
    /// Each callback owns exactly one disjunct sibling; resource
    /// representations close independently before the audited logical join.
    pub(in crate::lang::click::proof) fn apply_loop_effect_cases<Left, Right>(
        scopes: &[Self],
        current: Self,
        disjunction: ClickProposition,
        apply_left: Left,
        apply_right: Right,
    ) -> Result<Proof<'a>, ClickError>
    where
        Left: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
        Right: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
    {
        Self::validate_loop_effect_open_scopes(scopes)?;
        let inner = scopes
            .last()
            .expect("the nonempty leading scope chain has an inner scope");
        if !Arc::ptr_eq(&current.root.context, &inner.root.context)
            || !current.root.state.shares_state_with(&inner.root.state)
            || !Arc::ptr_eq(&current.root.node, &inner.root.node)
        {
            return Err(inner
                .root
                .step_error("loop-effect cases cursor left its innermost open scope"));
        }
        let mut left_scope = current.clone();
        let mut right_scope = current.clone();
        current.body.apply_execution_cases_with(
            disjunction,
            |left_body| {
                left_scope.body = left_body;
                apply_left(left_scope)
            },
            |right_body| {
                right_scope.body = right_body;
                apply_right(right_scope)
            },
        )
    }

    /// Closes every currently open resource representation on one terminal
    /// branch, then retires that leaf goal. No surface step is synthesized:
    /// the leaf operations and later audited `if` joins retain the exact
    /// provenance, while resource closure is the semantics of the enclosing
    /// `open` nodes.
    pub(in crate::lang::click::proof) fn complete_loop_effect_leaf(
        scopes: &[Self],
        leaf: Self,
    ) -> Result<Proof<'a>, ClickError> {
        Self::validate_loop_effect_open_scopes(scopes)?;
        let inner = scopes
            .last()
            .expect("the nonempty leading scope chain has an inner scope");
        if !Arc::ptr_eq(&leaf.root.context, &inner.root.context)
            || !leaf.root.state.shares_state_with(&inner.root.state)
            || !Arc::ptr_eq(&leaf.root.node, &inner.root.node)
        {
            return Err(inner
                .root
                .step_error("loop-effect leaf left its innermost open scope"));
        }
        let mut body = leaf.body;
        for scope in scopes.iter().rev() {
            body = scope.close_open_resource_on_focused_branch(body)?;
        }
        scopes[0].discharge_closed_loop_effect_branch(body)
    }

    /// Retains a checked branch subtree inside the open scopes introduced at
    /// `wrap_from`. Earlier scopes remain semantic ancestors and are wrapped
    /// by their own caller. Prefix operations before each nested `open` come
    /// from that child scope's checked root lineage, so serialization loses
    /// neither scope-local work nor branch structure.
    pub(in crate::lang::click::proof) fn retain_loop_effect_open_scopes(
        scopes: &[Self],
        wrap_from: usize,
        joined: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        Self::validate_loop_effect_open_scopes(scopes)?;
        if wrap_from > scopes.len() {
            return Err(scopes[0]
                .root
                .step_error("loop-effect open-scope provenance boundary is out of range"));
        }
        if wrap_from == scopes.len() {
            return Ok(joined);
        }

        let mut body = joined.certificate();
        for index in ((wrap_from + 1)..scopes.len()).rev() {
            let scope = &scopes[index];
            let ProofScopeStructure::Open { resource, .. } = scope.structure.as_ref() else {
                unreachable!("the scope kinds were checked above")
            };
            let mut steps = scope.root.certificate().steps().to_vec();
            steps.push(ProofStep::Open {
                resource: resource.clone(),
                proof: Box::new(body),
            });
            body = ProofCertificate::from_steps(steps);
        }
        let outer = &scopes[wrap_from];
        let ProofScopeStructure::Open { resource, .. } = outer.structure.as_ref() else {
            unreachable!("the scope kind was checked above")
        };
        let mut introduced_facts = PersistentOrderedSet::default();
        for scope in &scopes[wrap_from..] {
            for fact in &scope.introduced_facts {
                introduced_facts.insert(fact.clone());
            }
        }
        let introduced_facts = introduced_facts.to_vec();
        let state = joined
            .state
            .restore_allocated_cursor_with_fact_deltas(
                outer.root.focused_branch_id(),
                introduced_facts.clone(),
                introduced_facts,
            )
            .map_err(|error| match error {
                ProofFocusError::NotAllocated => outer
                    .root
                    .step_error("open-scope join lost its allocated parent branch"),
                ProofFocusError::NotOpen => {
                    unreachable!("allocated-cursor restoration does not require an open branch")
                }
            })?;
        Ok(Proof {
            context: outer.root.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(outer.root.node.clone()),
                step: Some(Arc::new(ProofStep::Open {
                    resource: resource.clone(),
                    proof: Box::new(body),
                })),
                focused_branch: outer.root.focused_branch_id(),
                depth: outer.root.node.depth + 1,
            }),
        })
    }

    pub(super) fn validate_loop_effect_open_scopes(scopes: &[Self]) -> Result<(), ClickError> {
        let Some(outer) = scopes.first() else {
            return Err(ClickError::new(
                "a loop-effect branch requires at least one open resource scope",
            ));
        };
        if scopes
            .iter()
            .any(|scope| !matches!(scope.structure.as_ref(), ProofScopeStructure::Open { .. }))
        {
            return Err(outer
                .root
                .step_error("a loop-effect branch requires open resource scopes"));
        }
        for pair in scopes.windows(2) {
            let [parent, child] = pair else {
                unreachable!("a two-element scope window has two entries")
            };
            if !Arc::ptr_eq(&child.root.context, &parent.body.context)
                || !child.root.state.shares_state_with(&parent.body.state)
                || !Arc::ptr_eq(&child.root.node, &parent.body.node)
            {
                return Err(outer
                    .root
                    .step_error("leading open scopes do not form one checked Proof chain"));
            }
        }
        Ok(())
    }

    /// Closes this open resource on the currently focused branch terminal branch
    /// without yet retiring the branch goal. This is the per-arm half of
    /// a recursive loop-effect branch tree; logical joins are allowed only after
    /// both independently checked representations have closed.
    pub(super) fn close_open_resource_on_focused_branch(
        &self,
        body: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        let ProofScopeStructure::Open {
            resource,
            source_index,
            preserve_exposed_body,
        } = self.structure.as_ref()
        else {
            unreachable!("only an open scope closes a resource representation")
        };
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("an open scope can only be created from an execution Proof")
        };
        if !body.focused_loop_effect_closed() {
            return Err(self.root.step_error(
                "cannot close an open resource branch before its loop-effect goal is proved",
            ));
        }
        let mut execution = body
            .branch_execution()
            .cloned()
            .map(Arc::unwrap_or_clone)
            .ok_or_else(|| {
                self.root
                    .step_error("open resource branch lost its execution frontier")
            })?;
        let mut facts = body.facts().clone();
        if execution.core.frontier.is_at_function_exit() {
            execution.defer_post_execution(
                context.tactic_index,
                *source_index,
                PostExecutionTactic::CloseOpen {
                    resource: resource.clone(),
                    preserve_exposed_body: *preserve_exposed_body,
                },
            );
        } else {
            let pre_state = context
                .old_reference_state(&execution.core.frontier, &execution.core.state)
                .clone();
            let checked = close_open_resource_for_proof(
                context.resource_environment,
                resource,
                context.claim_label,
                context.tactic_index,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                &pre_state,
                execution.core.state.into_value(),
                context.predicate_environment,
                context.click_function_environment,
                &execution.core.unfolded_predicates,
                *preserve_exposed_body,
            )?;
            facts = checked.facts;
            execution.core.state = checked.state.into();
        }
        let state = body
            .state
            .publish_checked_frontier_transition(
                facts,
                execution,
                body.added_facts().to_vec(),
                body.checked_facts().to_vec(),
                false,
            )
            .map_err(|error| match error {
                ExecutionUpdateError::NotFrontier | ExecutionUpdateError::MissingExecution => self
                    .root
                    .step_error("open resource branch lost its execution frontier"),
                ExecutionUpdateError::LoopEffectNotClosed
                | ExecutionUpdateError::ClosedLoopEffect
                | ExecutionUpdateError::NotLoopBody
                | ExecutionUpdateError::InvariantsAlreadyClosed => unreachable!(
                    "resource close publication preserves an open loop-effect frontier"
                ),
            })?;
        Ok(Proof {
            context: body.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(body.node.clone()),
                step: None,
                focused_branch: body.focused_branch_id(),
                depth: body.node.depth,
            }),
        })
    }

    /// Retires one sealed effect arm only after its resource representation
    /// has closed. The marker carries no surface step: closure and discharge
    /// are the audited exit semantics of the enclosing `open` and `if`.
    pub(super) fn discharge_closed_loop_effect_branch(
        &self,
        body: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        let state = body
            .state
            .discharge_closed_loop_effect()
            .map_err(|error| match error {
                ExecutionUpdateError::LoopEffectNotClosed => self
                    .root
                    .step_error("cannot discharge an unfinished loop-effect branch"),
                ExecutionUpdateError::NotFrontier | ExecutionUpdateError::MissingExecution => self
                    .root
                    .step_error("loop-effect branch lost its execution frontier"),
                ExecutionUpdateError::ClosedLoopEffect
                | ExecutionUpdateError::NotLoopBody
                | ExecutionUpdateError::InvariantsAlreadyClosed => {
                    unreachable!("loop-effect discharge checks only frontier ownership and closure")
                }
            })?;
        Ok(Proof {
            context: body.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(body.node.clone()),
                step: None,
                focused_branch: body.focused_branch_id(),
                depth: body.node.depth,
            }),
        })
    }

    /// Reports whether a terminal frame step can use the checked Proof-owned
    /// operation. Unsupported forms leave this scope untouched so a larger
    /// transactional Proof attempt can decline without observing a partial
    /// transition.
    pub(in crate::lang::click::proof) fn supports_checked_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        self.body
            .supports_checked_execution_frame_using(region, premises)
    }

    /// Searches for a frame certificate and submits the selected candidate to
    /// the owned Proof exactly once. The cheap exact-empty candidate goes
    /// first; a miss invokes contextual derivation search, which may add
    /// explicit checked `have` steps before the terminal `FrameUsing`.
    pub(in crate::lang::click::proof) fn try_smart_frame_at(
        &self,
        region: Option<&CodeRegionRef>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let checkpoint = self.body.checkpoint();
        let Some(body) = self
            .body
            .try_smart_frame_at(region, tactic_index, source_index)?
        else {
            return Ok(None);
        };
        let candidate = body.certificate_since(&checkpoint)?;
        let mut next = self.clone();
        for step in candidate.steps() {
            if let ProofStep::Have { proposition, .. } = step {
                let fact = body.lower_surface_proposition(
                    proposition,
                    "smart frame intermediate proposition",
                )?;
                if !next.introduced_facts.contains(&fact) {
                    next.introduced_facts.push(fact);
                }
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the narrow linear `execute` search inside this scope.
    ///
    /// Each selected statement is checked and retained by
    /// `Proof::try_statement_step`; the search never mutates a second
    /// semantic context or reconstructs steps from its aftermath. A partial
    /// advance is discarded unless the checked descendant reaches function
    /// exit, so unsupported frontiers return a bounded miss to the caller.
    pub(in crate::lang::click::proof) fn try_linear_execute(
        &self,
    ) -> Result<Option<Self>, ClickError> {
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
    pub(in crate::lang::click::proof) fn try_theorem_application(
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
    pub(in crate::lang::click::proof) fn try_fact_transport(
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
    pub(in crate::lang::click::proof) fn try_linear_execute_until(
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
    pub(in crate::lang::click::proof) fn try_direct_logical_closure(
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
    pub(in crate::lang::click::proof) fn is_at_function_exit(&self) -> bool {
        self.body.is_at_function_exit()
    }

    /// Schedules an ordered outcome operation written inside the scope
    /// body after execution reached function exit; the body's deferred
    /// operations follow the scope through its join to finalization.
    pub(in crate::lang::click::proof) fn defer_post_execution_source_tactic(
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

    pub(in crate::lang::click::proof) fn try_simp_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
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

    /// Runs one supported source script inside the owned nested body and
    /// retains its already-checked descendant.
    pub(in crate::lang::click::proof) fn try_linear_script(
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
    pub(in crate::lang::click::proof) fn try_authoritative_linear_script(
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
    pub(in crate::lang::click::proof) fn try_planned_linear_script(
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
    pub(in crate::lang::click::proof) fn try_linear_smart_script(
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
    pub(in crate::lang::click::proof) fn join(self) -> Result<Proof<'a>, ClickError> {
        self.join_inner(true)
    }

    /// The enclosing-frontier bookkeeping of a checked execution `have`,
    /// shared in meaning with `check_mid_execution_have`: lowering and
    /// certificate fact recording, plus function-entry derivation authority
    /// when execution has not yet left the entry state. Every lookup uses
    /// the frontier's indexed fact context; no fact vector is rebuilt.
    fn carry_have_into_frontier(
        context: &ExecutionProofContext<'a>,
        execution: &mut ExecutionProofState,
        root_facts: &ProofFacts,
        proposition: &ClickProposition,
        kernel: &Proposition,
        script: Option<&[ProofTactic]>,
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
        let at_entry = execution
            .core
            .frontier
            .execution_start_state
            .as_ref()
            .is_none_or(|start| start == &*execution.core.state);
        if !at_entry {
            return Ok(());
        }
        let assumptions = root_facts.assumptions();
        for tactic in script.into_iter().flatten() {
            let ProofTactic::ApplyTheoremUsing { application, .. } = tactic else {
                continue;
            };
            let pre_state = context
                .old_reference_state(&execution.core.frontier, &execution.core.state)
                .clone();
            if let Some(derivation) =
                kernel_standard_theorem_derivation_in_current_state_with_assumptions(
                    context.theorem_environment,
                    application,
                    context.parsed_function.parameters(),
                    context.arguments,
                    &pre_state,
                    &execution.core.state,
                    &execution.presentation.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                    assumptions,
                )?
            {
                let mut conclusion = derivation.proposition();
                while let Proposition::Implies(_, body) = conclusion {
                    conclusion = body;
                }
                execution
                    .core
                    .function_entry_execution_prerequisites
                    .insert(conclusion.clone());
                execution.core.function_entry_derivations.insert(derivation);
            }
        }
        if let Some(derivation) =
            crate::kernel::prove_pure_proposition_from_context(assumptions, kernel)
        {
            execution
                .core
                .function_entry_execution_prerequisites
                .insert(kernel.clone());
            execution.core.function_entry_derivations.insert(derivation);
        }
        Ok(())
    }

    /// Joins one scope, optionally retiring a sealed structural-effect goal.
    /// Nested resource joins pass `false` so all enclosing resource
    /// representations close before the outermost join discharges the goal.
    pub(super) fn join_inner(
        self,
        discharge_closed_loop_effect: bool,
    ) -> Result<Proof<'a>, ClickError> {
        match *self.structure {
            ProofScopeStructure::Have {
                proposition,
                kernel,
                script,
            } => {
                if !self.body.is_complete() {
                    return Err(self
                        .root
                        .step_error("cannot close `have`: nested proof is incomplete"));
                }
                let body = self.body.certificate();
                let mut facts = self.root.facts().clone();
                facts = facts.with_fact(kernel.clone());
                let mut goals = match (self.root.context.as_ref(), self.root.focused_obligation()) {
                    // A `have` at an execution frontier publishes what the
                    // shared mid-execution law publishes: the proposition's
                    // lowering, its certificate fact, and any function-entry
                    // authority the checked fact or an explicit theorem
                    // application establishes for later statement checks.
                    (ProofContext::Execution(context), Some(Obligation::Frontier(_))) => {
                        let mut execution = self
                            .root
                            .branch_execution()
                            .cloned()
                            .map(Arc::unwrap_or_clone)
                            .ok_or_else(|| {
                                self.root
                                    .step_error("`have` scope lost its execution frontier")
                            })?;
                        Self::carry_have_into_frontier(
                            context,
                            &mut execution,
                            self.root.facts(),
                            &proposition,
                            &kernel,
                            script.as_deref(),
                        )?;
                        self.root.state.open_branches.replace_frontier_at(
                            self.root.focused_branch_id(),
                            facts,
                            execution,
                        )
                    }
                    _ => self
                        .root
                        .state
                        .open_branches
                        .with_facts_at(self.root.focused_branch_id(), facts),
                };
                if let Some(Obligation::FunctionOutcome(outcome)) =
                    goals.obligation(self.root.focused_branch_id()).cloned()
                {
                    let mut updated = outcome;
                    let mut data = (*updated.data).clone();
                    data.surface_propositions
                        .record_lowering(&proposition, &kernel)?;
                    updated.data = Arc::new(data);
                    goals = goals.replace_obligation_at(
                        self.root.focused_branch_id(),
                        Obligation::FunctionOutcome(updated),
                    );
                }
                Ok(Proof {
                    context: self.root.context.clone(),
                    state: KernelProofObject::new(
                        ProofState {
                            locals: self.root.state.locals.clone(),
                            open_branches: goals,
                            added_facts: Arc::new(vec![kernel.clone()]),
                            checked_facts: Arc::new(vec![kernel]),
                        },
                        self.root.focused_branch_id(),
                    ),
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
                let loop_effect_closed = self.body.focused_loop_effect_closed();
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
                    execution.defer_post_execution(
                        context.tactic_index,
                        source_index,
                        PostExecutionTactic::CloseOpen {
                            resource: resource.clone(),
                            preserve_exposed_body,
                        },
                    );
                } else {
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
                        execution.core.state.into_value(),
                        context.predicate_environment,
                        context.click_function_environment,
                        &execution.core.unfolded_predicates,
                        preserve_exposed_body,
                    )?;
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
                        discharge_closed_loop_effect && loop_effect_closed,
                    )
                    .map_err(|error| match error {
                        ExecutionUpdateError::NotFrontier
                        | ExecutionUpdateError::MissingExecution => self
                            .root
                            .step_error("open scope body lost its execution frontier"),
                        ExecutionUpdateError::LoopEffectNotClosed => self
                            .root
                            .step_error("cannot discharge an unfinished loop-effect branch"),
                        ExecutionUpdateError::ClosedLoopEffect
                        | ExecutionUpdateError::NotLoopBody
                        | ExecutionUpdateError::InvariantsAlreadyClosed => unreachable!(
                            "open-scope publication checks only frontier ownership and closure"
                        ),
                    })?;
                // The successor's goal map came from the scope body, whose
                // cursor may have moved through a decided branch.
                let focused_branch = self.body.focused_branch_id();
                Ok(Proof {
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
