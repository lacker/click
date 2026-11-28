//! Proof script orchestration; explicit operations remain on Proof.
use super::*;
use crate::surface::proof::driver::ProofDriver;

impl<'p, 'a> ProofDriver<'p, ProofScope<'a>> {
    pub(in crate::surface::proof) fn try_ordinary_fact_transport(
        &self,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_ordinary_fact_transport(
            &self.proof.body,
            source,
            target,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_preserve_selected_fact(
        &self,
        conclusion: &SyntaxProposition,
        source: SyntaxProposition,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_preserve_selected_fact(
            &self.proof.body,
            conclusion,
            source,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_struct_field_equality(
        &self,
        equality: &SyntaxProposition,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_struct_field_equality(
            &self.proof.body,
            equality,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Replay one operation bound inside the selected have body.
    pub(in crate::surface::proof) fn try_float_bound_link(
        &self,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_float_bound_link(
            &self.proof.body,
            source,
            goal,
            source_surface,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_signed_definedness_bounds(
        &self,
        width: crate::kernel::SignedDefinedWidth,
        premises: Vec<SyntaxProposition>,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_signed_definedness_bounds(
            &self.proof.body,
            width,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Expand a mathematical identity inside its owned have body.
    pub(in crate::surface::proof) fn try_integer_algebra(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_integer_algebra(&self.proof.body)?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Emit local word laws in an owned have body.
    pub(in crate::surface::proof) fn try_address_words_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_address_words_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Rewrite selected conditional arms inside an owned have body.
    pub(in crate::surface::proof) fn try_rewrite_conditional_arms_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some((body, _)) = crate::kernel::search::ProofSearch::rewrite_conditional_arms_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Construct a selected scalar interval leaf without normalization.
    pub(in crate::surface::proof) fn try_interval_fact_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_interval_fact_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Carry a selected native endpoint inside an owned have body.
    pub(in crate::surface::proof) fn try_native_integer_bound(
        &self,
        source: &Proposition,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) =
            crate::kernel::search::ProofSearch::try_native_integer_bound(&self.proof.body, source)?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Construct a signed addition or subtraction certificate from the selected bounds.
    pub(in crate::surface::proof) fn try_int32_add_sub_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_int32_add_sub_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Construct the selected countdown bound in its owned have body.
    pub(in crate::surface::proof) fn try_signed_countdown_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_signed_countdown_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Run only the ordinary Integer emitter in a selected have body.
    pub(in crate::surface::proof) fn try_integer_composition_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_integer_composition_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Compose an exact sum's intrinsic bounds inside an owned have body.
    pub(in crate::surface::proof) fn try_intrinsic_sum_bound(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) =
            crate::kernel::search::ProofSearch::try_intrinsic_sum_bound(&self.proof.body)?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Emit the explicit interval-product proof inside a selected have body.
    pub(in crate::surface::proof) fn try_product_bound_using(
        &self,
        premises: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = crate::kernel::search::ProofSearch::try_product_bound_using(
            &self.proof.body,
            premises,
        )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the loop-bundle member planner inside the owned nested body, so a
    /// pivot arm proved under `have` retains the same checked descendant the
    /// bundle root would have retained for it.
    pub(in crate::surface::proof) fn plan_invariant_bundle_closure(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) = self.proof.body.driver().plan_invariant_bundle_closure()? else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Interpret an expanded branch, then retain its direct checked successor.
    pub(in crate::surface::proof) fn apply_expanded_execution_if(
        &self,
        condition: &SyntaxProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
    ) -> Result<ProofScope<'a>, ClickError> {
        let body = self
            .proof
            .body
            .driver()
            .apply_expanded_execution_if(condition, then_steps, else_steps)?;
        self.proof.with_completed_execution_if(body)
    }

    /// Retain proofs of a resource close's body facts inside the scope.
    pub(in crate::surface::proof) fn complete_scope(&self) -> Result<Proof<'a>, ClickError> {
        let scope = self.proof;
        let ProofScopeStructure::Open {
            resource,
            source_index,
            restoration,
        } = scope.structure.as_ref()
        else {
            return scope.clone().join();
        };
        let close = |body: &Proof<'a>| {
            scope.close_open_scope_from(body, resource, *source_index, restoration)
        };
        if scope.body.is_at_function_exit() {
            return close(&scope.body);
        }
        let (closed, tail) =
            scope
                .body
                .driver()
                .close_scope_with_body_fact_proof(resource, restoration, &close)?;
        let Some(tail) = tail else {
            return Ok(closed);
        };
        let mut steps = scope.body.certificate().steps().to_vec();
        steps.extend(tail.steps().iter().cloned());
        Ok(Proof {
            node: ProofNode::step_child(
                &scope.root.node,
                closed.focused_branch_id(),
                Arc::new(ProofStep::Open {
                    resource: resource.clone(),
                    proof: Box::new(ProofCertificate::from_steps(steps)?),
                    deferred_tail: None,
                }),
            ),
            ..closed
        })
    }

    pub(in crate::surface::proof) fn complete_nested_scope(
        &self,
        nested: ProofScope<'a>,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.proof.require_nested_root(&nested)?;
        let closed = nested.driver().complete_scope()?;
        self.proof.join_nested_result(closed)
    }

    /// Applies one checked step inside the nested body. Failed
    /// candidates leave the enclosing scope value unchanged.
    pub(in crate::surface::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<ProofScope<'a>, ClickError> {
        let driver_proof = self.proof;
        let mut next = driver_proof.clone();
        let body = driver_proof
            .body
            .driver()
            .apply_step_with_origin(step, None)?;
        if matches!(
            driver_proof.structure.as_ref(),
            ProofScopeStructure::Open { .. }
        ) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Check a planner's selected step and explicitly close the nested goal.
    pub(in crate::surface::proof) fn apply_step_then_close(
        &self,
        step: ProofStep,
    ) -> Result<ProofScope<'a>, ClickError> {
        let scope = self.apply_step(step)?;
        if scope.is_complete() {
            Ok(scope)
        } else {
            scope.driver().apply_step(ProofStep::Known)
        }
    }

    /// Runs the implicit tail's search inside this scope.
    ///
    /// Each selected statement is checked and retained by
    /// `Proof::try_statement_step`; the search never mutates a second
    /// semantic context or reconstructs steps from its aftermath. A partial
    /// advance is discarded unless the checked descendant reaches function
    /// exit, so unsupported frontiers return a bounded miss to the caller.
    pub(in crate::surface::proof) fn try_execute_to_exit(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let _origin = crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit tail");
        let driver_proof = self.proof;
        let Some((body, added_facts)) =
            crate::kernel::search::ProofSearch::try_execute_to_exit_descendant(
                &(driver_proof.body),
            )?
        else {
            return Ok(None);
        };
        let mut introduced_facts = driver_proof.introduced_facts.clone();
        for fact in added_facts {
            if !introduced_facts.contains(&fact) {
                introduced_facts.push(fact);
            }
        }
        let mut next = driver_proof.clone();
        next.introduced_facts = introduced_facts;
        next.body = body;
        Ok(Some(next))
    }

    /// Runs `step_until` on checked descendants and stops before the
    /// selected source statement.
    pub(in crate::surface::proof) fn try_execute_until(
        &self,
        point: &ExecutionPoint,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some((body, added_facts)) =
            crate::kernel::search::ProofSearch::try_execute_until_descendant(
                &(driver_proof.body),
                point,
            )?
        else {
            return Ok(None);
        };
        let mut introduced_facts = driver_proof.introduced_facts.clone();
        for fact in added_facts {
            if !introduced_facts.contains(&fact) {
                introduced_facts.push(fact);
            }
        }
        let mut next = driver_proof.clone();
        next.introduced_facts = introduced_facts;
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the small shared smart closure search inside the nested proof.
    /// Every accepted candidate still advances through `Proof::apply_step`.
    pub(in crate::surface::proof) fn try_direct_logical_closure(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(&(driver_proof.body))?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Keep the direct structural candidate and its loop-specific universal
    /// closer inside a named leaf of a wide conjunction.
    pub(in crate::surface::proof) fn try_direct_structural_closure_with_quantified(
        &self,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) =
            crate::kernel::search::ProofSearch::try_direct_structural_closure_with_quantified(
                &(driver_proof.body),
                quantified,
            )?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Preserve the selected sources in an owned signed-domain proof.
    pub(in crate::surface::proof) fn try_restricted_signed_definedness_closure(
        &self,
        premises: &[(crate::kernel::Proposition, SyntaxProposition)],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) =
            crate::kernel::search::ProofSearch::try_restricted_signed_definedness_closure(
                &self.proof.body,
                premises,
            )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Closes the body's `int32` or `int64` definedness goal from the
    /// operands' indexed constant bounds.
    pub(in crate::surface::proof) fn try_signed_definedness_closure(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) = crate::kernel::search::ProofSearch::try_signed_definedness_closure(
            &(driver_proof.body),
        )?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_direct_model_equality_rewrite_closure(
        &self,
    ) -> Option<ProofScope<'a>> {
        let driver_proof = self.proof;
        let body = crate::kernel::search::ProofSearch::try_direct_model_equality_rewrite_closure(
            &(driver_proof.body),
        )?;
        let mut next = driver_proof.clone();
        next.body = body;
        Some(next)
    }

    pub(in crate::surface::proof) fn try_solve_closure(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(mut body) =
            crate::kernel::search::ProofSearch::try_solve_closure(&(driver_proof.body))?
        else {
            return Ok(None);
        };
        // An exact indexed premise needs no alternative derivation: its
        // `known` step replays directly. Retain the existing preference for
        // spelled derivations only for broader `known` routes at outcomes
        // and in pure proofs.
        let mid_execution = matches!(
            driver_proof.body.context.as_ref(),
            ProofContext::Execution(_)
        ) && driver_proof.body.focused_outcome_data().is_none();
        if body.node.depth == 1
            && matches!(body.node.step.as_deref(), Some(ProofStep::Known))
            && !mid_execution
            && driver_proof.loop_entry_goal.is_none()
            && !driver_proof
                .body
                .goal()
                .is_some_and(|goal| driver_proof.body.facts().contains(goal))
            && let Some(checkable) =
                crate::kernel::search::ProofSearch::try_solve_closure_after_direct(
                    &(driver_proof.body),
                    true,
                )?
        {
            body = checkable;
        }
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// A stated arithmetic subgoal closed by arithmetic alone
    /// (the body's `try_arithmetic_fact_closure`).
    pub(in crate::surface::proof) fn try_arithmetic_fact_closure(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) =
            crate::kernel::search::ProofSearch::try_arithmetic_fact_closure(&(driver_proof.body))?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Selected-premise arithmetic without operation identities, for the bounds and
    /// goal an identity closure proves inside its own `have`s.
    pub(in crate::surface::proof) fn try_selected_arithmetic_without_identities(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) = crate::kernel::search::ProofSearch::selected_arithmetic(
            &(driver_proof.body),
            false,
            &[],
        )?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// The narrow closure of a store's index disequality: a signed interval
    /// certificate over the indexed bounds of its variables, one side of the
    /// other by selected-premise arithmetic over the connected facts, then
    /// the case split that carries a connected disequality across an
    /// equality (the Integer/word bridge). It runs none of `solve`'s other
    /// strategies, so a miss at each store costs those bounded searches.
    pub(in crate::surface::proof) fn try_index_disequality_closure(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let signed = crate::kernel::search::ProofSearch::try_execution_signed_arithmetic(
            &(driver_proof.body),
        )
        .or_else(|| {
            crate::kernel::search::ProofSearch::try_pure_signed_arithmetic(&(driver_proof.body))
        });
        let selected = match signed {
            Some(body) => Some(body),
            None => crate::kernel::search::ProofSearch::try_disequality_by_selected_refutation(
                &(driver_proof.body),
            )?,
        };
        let body = match selected {
            Some(body) => body,
            None => {
                let Some(body) =
                    crate::kernel::search::ProofSearch::try_disequality_by_refuted_equality(
                        &(driver_proof.body),
                    )?
                else {
                    return Ok(None);
                };
                body
            }
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_selected_arithmetic(
        &self,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) =
            crate::kernel::search::ProofSearch::try_selected_arithmetic(&(driver_proof.body))?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_restricted_solve_closure(
        &self,
        surfaces: &[SyntaxProposition],
    ) -> Option<ProofScope<'a>> {
        let driver_proof = self.proof;
        let body = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
            &(driver_proof.body),
            surfaces,
        )?;
        let mut next = driver_proof.clone();
        next.body = body;
        Some(next)
    }

    pub(in crate::surface::proof) fn try_solve_closure_with_surfaces(
        &self,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) = crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(driver_proof.body),
            introduced_surfaces,
        )?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_indexed_separation_restriction(
        &self,
        goal: &SyntaxProposition,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let Some(body) =
            crate::kernel::search::ProofSearch::try_resource_separation_restriction_closure(
                &self.proof.body,
                goal,
                &[],
                true,
            )?
        else {
            return Ok(None);
        };
        let mut next = self.proof.clone();
        next.body = body;
        Ok(Some(next))
    }
}

impl<'p, 'a> ProofDriver<'p, ProofScope<'a>> {
    /// Checks a source body after its enclosing driver has selected Proof as
    /// the authority for this scope. Explicit failures remain checked errors
    /// through every nested scope and logical arm.
    pub(in crate::surface::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) = driver_proof
            .body
            .driver()
            .try_authoritative_linear_script(tactics)?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// [`Self::try_authoritative_linear_script`] for a body whose driver
    /// knows where each tactic was written: `sites[index]` addresses
    /// `tactics[index]`.
    pub(in crate::surface::proof) fn try_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        implicit_tail: bool,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) = driver_proof.body.driver().try_addressed_linear_script(
            tactics,
            sites,
            &mut None,
            None,
            implicit_tail,
        )?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }

    pub(in crate::surface::proof) fn try_authoritative_linear_script_reporting(
        &self,
        tactics: &[ProofTactic],
        declined: &mut Option<crate::surface::proof::smart_closures::LinearScriptDecline>,
        unfinished: &mut Option<Proof<'a>>,
        implicit_tail: bool,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        let Some(body) = driver_proof
            .body
            .driver()
            .try_authoritative_linear_script_reporting(
                tactics,
                declined,
                Some(unfinished),
                implicit_tail,
            )?
        else {
            return Ok(None);
        };
        let mut next = driver_proof.clone();
        next.body = body;
        Ok(Some(next))
    }
}

impl<'p, 'a> ProofDriver<'p, ProofScope<'a>> {
    /// Checks an explicit theorem application on the scope's current body.
    /// Preserve a missing-premise diagnostic instead of treating the written
    /// application as a search miss. Function-exit applications remain
    /// outcome-local ordered-finalization operations.
    pub(in crate::surface::proof) fn apply_fact_application(
        &self,
        fact: &SyntaxProposition,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        if driver_proof.body.is_at_function_exit() {
            return Ok(None);
        }
        let body = driver_proof.body.driver().apply_fact_application(fact)?;
        let mut next = driver_proof.clone();
        if matches!(
            driver_proof.structure.as_ref(),
            ProofScopeStructure::Open { .. }
        ) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(Some(next))
    }
    pub(in crate::surface::proof) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<ProofScope<'a>>, ClickError> {
        let driver_proof = self.proof;
        if driver_proof.body.is_at_function_exit() {
            return Ok(None);
        }
        let body = driver_proof
            .body
            .driver()
            .apply_theorem_application(application)?;
        let mut next = driver_proof.clone();
        if matches!(
            driver_proof.structure.as_ref(),
            ProofScopeStructure::Open { .. }
        ) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(Some(next))
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Open a generated have, preserving its native arithmetic presentation.
    pub(in crate::surface::proof) fn open_have(
        &self,
        proposition: SyntaxProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.open_have_with_presentation(proposition, true)
    }

    pub(in crate::surface::proof) fn open_source_have(
        &self,
        have: &ProofHave,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.open_have_as_written(have.proposition.clone())
    }

    pub(in crate::surface::proof) fn open_have_as_written(
        &self,
        proposition: SyntaxProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.open_have_with_presentation(proposition, false)
    }

    fn open_have_with_presentation(
        &self,
        proposition: SyntaxProposition,
        observed_spelling: bool,
    ) -> Result<ProofScope<'a>, ClickError> {
        let operation =
            |proof: &Proof<'a>| proof.begin_have(proposition.clone(), observed_spelling);
        if super::execution_statements::implicit_solve_disabled() {
            return operation(self.proof);
        }
        let step = ProofStep::Have {
            proposition: proposition.clone(),
            proof: Box::new(ProofCertificate::from_proof_tactics(&[]).expect("empty certificate")),
        };
        self.with_proved_lowering_requirements(&step, operation)
    }
}

impl<'p, 'a> ProofDriver<'p, ProofScope<'a>> {
    /// Open a nested have at this scope's current body. The resulting scope
    /// must still be incorporated through the existing join_nested operation.
    pub(in crate::surface::proof) fn open_have(
        &self,
        proposition: SyntaxProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.proof.body.driver().open_have(proposition)
    }

    pub(in crate::surface::proof) fn open_source_have(
        &self,
        have: &ProofHave,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.proof.body.driver().open_source_have(have)
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Import the facts introduced by lowering this claim, then open its proof.
    pub(in crate::surface::proof) fn open_contract_claim(
        &self,
        goal: &crate::kernel::ContractClaimGoal,
        surface: &SyntaxProposition,
    ) -> Result<Proof<'a>, ClickError> {
        let root = self
            .proof
            .clone()
            .with_claim_lowering_facts(self.proof, goal.facts())?;
        root.driver()
            .open_contract_claim_without_lowering_facts(goal, surface)
    }

    /// Open a claim using the existing facts, retaining prerequisite proofs
    /// before its own steps without copying the enclosing execution history.
    pub(in crate::surface::proof) fn open_contract_claim_without_lowering_facts(
        &self,
        goal: &crate::kernel::ContractClaimGoal,
        surface: &SyntaxProposition,
    ) -> Result<Proof<'a>, ClickError> {
        let checkpoint = self.proof.checkpoint();
        let operation = |root: &Proof<'a>| {
            let mut opened = root.begin_contract_claim(goal, surface)?;
            for step in root.certificate_since(&checkpoint)?.steps() {
                opened.node =
                    ProofNode::step_child(&opened.node, BranchId::ROOT, Arc::new(step.clone()));
            }
            Ok(opened)
        };
        if super::execution_statements::implicit_solve_disabled() {
            return operation(self.proof);
        }
        let step = ProofStep::Have {
            proposition: surface.clone(),
            proof: Box::new(ProofCertificate::from_proof_tactics(&[]).expect("empty certificate")),
        };
        self.with_proved_lowering_requirements(&step, operation)
    }
}
