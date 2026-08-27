//! Point-goal theorem application, witness/instantiate, rewrite, and
//! transport steps.

use super::*;

impl<'a> Proof<'a> {
    pub(super) fn apply_theorem_using(
        &self,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                self.apply_pure_theorem_using(context, application, surface_premises)
            }
            ProofContext::Point(context) => self.apply_point_theorem_using(
                &PointOperationView::from_point(context),
                application,
                surface_premises,
            ),
            // A focused function-outcome goal applies theorems through the
            // point checker, reading its data from the goal; the effect
            // context is the replay-level set the legacy drain consumed.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view_with_effects(OutcomeEffectContext::Replay)
                    .expect("a focused outcome judgment resolves its point view");
                self.apply_point_theorem_using(&view, application, surface_premises)
            }
            ProofContext::Execution(context) => {
                self.apply_execution_theorem_using(context, application, surface_premises)
            }
        }
    }

    pub(super) fn apply_pure_theorem_using(
        &self,
        context: &PureProofContext<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "`apply using` premise"))
            .collect::<Result<Vec<_>, _>>()?;

        for premise in &explicit_premises {
            if !self.facts().contains(premise) {
                return Err(self.step_error(format!(
                    "`apply using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        // The checker receives exactly the named premises, not the ambient
        // context. Its work is therefore independent of unrelated facts, and
        // it cannot silently search for an omitted theorem requirement.
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let program_point_states = ProgramPointStates::new();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            pre_state: &state,
            post_state: &state,
            result: None,
            program_point_states: &program_point_states,
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let applied = apply_theorem_applications_to_available(
            context.theorem_environment,
            &[(self.node.depth, application.clone())],
            context.claim_label,
            None,
            explicit_premises,
            &application_context,
            context.predicate_environment,
            context.click_function_environment,
            &unfolded_predicates,
        )?;

        let mut facts = self.facts().clone();
        let mut added_facts = Vec::new();
        for fact in applied {
            if !facts.contains(&fact) {
                added_facts.push(fact.clone());
            }
            facts = facts.with_fact(fact);
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, facts),
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
        })
    }

    pub(super) fn apply_point_theorem_using(
        &self,
        view: &PointOperationView<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let checked = check_point_theorem_application_using_facts(
            view.theorem_environment,
            application,
            surface_premises,
            view.claim_label,
            view.tactic_index,
            &self.facts(),
            view.parameters,
            view.arguments,
            view.pre_state,
            view.state,
            view.result,
            view.program_point_states,
            view.surface_propositions,
            &unfolded_predicates,
            view.effect_facts,
            view.predicate_environment,
            view.click_function_environment,
            false,
        )?;
        let complete = self.goal().is_some_and(|goal| checked.facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, checked.facts),
            checked_facts: Arc::new(checked.added_facts.clone()),
            added_facts: Arc::new(checked.added_facts),
        })
    }

    pub(super) fn apply_execution_theorem_using(
        &self,
        context: &ExecutionProofContext<'a>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let pre_state = context
            .old_reference_state(&execution.frontier, &execution.state)
            .clone();
        let retain_function_entry_derivation = execution
            .frontier
            .execution_start_state
            .as_ref()
            .is_none_or(|start| start == &*execution.state);
        let checked = check_point_theorem_application_using_facts(
            context.theorem_environment,
            application,
            surface_premises,
            context.claim_label,
            context.tactic_index,
            &self.facts(),
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            &execution.state,
            None,
            &execution.program_point_states,
            &execution.surface_propositions,
            &execution.unfolded_predicates,
            &execution.effect_facts,
            context.predicate_environment,
            context.click_function_environment,
            retain_function_entry_derivation,
        )?;
        if let Some(prerequisite) = checked.function_entry_prerequisite
            && !execution
                .replay
                .function_entry_execution_prerequisites
                .contains(&prerequisite)
        {
            execution
                .last_step_delta
                .function_entry_prerequisites
                .push(prerequisite.clone());
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(prerequisite);
        }
        if let Some(derivation) = checked.function_entry_derivation
            && !execution
                .replay
                .function_entry_derivations
                .contains(&derivation)
        {
            execution
                .last_step_delta
                .function_entry_derivations
                .push(derivation.clone());
            execution
                .replay
                .function_entry_derivations
                .insert(derivation);
        }
        let complete = self.goal().is_some_and(|goal| checked.facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.discharged_if_or_execution_at(
                self.focused,
                complete,
                checked.facts,
                execution,
            ),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    pub(super) fn apply_point_choose(
        &self,
        choice: &ProofChoice,
    ) -> Result<ProofState, ClickError> {
        let view = match self.context.as_ref() {
            ProofContext::Point(context) => PointOperationView::from_point(context),
            // A choice on a judgment stated at a function outcome selects
            // its requirement source through the outcome view.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => self
                .outcome_point_view()
                .expect("a focused outcome judgment resolves its point view"),
            ProofContext::Execution(_) => self
                .execution_proposition_point_view()
                .ok_or_else(|| self.step_error("`choose` requires a point proposition proof"))?,
            _ => return Err(self.step_error("`choose` requires a point proposition proof")),
        };
        self.proposition_goal("`choose` requires a proposition goal")?;
        if choice.name == "result"
            || view.state.locals().contains_name(&choice.name)
            || self.state.locals.values.contains_key(&choice.name)
        {
            return Err(self.step_error(format!("`{}` is already in scope", choice.name)));
        }

        let source_index = match &choice.source {
            ProofFactSource::Requirement(index) => {
                if *index >= view.original_requirements.len() {
                    return Err(self.step_error(format!(
                        "requirement {index} is out of range; function has {} requirement(s)",
                        view.original_requirements.len()
                    )));
                }
                *index
            }
            ProofFactSource::RequirementLabel(label) => view
                .requirement_label_indices
                .and_then(|indices| indices.get(label))
                .copied()
                .ok_or_else(|| self.step_error(format!("unknown requirement label `{label}`")))?,
        };
        let mut source = view
            .requirement_facts
            .get(source_index)
            .cloned()
            .ok_or_else(|| {
                self.step_error(format!("requirement {source_index} was not available"))
            })?;
        let unfolded_predicates = self.active_unfolded_predicates();
        if !matches!(source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty() {
            source = unfold_predicates_in_proposition(
                view.predicate_environment,
                view.click_function_environment,
                &unfolded_predicates,
                &source,
                self.facts().assumptions(),
            )
            .map_err(|message| self.step_error(message))?;
        }
        let Proposition::Exists {
            var, sort, body, ..
        } = source
        else {
            return Err(self.step_error("`choose` source is not an existential proposition"));
        };
        if sort != Sort::CInt32 {
            return Err(self.step_error("only int32 existential choices are supported"));
        }

        let chosen = Bitvector32Term::Variable(Variable(self.state.locals.next_choice_variable));
        let chosen_fact = substitute_int32_variable_in_proposition(&body, var, chosen.clone());
        let mut locals = self.state.locals.clone();
        locals.values = locals.values.with_inserted(
            choice.name.clone(),
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(chosen))),
        );
        locals.next_choice_variable += 1;
        let added_facts = (!self.facts().contains_top_level(&chosen_fact))
            .then(|| vec![chosen_fact.clone()])
            .unwrap_or_default();
        let facts = self.facts().with_fact(chosen_fact.clone());
        Ok(ProofState {
            locals,

            goals: self.state.goals.with_facts_at(self.focused, facts),
            added_facts: Arc::new(added_facts),
            checked_facts: Arc::new(vec![chosen_fact]),
        })
    }

    pub(super) fn apply_point_witness(
        &self,
        witness: &ProofWitness,
    ) -> Result<ProofState, ClickError> {
        let view = match self.context.as_ref() {
            ProofContext::Point(context) => PointOperationView::from_point(context),
            // A witness refinement on a judgment stated at a function
            // outcome reads the outcome's result-aware data.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => self
                .outcome_point_view()
                .expect("a focused outcome judgment resolves its point view"),
            ProofContext::Execution(_) => self
                .execution_proposition_point_view()
                .ok_or_else(|| self.step_error("`witness` requires a point proposition proof"))?,
            _ => return Err(self.step_error("`witness` requires a point proposition proof")),
        };
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = unfold_predicates_in_proposition(
            view.predicate_environment,
            view.click_function_environment,
            &unfolded_predicates,
            &goal,
            self.facts().assumptions(),
        )
        .map_err(|message| self.step_error(format!("could not unfold witness goal: {message}")))?;
        let values = parameter_values(view.parameters, view.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(view.parameters, &values, view.state.memory());
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, view.state);
        let checked_witness = ProofWitness {
            name: witness.name.clone(),
            value: self.substitute_point_locals_in_expression(&witness.value)?,
        };
        let value = evaluate_witness_tactic_value(
            &checked_witness,
            view.claim_label,
            0,
            view.tactic_index,
            &values,
            &array_refs,
            view.pre_state,
            view.state,
            view.result,
            self.facts().assumptions(),
            view.predicate_environment,
            view.click_function_environment,
            view.program_point_states,
        )?;
        let goal = apply_witness_tactic(
            &checked_witness,
            value,
            goal,
            view.claim_label,
            0,
            view.tactic_index,
        )?;
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Exists { name, body, .. }) if name == &witness.name => {
                let substitutions = BTreeMap::from([(name.clone(), witness.value.clone())]);
                Some(
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface witness goal: {message}"
                        ))
                    })?,
                )
            }
            Some(ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            }) if item == &witness.name => {
                let substitutions = BTreeMap::from([(item.clone(), witness.value.clone())]);
                let start =
                    substitute_contract_expression(start, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range start: {message}"
                        ))
                    })?;
                let end =
                    substitute_contract_expression(end, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range end: {message}"
                        ))
                    })?;
                let value = substitute_contract_expression(&witness.value, &substitutions)
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range witness: {message}"
                        ))
                    })?;
                let body =
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range witness goal: {message}"
                        ))
                    })?;
                Some(ClickProposition::And(
                    Box::new(ClickProposition::And(
                        Box::new(ClickProposition::Comparison {
                            left: start,
                            operator: ComparisonOperator::LessEqual,
                            right: value.clone(),
                        }),
                        Box::new(ClickProposition::Comparison {
                            left: value,
                            operator: ComparisonOperator::LessThan,
                            right: end,
                        }),
                    )),
                    Box::new(body),
                ))
            }
            _ => None,
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(self.focused, {
                let context = self.refined_context(self.facts().clone());
                self.refined_proposition(context, goal, surface_goal)
            }),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    pub(super) fn apply_point_instantiate_using(
        &self,
        surface_quantified: &ClickProposition,
        argument: &ContractExpression,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let view = match self.context.as_ref() {
            ProofContext::Point(context) => PointOperationView::from_point(context),
            // An instantiation on a judgment stated at a function outcome
            // evaluates its argument and quantified fact in that outcome's
            // result-aware point environment.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => self
                .outcome_point_view()
                .expect("a focused outcome judgment resolves its point view"),
            // A leading nested `have` is a proposition proof at the
            // execution frontier. It evaluates the quantified fact and
            // argument in that frontier's point environment without
            // exporting or replaying execution state.
            ProofContext::Execution(_) => {
                self.execution_proposition_point_view().ok_or_else(|| {
                    self.step_error("`instantiate` requires a point proposition proof")
                })?
            }
            _ => {
                return Err(self.step_error("`instantiate` requires a point proposition proof"));
            }
        };
        self.proposition_goal("`instantiate` requires a proposition goal")?;

        let explicit_premises = surface_premises
            .iter()
            .map(|surface| self.lower_surface_proposition(surface, "`instantiate using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        for premise in &explicit_premises {
            if !self.facts().replay_available_across_effects(premise, &[]) {
                return Err(self.step_error(format!(
                    "`instantiate using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        let lowered_quantified =
            self.lower_surface_proposition(surface_quantified, "`instantiate` quantified fact")?;
        let quantified = if self.facts().contains(&lowered_quantified) {
            lowered_quantified
        } else if let Some(available) = self
            .facts()
            .matching_quantified_replay_fact(&lowered_quantified)
        {
            available
        } else {
            return Err(self.step_error(format!(
                "`instantiate` quantified fact is not exactly available: {}",
                describe_click_proposition(surface_quantified)
            )));
        };

        let parameter_values = parameter_values(view.parameters, view.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs =
            array_refs_for_parameters(view.parameters, &parameter_values, view.state.memory());
        let (values, array_refs) =
            contract_environment_at_state(&parameter_values, &array_refs, view.state);
        let mut active_functions = BTreeSet::new();
        let argument = self.substitute_point_locals_in_expression(argument)?;
        let value = evaluate_contract_expression_with_environment(
            &values,
            &array_refs,
            view.pre_state,
            view.state,
            view.result,
            self.facts().assumptions(),
            &argument,
            view.predicate_environment,
            view.click_function_environment,
            view.program_point_states,
            &mut active_functions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not evaluate `instantiate` argument: {message}"
            ))
        })?;
        let CValue::Int32(argument) = value else {
            return Err(self.step_error("`instantiate` argument did not evaluate to int32"));
        };

        let conclusion =
            check_forall_int32_instantiation(&quantified, argument, &explicit_premises)
                .map_err(|message| self.step_error(format!("`instantiate` failed: {message}")))?;
        let added = !self.facts().contains_top_level(&conclusion);
        let facts = self.facts().with_fact(conclusion.clone());
        let added_facts = added.then_some(conclusion).into_iter().collect::<Vec<_>>();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.with_facts_at(self.focused, facts),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    pub(super) fn apply_rewrite(
        &self,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.apply_pure_rewrite(surface_equality),
            ProofContext::Point(context) => {
                self.apply_point_rewrite(&PointOperationView::from_point(context), surface_equality)
            }
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view()
                    .expect("a focused outcome judgment resolves its point view");
                self.apply_point_rewrite(&view, surface_equality)
            }
            // A nested execution `have` is still a proposition proof. It
            // borrows the execution context only for lowering; its scope join
            // restores the exact outer frontier after this checked rewrite.
            ProofContext::Execution(_) if self.goal().is_some() => {
                self.apply_pure_rewrite(surface_equality)
            }
            ProofContext::Execution(_) => {
                Err(self.step_error("`rewrite` requires a proposition proof"))
            }
        }
    }

    // Keep lowering's large proposition temporaries out of the common rewrite
    // dispatcher frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    pub(super) fn apply_pure_rewrite(
        &self,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let goal = Box::new(
            self.proposition_goal("`rewrite` requires a proposition goal")?
                .clone(),
        );
        let equality =
            Box::new(self.lower_surface_proposition(surface_equality, "`rewrite` equality")?);
        self.finish_rewrite(goal, equality, surface_equality)
    }

    // Keep point-lowering and unfold temporaries out of the common rewrite
    // dispatcher frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    pub(super) fn apply_point_rewrite(
        &self,
        view: &PointOperationView<'_>,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = Box::new(
            unfold_predicates_in_proposition(
                view.predicate_environment,
                view.click_function_environment,
                &unfolded_predicates,
                self.proposition_goal("`rewrite` requires a proposition goal")?,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` goal: {message}"))
            })?,
        );
        let recorded = view
            .surface_propositions
            .available_kernel_matching(surface_equality, |kernel| {
                self.facts().materialization_available(kernel)
            })
            .map(|kernel| Box::new(kernel.clone()))
            .or_else(|| {
                let reverse = reverse_surface_equality(surface_equality)?;
                let kernel = view
                    .surface_propositions
                    .available_kernel_matching(&reverse, |kernel| {
                        self.facts().materialization_available(kernel)
                    })?
                    .clone();
                reverse_kernel_equality(kernel).map(Box::new)
            });
        let equality = match recorded {
            Some(equality) => equality,
            None => Box::new(
                lower_point_proposition_with_assumptions(
                    surface_equality,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.program_point_states,
                    view.predicate_environment,
                    view.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower `rewrite` equality: {message}"))
                })?,
            ),
        };
        let equality = Box::new(
            unfold_predicates_in_proposition(
                view.predicate_environment,
                view.click_function_environment,
                &unfolded_predicates,
                &equality,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` equality: {message}"))
            })?,
        );
        self.finish_rewrite(goal, equality, surface_equality)
    }

    // Keep the by-value goal/equality pair in the rewrite worker rather than
    // every caller's frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    pub(super) fn finish_rewrite(
        &self,
        goal: Box<Proposition>,
        equality: Box<Proposition>,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let admitted = self.facts().materialization_available(&equality)
            || reverse_kernel_equality(equality.as_ref().clone())
                .as_ref()
                .is_some_and(|reverse| self.facts().materialization_available(reverse));
        let available = if admitted {
            std::slice::from_ref(equality.as_ref())
        } else {
            &[]
        };
        let rewritten = rewrite_proposition_by_exact_equality(&goal, &equality, available)
            .map_err(|message| self.step_error(message))?;
        let surface_goal = self.surface_goal().and_then(|surface_goal| {
            let candidate =
                rewrite_click_proposition_by_surface_equality(surface_goal, surface_equality)?;
            self.lower_surface_proposition_direct(&candidate, "rewritten Surface goal")
                .ok()
                .filter(|lowered| lowered == &rewritten)
                .map(|_| candidate)
        });
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(self.focused, {
                let context = self.refined_context(self.facts().clone());
                self.refined_proposition(context, rewritten, surface_goal)
            }),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    pub(super) fn apply_extract(
        &self,
        surface: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let proposition = self.lower_surface_proposition(surface, "`extract` proposition")?;
        if !self.facts().contains_proper_conjunct(&proposition)
            && !self
                .facts()
                .contains_discharged_implication_consequent(&proposition)
        {
            return Err(self.step_error(format!(
                "`extract` proposition is not a proper conjunct of an exact available fact or a discharged implication consequent: {}",
                describe_pure_fact(&proposition, &[], &[])
            )));
        }
        let added_facts = (!self.facts().contains_top_level(&proposition))
            .then(|| proposition.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = self.facts().with_fact(proposition);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, facts),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    /// The point-operation data a result-aware checker consumes, resolved
    /// either from a point proof's borrowed context or from a focused
    /// function-outcome goal on an execution proof. This is the goal-aware
    /// point view: outcome goals own their result, post-state, surface
    /// lowerings, and effect facts, and borrow the frontier snapshot for the
    /// remaining program-point data.
    pub(super) fn outcome_point_view(&self) -> Option<PointOperationView<'_>> {
        self.outcome_point_view_with_effects(OutcomeEffectContext::Path)
    }

    /// Point-operation data for a proposition scope opened on an execution
    /// frontier before a function outcome exists. The nested goal borrows the
    /// frontier snapshot solely for lowering and requirement selection;
    /// checked point steps can refine only that proposition and proof-local
    /// bindings.
    pub(super) fn execution_proposition_point_view(&self) -> Option<PointOperationView<'_>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let Goal::Proposition(goal) = self.focused_goal()? else {
            return None;
        };
        if goal.outcome.is_some() {
            return None;
        }
        let execution = goal.context.execution.as_deref()?;
        Some(PointOperationView {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: &execution.effect_facts,
            parameters: context.parsed_function.parameters(),
            arguments: context.arguments,
            pre_state: execution.frontier.execution_start_state(&execution.state),
            state: &execution.state,
            result: None,
            program_point_states: &execution.program_point_states,
            surface_propositions: &execution.surface_propositions,
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
            theorem_environment: context.theorem_environment,
            original_requirements: context.function_block.requires(),
            requirement_label_indices: Some(context.function_block.requirement_label_indices()),
            requirement_facts: &context.constants.execution_start_facts,
        })
    }

    /// The focused judgment's result-aware point data: a function-outcome
    /// goal owns its data, and a proposition judgment stated at an outcome
    /// borrows that outcome's data by identity.
    pub(super) fn focused_outcome_point(&self) -> Option<&Arc<OutcomePointData>> {
        match self.focused_goal()? {
            Goal::FunctionOutcome(goal) => Some(&goal.point),
            Goal::Proposition(goal) => goal.outcome.as_ref(),
            Goal::Frontier(_) => None,
        }
    }

    /// Decides one explicit post-execution `if` from the focused outcome's
    /// exact fact context. The syntax driver may use the returned polarity to
    /// choose which source arm to visit, but it cannot manufacture a fact or
    /// successor: both alternatives are lowered and the kernel assumptions
    /// must establish exactly one of them on this `Proof` path.
    pub(in crate::lang::click::proof) fn checked_outcome_if_value(
        &self,
        condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        if !matches!(self.focused_goal(), Some(Goal::FunctionOutcome(_))) {
            return Err(self.step_error("post-execution `if` requires a focused outcome goal"));
        }
        let point = self
            .focused_outcome_point()
            .expect("a focused outcome judgment resolves its point data");
        let mut recorded_value = None;
        for decision in point.branch_decisions.iter() {
            if &decision.condition != condition {
                continue;
            }
            if recorded_value.is_some_and(|value| value != decision.value) {
                return Err(self.step_error(
                    "focused outcome records both sides of the post-execution `if` condition",
                ));
            }
            recorded_value = Some(decision.value);
        }
        if let Some(value) = recorded_value {
            return Ok(value);
        }
        let negative_surface = ClickProposition::Not(Box::new(condition.clone()));
        let positive =
            self.lower_surface_proposition(condition, "post-execution `if` condition")?;
        let negative =
            self.lower_surface_proposition(&negative_surface, "post-execution `if` negation")?;
        let assumptions = self.facts().assumptions();
        let positive_holds = self.facts().contains(&positive) || assumptions.proves(&positive);
        let negative_holds = self.facts().contains(&negative)
            || assumptions.proves(&negative)
            || fact_conflicts_with_assumptions(&positive, assumptions);
        match (positive_holds, negative_holds) {
            (true, false) => Ok(true),
            (false, true) => Ok(false),
            (false, false) => Err(self
                .step_error("focused outcome does not decide the post-execution `if` condition")),
            (true, true) => Err(self.step_error(
                "focused outcome proves both sides of the post-execution `if` condition",
            )),
        }
    }

    /// Reports whether every checked execution path already decides a
    /// post-execution condition. Such an `if` is a cursor over an existing
    /// path partition and may be deferred until each outcome Proof is
    /// focused. An undecided logical case split must stay with the general
    /// proof driver, which introduces the two assumptions explicitly.
    /// Forks every outcome path on which `condition` is undecided into two
    /// paths, one per polarity, each carrying the case fact and a recorded
    /// proof-case decision; a path whose facts already decide the condition
    /// only records the decision. Afterwards a deferred post-execution `if`
    /// on `condition` is decided on every path, and certification runs once
    /// per recorded case.
    pub(in crate::lang::click::proof) fn split_outcome_paths_by_case(
        &self,
        condition: &ClickProposition,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("post-execution case split")?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("post-execution case split requires an execution proof"));
        };
        let mut execution = self.execution().cloned().ok_or_else(|| {
            self.step_error("post-execution case split lost its execution frontier")
        })?;
        if !execution.frontier.is_at_function_exit() {
            return Err(self.step_error("post-execution case split requires function exit"));
        }
        let checked = execution.frontier.execution().cloned().ok_or_else(|| {
            self.step_error("post-execution case split has no checked execution paths")
        })?;
        let pre_state = execution
            .frontier
            .execution_start_state(&execution.state)
            .clone();
        let mut paths = Vec::with_capacity(checked.paths().len() * 2);
        let mut decisions_by_path = Vec::with_capacity(checked.paths().len() * 2);
        for (path_index, path) in checked.paths().iter().enumerate() {
            check_verification_deadline()?;
            let decisions = execution
                .outcome_branch_decisions
                .get(path_index)
                .cloned()
                .unwrap_or_else(|| execution.branch_decisions.clone());
            let keep = |paths: &mut Vec<_>, decisions_by_path: &mut Vec<_>| {
                paths.push((
                    path.outcome().clone(),
                    path.execution_facts(),
                    path.obligations().to_vec(),
                ));
                decisions_by_path.push(decisions.clone());
            };
            if decisions
                .iter()
                .any(|decision| &decision.condition == condition)
            {
                keep(&mut paths, &mut decisions_by_path);
                continue;
            }
            let CFunctionOutcome::Return { value, state } = path.outcome() else {
                keep(&mut paths, &mut decisions_by_path);
                continue;
            };
            let path_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let lowered = lower_outcome_proposition_with_program_points(
                context.parsed_function.parameters(),
                context.arguments,
                &pre_state,
                state,
                value,
                &path_facts,
                condition,
                context.predicate_environment,
                context.click_function_environment,
                &execution.program_point_states,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "post-execution case split could not lower its condition: {message}"
                ))
            })?;
            let positive = crate::kernel::canonical_condition_fact(&lowered);
            let negative =
                crate::kernel::canonical_condition_fact(&Proposition::Not(Box::new(lowered)));
            let assumptions = path_facts
                .iter()
                .fold(self.facts().assumptions().clone(), |assumptions, fact| {
                    assumptions.assume_proposition(fact.clone())
                });
            let cases: Vec<(bool, Option<Proposition>)> = if assumptions.proves(&positive) {
                vec![(true, None)]
            } else if assumptions.proves(&negative) {
                vec![(false, None)]
            } else {
                vec![(true, Some(positive)), (false, Some(negative))]
            };
            for (value, case_fact) in cases {
                let mut facts = path.execution_facts();
                if let Some(case_fact) = case_fact {
                    facts.push(ExecutionPureFact::new(case_fact));
                }
                paths.push((path.outcome().clone(), facts, path.obligations().to_vec()));
                let mut decisions = decisions.clone();
                decisions.push(ExecutionBranchDecision {
                    condition: condition.clone(),
                    value,
                    proof_case: true,
                });
                decisions_by_path.push(decisions);
            }
        }
        let candidates = crate::kernel::c_function_execution_candidates_from_outcomes(
            checked.state().clone(),
            checked.function().clone(),
            checked.arguments().to_vec(),
            paths,
        );
        execution.frontier.point = ProofExecutionPoint::FunctionExit {
            execution: candidates,
        };
        execution.outcome_branch_decisions = Arc::new(decisions_by_path);
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

    pub(in crate::lang::click::proof) fn post_execution_if_is_path_decided(
        &self,
        condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        self.require_execution_frontier("post-execution `if`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("post-execution `if` lost its execution frontier"))?;
        if !execution.frontier.is_at_function_exit() {
            return Err(self.step_error("post-execution `if` requires function exit"));
        }
        let checked = execution
            .frontier
            .execution()
            .ok_or_else(|| self.step_error("post-execution `if` has no checked execution paths"))?;
        for path_index in 0..checked.paths().len() {
            check_verification_deadline()?;
            let decisions = execution
                .outcome_branch_decisions
                .get(path_index)
                .unwrap_or(&execution.branch_decisions);
            let mut recorded = None;
            for decision in decisions.iter() {
                if &decision.condition != condition {
                    continue;
                }
                if recorded.is_some_and(|value| value != decision.value) {
                    return Err(self.step_error(
                        "checked execution path records both sides of the post-execution `if` condition",
                    ));
                }
                recorded = Some(decision.value);
            }
            if recorded.is_none() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Resolves the view with the caller's effect-availability context: the
    /// transport checker consumes the path's own execution facts, while the
    /// theorem checker consumes the replay-level effect set, matching the
    /// legacy drain inputs exactly.
    pub(super) fn outcome_point_view_with_effects(
        &self,
        effects: OutcomeEffectContext,
    ) -> Option<PointOperationView<'_>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let point = self.focused_outcome_point()?;
        let goal = self.focused_goal()?;
        let execution = goal.context().execution.as_deref()?;
        Some(PointOperationView {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: match effects {
                OutcomeEffectContext::Path => point.effect_facts.as_ref(),
                OutcomeEffectContext::Replay => &execution.effect_facts,
            },
            parameters: context.parsed_function.parameters(),
            arguments: context.arguments,
            pre_state: execution.frontier.execution_start_state(&execution.state),
            state: &point.state,
            result: Some(point.result.as_ref()),
            program_point_states: &execution.program_point_states,
            surface_propositions: &point.surface_propositions,
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
            theorem_environment: context.theorem_environment,
            original_requirements: context.function_block.requires(),
            requirement_label_indices: Some(context.function_block.requirement_label_indices()),
            requirement_facts: point.requirement_facts.as_ref(),
        })
    }

    pub(super) fn apply_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Point(context) => self.apply_point_transport_using(
                source,
                target,
                premises,
                &PointOperationView::from_point(context),
            ),
            // A focused function-outcome goal transports result-aware facts
            // through the same point checker, reading its data from the goal.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view()
                    .expect("a focused outcome judgment resolves its point view");
                self.apply_point_transport_using(source, target, premises, &view)
            }
            ProofContext::Execution(context) => {
                self.apply_execution_transport_using(source, target, premises, context)
            }
            ProofContext::Pure(_) => {
                Err(self.step_error("`transport using` requires a point or execution proof"))
            }
        }
    }

    pub(super) fn apply_point_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        view: &PointOperationView<'_>,
    ) -> Result<ProofState, ClickError> {
        let (source, target, premises) = if premises.is_empty() {
            (source.clone(), target.clone(), premises.to_vec())
        } else {
            (
                self.substitute_goal_surface_bindings_in_proposition(source)?,
                self.substitute_goal_surface_bindings_in_proposition(target)?,
                premises
                    .iter()
                    .map(|premise| self.substitute_goal_surface_bindings_in_proposition(premise))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        };
        let checked = check_point_fact_transport_using_facts(
            &source,
            &target,
            &premises,
            view.claim_label,
            view.tactic_index,
            &self.facts(),
            view.effect_facts,
            view.parameters,
            view.arguments,
            view.pre_state,
            view.state,
            view.result,
            view.program_point_states,
            view.surface_propositions,
            view.predicate_environment,
            view.click_function_environment,
        )?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        let checked_facts = vec![checked.source, checked.target.clone()];
        facts = facts.with_fact(checked.target);
        // A focused outcome goal records the checker-owned source and target
        // lowerings atomically with its fact successor; the drain no longer
        // has to re-record them into a caller-owned map for this path.
        if let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() {
            let mut updated = goal.clone();
            let mut point = (*updated.point).clone();
            point
                .surface_propositions
                .record_lowering(&source, &checked_facts[0])?;
            point
                .surface_propositions
                .record_lowering(&target, &checked_facts[1])?;
            updated.point = Arc::new(point);
            updated.context = GoalContext {
                facts,
                unfolded_predicates: goal.context.unfolded_predicates.clone(),
                execution: goal.context.execution.clone(),
            };
            return Ok(ProofState {
                locals: self.state.locals.clone(),
                goals: self
                    .state
                    .goals
                    .replace_at(self.focused, Goal::FunctionOutcome(updated)),
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            });
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, facts),
            added_facts: Arc::new(added_facts),
            checked_facts: Arc::new(checked_facts),
        })
    }

    pub(super) fn apply_execution_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        context: &ExecutionProofContext<'a>,
    ) -> Result<ProofState, ClickError> {
        // A nested proposition proof stated at this frontier may transport
        // facts as well; the successor below preserves the goal's kind.
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let pre_state = context
            .old_reference_state(&execution.frontier, &execution.state)
            .clone();
        let checked = check_point_fact_transport_using_facts(
            source,
            target,
            premises,
            context.claim_label,
            context.tactic_index,
            &self.facts(),
            &execution.effect_facts,
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            &execution.state,
            None,
            &execution.program_point_states,
            &execution.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
        )?;
        execution
            .surface_propositions
            .record_lowering(source, &checked.source)?;
        execution
            .surface_propositions
            .record_lowering(target, &checked.target)?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        facts = facts.with_fact(checked.target);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.discharged_if_or_execution_at(
                self.focused,
                complete,
                facts,
                execution,
            ),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }
}
