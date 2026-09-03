//! Predicate and resource unfold/fold/observation steps.

use super::*;

impl<'a> Proof<'a> {
    pub(super) fn apply_function_unfold(
        &self,
        application: &ClickFunctionApplication,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                let state = CState::new().with_memory(context.theorem_context.memory.clone());
                self.apply_function_unfold_in_state(
                    application,
                    context.theorem_context.values.clone(),
                    context.theorem_context.array_refs.clone(),
                    &state,
                    &state,
                    None,
                    &RecordedSnapshots::new(),
                    context.predicate_environment,
                    context.click_function_environment,
                )
            }
            ProofContext::FixedState(context) => {
                let values = parameter_values(context.parameters, context.arguments)?;
                let array_refs =
                    array_refs_for_parameters(context.parameters, &values, context.state.memory());
                let (values, array_refs) =
                    contract_environment_at_state(&values, &array_refs, context.state);
                self.apply_function_unfold_in_state(
                    application,
                    values,
                    array_refs,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
            }
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                let values = parameter_values(view.parameters, view.arguments)?;
                let array_refs =
                    array_refs_for_parameters(view.parameters, &values, view.state.memory());
                let (values, array_refs) =
                    contract_environment_at_state(&values, &array_refs, view.state);
                self.apply_function_unfold_in_state(
                    application,
                    values,
                    array_refs,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.recorded_snapshots,
                    view.predicate_environment,
                    view.click_function_environment,
                )
            }
            ProofContext::Execution(context) => {
                let execution = self.execution().ok_or_else(|| {
                    self.step_error("function `unfold` lost its semantic execution state")
                })?;
                let values =
                    parameter_values(context.parsed_function.parameters(), context.arguments)?;
                let array_refs = array_refs_for_parameters(
                    context.parsed_function.parameters(),
                    &values,
                    execution.core.state.memory(),
                );
                let (values, array_refs) =
                    contract_environment_at_state(&values, &array_refs, &execution.core.state);
                let pre_state =
                    context.old_reference_state(&execution.core.frontier, &execution.core.state);
                self.apply_function_unfold_in_state(
                    application,
                    values,
                    array_refs,
                    pre_state,
                    &execution.core.state,
                    None,
                    &execution.presentation.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_function_unfold_in_state(
        &self,
        application: &ClickFunctionApplication,
        values: BTreeMap<String, CValue>,
        array_refs: ClickArrayRefs,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
        recorded_snapshots: &RecordedSnapshots,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let definition = click_function_environment
            .get(&application.name)
            .ok_or_else(|| {
                self.step_error(format!(
                    "unknown pure function `{}` in `unfold`",
                    application.name
                ))
            })?;
        if definition.return_type() != C0Type::Int32 {
            return Err(self.step_error(format!(
                "pure function `unfold` currently requires an int32 result; `{}` returns {}",
                definition.name(),
                describe_c0_type(definition.return_type())
            )));
        }
        if application.arguments.len() != definition.parameters().len() {
            return Err(self.step_error(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                application.arguments.len()
            )));
        }

        let substitutions = definition
            .parameters()
            .iter()
            .zip(&application.arguments)
            .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let surface_body = substitute_contract_expression(definition.body(), &substitutions)
            .map_err(|message| {
                self.step_error(format!(
                    "could not instantiate function `{}` for `unfold`: {message}",
                    application.name
                ))
            })?;

        let mut argument_active_functions = BTreeSet::new();
        for argument in &application.arguments {
            collect_click_function_calls(argument, &mut argument_active_functions);
        }
        let argument_values = application
            .arguments
            .iter()
            .map(|argument| {
                evaluate_contract_expression_with_environment(
                    &values,
                    &array_refs,
                    pre_state,
                    state,
                    result,
                    self.facts().assumptions(),
                    argument,
                    predicate_environment,
                    click_function_environment,
                    recorded_snapshots,
                    &mut argument_active_functions,
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|message| {
                self.step_error(format!(
                    "could not lower function `unfold` arguments: {message}"
                ))
            })?;
        let arguments = argument_values
            .into_iter()
            .map(|value| match value {
                CValue::Int32(value) => Ok(value),
                other => Err(self.step_error(format!(
                    "pure function `unfold` currently requires int32 arguments, got {other:?}"
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut unfolding_active_functions = BTreeSet::new();
        collect_click_function_calls(&surface_body, &mut unfolding_active_functions);
        let unfolded = evaluate_contract_expression_with_environment(
            &values,
            &array_refs,
            pre_state,
            state,
            result,
            self.facts().assumptions(),
            &surface_body,
            predicate_environment,
            click_function_environment,
            recorded_snapshots,
            &mut unfolding_active_functions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not unfold function `{}`: {message}",
                application.name
            ))
        })?;
        let equality = comparison_proposition(
            CValue::Int32(Bitvector32Term::PureFunctionApplication {
                name: application.name.clone(),
                arguments,
            }),
            ComparisonOperator::Equal,
            unfolded,
        )
        .map_err(|error| self.step_error(error.message))?;

        let mut facts = self.facts().clone();
        let added_facts = (!facts.contains_top_level(&equality))
            .then(|| equality.clone())
            .into_iter()
            .collect::<Vec<_>>();
        facts = facts.with_kernel_checked_fact(equality.clone());

        let branch = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => {
                let original_surface = goal.surface.as_deref().cloned();
                let surface_application = ContractExpression::Call {
                    name: application.name.clone(),
                    arguments: application.arguments.clone(),
                };
                let surface_equality = ClickProposition::Comparison {
                    left: surface_application,
                    operator: ComparisonOperator::Equal,
                    right: surface_body,
                };
                let surface = original_surface.as_ref().and_then(|surface| {
                    rewrite_click_proposition_by_surface_equality(surface, &surface_equality)
                });
                let kernel = if let Some(surface) = &surface {
                    let mut opaque_calls = BTreeSet::new();
                    crate::surface::validation::collect_click_function_calls_in_proposition(
                        surface,
                        &mut opaque_calls,
                    );
                    lower_fixed_state_proposition_through_kernel_with_opaque_calls(
                        surface,
                        facts.assumptions(),
                        &values,
                        &array_refs,
                        pre_state,
                        state,
                        result,
                        recorded_snapshots,
                        predicate_environment,
                        click_function_environment,
                        &opaque_calls,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not refresh the goal after function `unfold`: {message}"
                        ))
                    })?
                } else {
                    goal.kernel().clone()
                };
                let complete = facts.contains(&kernel);
                (!complete).then(|| {
                    self.refined_proposition(
                        self.refined_branch_state(facts.clone()),
                        kernel,
                        surface.or(original_surface),
                    )
                })
            }
            Some(Obligation::Frontier(_) | Obligation::FunctionOutcome(_)) => Some(
                self.focused_branch()
                    .expect("function unfold requires an open branch")
                    .with_state(self.refined_branch_state(facts.clone())),
            ),
            None => return Err(self.step_error("function `unfold` requires an open goal")),
        };

        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch,
            added_facts: added_facts.clone(),
            checked_facts: added_facts,
        })
    }

    pub(super) fn apply_predicate_unfold(
        &self,
        name: &String,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => self.apply_proposition_predicate_unfold(
                name,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                self.node.depth,
            ),
            ProofContext::FixedState(context) => self.apply_proposition_predicate_unfold(
                name,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                context.tactic_index,
            ),
            // A function-outcome goal unfolds its own path-local facts and
            // delta only: the borrowed execution snapshot is shared by every
            // sibling outcome and must not absorb one path's unfolding.
            ProofContext::Execution(context) if self.focused_outcome_data().is_some() => self
                .apply_proposition_predicate_unfold(
                    name,
                    context.predicate_environment,
                    context.click_function_environment,
                    context.claim_label,
                    context.tactic_index,
                ),
            ProofContext::Execution(_) => self.apply_execution_unfold(name),
        }
    }

    pub(super) fn apply_proposition_predicate_unfold(
        &self,
        name: &String,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        claim_label: &str,
        tactic_index: usize,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let checked = check_unfold_predicate_in_facts(
            &self.facts(),
            name,
            predicate_environment,
            click_function_environment,
            claim_label,
            tactic_index,
        )?;
        let goal = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => {
                let surface = match &goal.surface {
                    Some(surface) => Some(
                        unfold_structural_invariant_proposition(
                            predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))?,
                    ),
                    None => None,
                };
                // Fixed-state and outcome certificates check `unfold` from its
                // retained surface form.  Re-lower that unfolded body
                // against the checked successor facts as part of this same
                // audited step, so resource counts and current memory loads
                // resolve exactly as they do during independent verification.
                // Unfolding only the already-lowered kernel predicate leaves
                // those expressions stranded in the older lowering context.
                let kernel = match (&surface, self.context.as_ref()) {
                    (Some(surface), ProofContext::FixedState(context)) => {
                        let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                        lower_fixed_state_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            context.parameters,
                            context.arguments,
                            context.pre_state,
                            context.state,
                            context.result,
                            context.recorded_snapshots,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .map_err(|message| self.step_error(message))?
                    }
                    (Some(surface), ProofContext::Execution(_))
                        if self.focused_outcome_data().is_some() =>
                    {
                        let view = self
                            .outcome_fixed_state_view()
                            .expect("a focused outcome judgment resolves its fixed-state view");
                        let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                        lower_fixed_state_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            view.parameters,
                            view.arguments,
                            view.pre_state,
                            view.state,
                            view.result,
                            view.recorded_snapshots,
                            view.predicate_environment,
                            view.click_function_environment,
                        )
                        .map_err(|message| self.step_error(message))?
                    }
                    _ => unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        std::slice::from_ref(name),
                        goal.kernel(),
                        checked.facts.assumptions(),
                    )
                    .map_err(|message| self.step_error(message))?,
                };
                self.refined_proposition(
                    self.refined_branch_state(checked.facts.clone()),
                    kernel,
                    surface,
                )
            }
            Some(Obligation::Frontier(_) | Obligation::FunctionOutcome(_)) => {
                let branch = self.focused_branch().expect("focused branch exists");
                let mut unfolded = branch.state.unfolded_predicates.clone();
                unfolded.insert(name.clone());
                branch.with_state(BranchState {
                    facts: checked.facts.clone(),
                    unfolded_predicates: unfolded,
                    execution: branch.state.execution.clone(),
                })
            }
            None => return Err(self.step_error("`unfold` requires an open goal")),
        };
        let goal = {
            let mut unfolded = goal.state.unfolded_predicates.clone();
            unfolded.insert(name.clone());
            goal.with_state(BranchState {
                facts: goal.state.facts.clone(),
                unfolded_predicates: unfolded,
                execution: goal.state.execution.clone(),
            })
        };
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(goal),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    pub(super) fn apply_execution_unfold(
        &self,
        name: &String,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`unfold` requires an execution-frontier proof"));
        };
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let checked = check_unfold_predicate_facts(&mut execution, context, &self.facts(), name)?;
        let mut unfolded_predicates = self.focused_branch_unfolds().clone();
        for name in &checked.added_unfolded_predicates {
            unfolded_predicates.insert(name.clone());
        }
        let refined_goal = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => {
                let surface = goal
                    .surface
                    .as_deref()
                    .map(|surface| {
                        unfold_structural_invariant_proposition(
                            context.predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))
                    })
                    .transpose()?;
                let kernel = match &surface {
                    Some(surface) => {
                        let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                        let pre_state = context
                            .old_reference_state(&execution.core.frontier, &execution.core.state);
                        lower_fixed_state_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            context.parsed_function.parameters(),
                            context.arguments,
                            pre_state,
                            &execution.core.state,
                            None,
                            &execution.presentation.recorded_snapshots,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .map_err(|message| {
                            self.step_error(format!("could not unfold proposition goal: {message}"))
                        })?
                    }
                    None => unfold_predicates_in_proposition(
                        context.predicate_environment,
                        context.click_function_environment,
                        std::slice::from_ref(name),
                        goal.kernel(),
                        checked.facts.assumptions(),
                    )
                    .map_err(|message| self.step_error(message))?,
                };
                Some((kernel, surface))
            }
            _ => None,
        };
        let goal_context = BranchState {
            facts: checked.facts,
            unfolded_predicates,
            execution: Some(Arc::new(execution)),
        };
        let goal = match refined_goal {
            Some((kernel, surface)) => self.refined_proposition(goal_context, kernel, surface),
            None => self
                .focused_branch()
                .expect("execution unfold requires an open goal")
                .with_state(goal_context),
        };
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            // A nested proposition proof stated at this frontier unfolds its
            // own goal through the same checked operation. Other execution
            // goals retain their kind while installing the updated snapshot
            // and unfold delta.
            branch: Some(goal),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    pub(super) fn apply_execution_resource_observation(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`observe` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`observe`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(
                self.step_error("`observe` must run before execution reaches function exit")
            );
        }
        let before_facts = self.facts().clone();
        let checked = observe_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.core.state).clone(),
            self.facts().clone(),
            &mut execution.presentation.surface_propositions,
            &mut execution.core.function_entry_derivations,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution
            .core
            .record_resource_observation(
                context.function,
                context.arguments,
                &before_facts,
                &checked.observed_resource,
                &checked.state,
                &checked.facts,
            )
            .map_err(|message| {
                self.step_error(format!("kernel rejected checked `observe`: {message}"))
            })?;
        execution.core.state = checked.state.into();
        let branch = self
            .focused_branch()
            .expect("resource observation requires an open goal")
            .with_state(BranchState {
                facts: checked.facts,
                unfolded_predicates: self.focused_branch_unfolds().clone(),
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    pub(super) fn apply_execution_resource_unfold(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource `unfold` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("resource `unfold`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(self
                .step_error("resource `unfold` must run before execution reaches function exit"));
        }
        let before_facts = self.facts().clone();
        let checked = unfold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.core.state).clone(),
            self.facts().clone(),
            &mut execution.presentation.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution
            .core
            .record_resource_rewrite(
                context.function,
                context.arguments,
                &before_facts,
                &checked.selected,
                &checked.state,
                &checked.facts,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "kernel rejected checked resource `unfold`: {message}"
                ))
            })?;
        execution.core.state = checked.state.into();
        let branch = self
            .focused_branch()
            .expect("resource unfold requires an open goal")
            .with_state(BranchState {
                facts: checked.facts,
                unfolded_predicates: self.focused_branch_unfolds().clone(),
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    pub(super) fn apply_execution_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource `fold` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("resource `fold`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(
                self.step_error("resource `fold` must run before execution reaches function exit")
            );
        }
        let before_facts = self.facts().clone();
        let pre_state = context
            .old_reference_state(&execution.core.frontier, &execution.core.state)
            .clone();
        let checked = fold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            context.tactic_index,
            self.facts().clone(),
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            (*execution.core.state).clone(),
            context.predicate_environment,
            context.click_function_environment,
            &execution.core.unfolded_predicates,
        )?;
        let selected = lower_resource_clause(
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            checked.state.memory(),
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
                self.step_error(format!(
                    "kernel rejected checked resource `fold`: {message}"
                ))
            })?;
        execution.core.state = checked.state.into();
        let branch = self
            .focused_branch()
            .expect("resource fold requires an open goal")
            .with_state(BranchState {
                facts: checked.facts,
                unfolded_predicates: self.focused_branch_unfolds().clone(),
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: Vec::new(),
            checked_facts: Vec::new(),
        })
    }

    /// Applies one source-ordered composite fold to the focused branch typed outcome.
    /// The result/state snapshot and persistent fact root advance together in
    /// the returned Proof successor; no caller-owned outcome is mutated.
    pub(super) fn apply_outcome_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource `fold` requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("outcome resource `fold` requires a focused outcome goal"));
        };
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let execution = branch_state.execution.as_deref().ok_or_else(|| {
            self.step_error("outcome resource `fold` lost its execution snapshot")
        })?;
        let pre_state = execution
            .core
            .frontier
            .execution_start_state(&execution.core.state);
        let outcome = CFunctionOutcome::Return {
            value: (*goal.data.core.result).clone(),
            state: (*goal.data.core.state).clone(),
        };
        let checked = fold_composite_resource_on_outcome_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            goal.path_index,
            &goal.data.core.execution_pure_facts,
            self.facts().clone(),
            &goal.data.surface_propositions,
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            outcome,
            context.predicate_environment,
            context.click_function_environment,
            &self.active_unfolded_predicates(),
        )?;
        let CFunctionOutcome::Return { value, state } = checked.outcome else {
            unreachable!("folding a return outcome preserves its outcome kind")
        };
        let mut data = (*goal.data).clone();
        data.core.result = Arc::new(value);
        data.core.state = state.into();
        let mut updated = goal.clone();
        updated.data = Arc::new(data);
        let state = BranchState {
            facts: checked.facts,
            unfolded_predicates: branch_state.unfolded_predicates.clone(),
            execution: branch_state.execution.clone(),
        };
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(OpenBranch::function_outcome(updated, state)),
            added_facts: Vec::new(),
            checked_facts: Vec::new(),
        })
    }
}
