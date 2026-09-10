//! Predicate and resource unfold/fold/observation steps.

use super::*;

impl<'a> Proof<'a> {
    fn apply_instance_rewrite(
        &self,
        binding: &ResourceInstanceBinding,
        resource: &ResourceClause,
        unfold: bool,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if !binding.children.is_empty() {
            return Err(self.step_error("parent-qualified resource handles are not supported; use `unfold(parent) as { slot: child }` and the independent child name"));
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("instance fold/unfold requires a C execution proof"));
        };
        let branch = self
            .focused_branch()
            .ok_or_else(|| self.step_error("instance rewrite requires an open goal"))?;
        let mut execution = branch
            .state
            .execution
            .as_deref()
            .cloned()
            .ok_or_else(|| self.step_error("instance rewrite has no execution snapshot"))?;
        let outcome = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => Some(goal),
            _ => {
                self.require_execution_frontier("instance fold/unfold")?;
                None
            }
        };
        let before: &CState = outcome.map_or(&*execution.core.state, |goal| &*goal.data.core.state);
        let pre_state = context.old_reference_state(&execution.core.frontier, before);
        let constructed;
        let instance = if let Some(fields) = &binding.fold_fields {
            if unfold || !binding.children.is_empty() {
                return Err(self.step_error("explicit fields require a fold construction"));
            }
            let ResourceClause::Named { resource, .. } = resource else {
                unreachable!()
            };
            let lowered = if let Some(goal) = outcome {
                lower_resource_clause_at_state_with_result(
                    resource,
                    context.parsed_function.parameters(),
                    context.arguments,
                    before,
                    &goal.data.core.result,
                )?
            } else {
                lower_resource_clause_at_state(
                    resource,
                    context.parsed_function.parameters(),
                    context.arguments,
                    before,
                )?
            };
            let CResourceFact::Own(CResource::Composite { name, arguments }, _) = lowered else {
                return Err(self.step_error("fold construction requires an owned resource"));
            };
            let definition = context
                .function
                .composite_resource_definition(&name)
                .ok_or_else(|| self.step_error("fold resource has no checked definition"))?;
            let schema = definition
                .instance_field_schema()
                .ok_or_else(|| self.step_error("fold resource has no fields"))?;
            let mut supplied = BTreeMap::new();
            for (name, value) in fields {
                if supplied.insert(name.as_str(), value).is_some() {
                    return Err(self.step_error(format!("duplicate fold field `{name}`")));
                }
            }
            if supplied.len() != schema.fields().len() {
                return Err(self.step_error("fold must explicitly supply every resource field"));
            }
            let values = parameter_values(context.parsed_function.parameters(), context.arguments)?;
            let array_refs = array_refs_for_parameters(
                context.parsed_function.parameters(),
                &values,
                before.memory(),
            );
            let (values, array_refs) = contract_environment_at_state(&values, &array_refs, before);
            let mut proposed = Vec::new();
            for (name, ty) in schema.fields() {
                let expression = supplied
                    .get(name.as_str())
                    .ok_or_else(|| self.step_error(format!("missing fold field `{name}`")))?;
                let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
                let value = capture_resource_field_initializer(
                    &expression,
                    ty,
                    self.facts().assumptions(),
                    &values,
                    &array_refs,
                    pre_state,
                    before,
                    &execution.presentation.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| self.step_error(format!("fold field `{name}`: {message}")))?;
                proposed.push(value);
            }
            let identity = pre_state
                .owned_resource_instance(binding.identity)
                .map_or(binding.identity, |instance| instance.identity());
            constructed = crate::kernel::ResourceInstance::new(
                identity,
                name,
                arguments,
                schema.clone(),
                proposed.into(),
            )
            .ok_or_else(|| self.step_error("invalid fold fields"))?;
            &constructed
        } else {
            before
                .resource_instance_at_path(binding.identity, &binding.children)
                .or_else(|| {
                    if !unfold && binding.children.is_empty() {
                        pre_state.owned_resource_instance(binding.identity)
                    } else {
                        None
                    }
                })
                .ok_or_else(|| {
                    self.step_error(
                        "resource instance is not owned and has no entry-state fold template",
                    )
                })?
        };
        let definition = context
            .function
            .composite_resource_definition(instance.name())
            .ok_or_else(|| self.step_error("resource instance has no registered body"))?;
        let selected = CResourceFact::own(CResource::Instance(instance.clone()));
        let selected_children = binding
            .child_bindings
            .as_ref()
            .map(|children| {
                children
                    .iter()
                    .map(|(slot, name, identity)| {
                        let identity = if unfold {
                            *identity
                        } else {
                            before
                                .owned_resource_instance(*identity)
                                .ok_or_else(|| {
                                    self.step_error(format!(
                                        "child `{name}` is not owned in folded form"
                                    ))
                                })?
                                .identity()
                        };
                        Ok((slot.clone(), identity))
                    })
                    .collect::<Result<Arc<[(String, Variable)]>, ClickError>>()
            })
            .transpose()?;
        let (after, added) = crate::kernel::rewrite_resource_instance_selecting_children(
            before,
            instance,
            definition,
            self.facts().assumptions(),
            unfold,
            selected_children.as_deref(),
        )
        .map_err(|message| self.step_error(message))?;
        let mut facts = self.facts().clone();
        for fact in &added {
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        let updated_branch = if let Some(goal) = outcome {
            execution
                .core
                .record_return_resource_rewrite_with_children(
                    context.function,
                    goal.path_index,
                    self.facts(),
                    &selected,
                    &facts,
                    selected_children.clone(),
                )
                .map_err(|message| self.step_error(message))?;
            execution.core.state = after.clone().into();
            let mut updated = goal.clone();
            let mut data = (*goal.data).clone();
            data.core.state = after.into();
            updated.data = Arc::new(data);
            OpenBranch::function_outcome(
                updated,
                BranchState {
                    facts,
                    unfolded_predicates: branch.state.unfolded_predicates.clone(),
                    execution: Some(Arc::new(execution)),
                },
            )
        } else {
            execution
                .core
                .record_resource_rewrite_with_children(
                    context.function,
                    context.arguments,
                    self.facts(),
                    &selected,
                    &after,
                    &facts,
                    selected_children,
                )
                .map_err(|message| self.step_error(message))?;
            execution.core.state = after.into();
            branch.with_state(BranchState {
                facts,
                unfolded_predicates: branch.state.unfolded_predicates.clone(),
                execution: Some(Arc::new(execution)),
            })
        };
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(updated_branch),
            added_facts: added.clone(),
            checked_facts: added,
        })
    }

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
                    context
                        .structural_induction_setup
                        .as_ref()
                        .map(|setup| setup.algebraic_values.clone())
                        .unwrap_or_default(),
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
                    BTreeMap::new(),
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
                    BTreeMap::new(),
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
                    BTreeMap::new(),
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
        algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
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
        let checked_arguments = application
            .arguments
            .iter()
            .map(|argument| self.substitute_fixed_state_locals_in_expression(argument))
            .collect::<Result<Vec<_>, _>>()?;
        let variable_types = generics::concrete_variable_types(&values, &algebraic_values);
        let definition = generics::instantiate_function_for_surface_call_with_variables(
            definition,
            &checked_arguments,
            &variable_types,
        )
        .map_err(|message| self.step_error(message))?;
        if application.arguments.len() != definition.parameters().len() {
            return Err(self.step_error(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                application.arguments.len()
            )));
        }

        let checked_substitutions = definition
            .parameters()
            .iter()
            .zip(&checked_arguments)
            .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let checked_body =
            substitute_contract_expression(definition.body(), &checked_substitutions).map_err(
                |message| {
                    self.step_error(format!(
                        "could not instantiate function `{}` for `unfold`: {message}",
                        application.name
                    ))
                },
            )?;
        let checked_equality = ClickProposition::Comparison {
            left: ContractExpression::Call {
                name: application.name.clone(),
                arguments: checked_arguments,
            },
            operator: ComparisonOperator::Equal,
            right: checked_body,
        };
        let equality =
            lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
                &checked_equality,
                self.facts().assumptions(),
                &values,
                &array_refs,
                &algebraic_values,
                &crate::persistent::PersistentMap::default(),
                pre_state,
                state,
                result,
                recorded_snapshots,
                predicate_environment,
                click_function_environment,
                &BTreeSet::from([application.name.clone()]),
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not lower defining equation for `{}`: {message}",
                    application.name
                ))
            })?;

        let mut facts = self.facts().clone();
        let added_facts = (!facts.contains_top_level(&equality))
            .then(|| equality.clone())
            .into_iter()
            .collect::<Vec<_>>();
        facts = facts.with_kernel_checked_fact(equality.clone());

        let branch = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => {
                let original_surface = goal.surface.as_deref().cloned();
                let substitutions = definition
                    .parameters()
                    .iter()
                    .zip(&application.arguments)
                    .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                    .collect::<BTreeMap<_, _>>();
                let surface_body =
                    substitute_contract_expression(definition.body(), &substitutions).map_err(
                        |message| {
                            self.step_error(format!(
                            "could not instantiate surface function `{}` for `unfold`: {message}",
                            application.name
                        ))
                        },
                    )?;
                // Keep the retained goal aligned with the constructor-iota
                // reduction performed by the kernel for this explicit unfold.
                // Unknown scrutinees remain matches; no pure calls are evaluated.
                // Walk selected arms by reference, substituting only their
                // scrutinees and the final body, not the remaining subtree
                // once per nested match.
                let mut selected_body = &surface_body;
                let mut bindings = BTreeMap::new();
                while let ContractExpression::AlgebraicMatch { scrutinee, arms } = selected_body {
                    crate::instrumentation::record_deterministic_work(1);
                    let scrutinee = substitute_contract_expression(scrutinee, &bindings)
                        .map_err(|message| self.step_error(message))?;
                    let ContractExpression::AlgebraicConstructor {
                        algebraic_type,
                        variant,
                        arguments,
                    } = &scrutinee
                    else {
                        break;
                    };
                    let Some(arm) = arms.iter().find(|arm| {
                        arm.type_name == algebraic_type.name
                            && arm.variant == *variant
                            && arm.bindings.len() == arguments.len()
                    }) else {
                        break;
                    };
                    bindings.extend(arm.bindings.iter().cloned().zip(arguments.iter().cloned()));
                    selected_body = &arm.body;
                }
                let surface_body = substitute_contract_expression(selected_body, &bindings)
                    .map_err(|message| self.step_error(message))?;
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
                    let checked_surface =
                        self.substitute_fixed_state_locals_in_proposition(surface)?;
                    let mut opaque_calls = BTreeSet::new();
                    crate::surface::validation::collect_click_function_calls_in_proposition(
                        &checked_surface,
                        &mut opaque_calls,
                    );
                    lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
                        &checked_surface,
                        facts.assumptions(),
                        &values,
                        &array_refs,
                        &algebraic_values,
                        &crate::persistent::PersistentMap::default(),
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
                } else if original_surface.is_none() {
                    // A nested proof can carry a checked kernel goal without
                    // retained source syntax. Unfold the selected occurrence
                    // by the same exact defining equality in that case.
                    rewrite_proposition_by_exact_equality(
                        goal.kernel(),
                        &equality,
                        std::slice::from_ref(&equality),
                    )
                    .unwrap_or_else(|_| goal.kernel().clone())
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
            self.facts(),
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
        let checked = check_unfold_predicate_facts(&mut execution, context, self.facts(), name)?;
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
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, true);
        }
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
            true,
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
        execution.presentation.resource_unfolded = true;
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
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, false);
        }
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
        let selected = lower_resource_clause_at_state(
            resource,
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

    /// Exposes one selected composite on a completed call's focused outcome.
    /// Reuse the ordinary checked definition law, binding the result only in
    /// the explicit resource operand; retain the original surface step.
    pub(super) fn apply_outcome_resource_unfold(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource `unfold` requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(
                self.step_error("outcome resource `unfold` requires a focused outcome goal")
            );
        };
        let resource = crate::surface::verification::substitute_resource_clause_for_summary(
            resource,
            &BTreeMap::from([(
                "result".to_string(),
                ContractExpression::CFragment(CExpression::Value((*goal.data.core.result).clone())),
            )]),
        )
        .map_err(|message| self.step_error(message))?;
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let mut data = (*goal.data).clone();
        let checked = unfold_composite_resource_for_proof(
            context.resource_environment,
            &resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*data.core.state).clone(),
            self.facts().clone(),
            &mut data.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
            false,
        )?;
        data.core.state = checked.state.into();
        let mut updated = goal.clone();
        updated.data = Arc::new(data);
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(OpenBranch::function_outcome(
                updated,
                BranchState {
                    facts: checked.facts,
                    unfolded_predicates: branch_state.unfolded_predicates.clone(),
                    execution: branch_state.execution.clone(),
                },
            )),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    /// Applies one source-ordered composite fold to the focused branch typed outcome.
    /// The result/state snapshot and persistent fact root advance together in
    /// the returned Proof successor; no caller-owned outcome is mutated.
    pub(super) fn apply_outcome_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, false);
        }
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

    /// Applies one kernel-checked, zero-source construction to the focused
    /// function outcome. The retained `ProofStep` is the certificate event;
    /// the kernel checks its authorization and exact one-token delta.
    pub(super) fn apply_outcome_resource_construction(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource `construct` requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(
                self.step_error("outcome resource `construct` requires a focused outcome goal")
            );
        };
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let execution = branch_state
            .execution
            .as_deref()
            .ok_or_else(|| self.step_error("resource `construct` lost its execution snapshot"))?;
        let value = (*goal.data.core.result).clone();
        let state = (*goal.data.core.state).clone();
        let fact = lower_resource_clause_at_state_with_result(
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            &state,
            &value,
        )?;
        let mut assumptions = self.facts().assumptions().clone();
        for execution_fact in goal.data.core.execution_pure_facts.iter() {
            assumptions = assumptions.assume_proposition(execution_fact.proposition().clone());
        }
        let state = crate::kernel::construct_c_function_resource(
            &state,
            context.function,
            context.arguments,
            &value,
            &fact,
            &assumptions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "kernel rejected checked resource `construct`: {message}"
            ))
        })?;
        let mut data = (*goal.data).clone();
        data.core.state = state.into();
        let mut updated = goal.clone();
        updated.data = Arc::new(data);
        let state = BranchState {
            facts: self.facts().clone(),
            unfolded_predicates: branch_state.unfolded_predicates.clone(),
            execution: Some(Arc::new(execution.clone())),
        };
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(OpenBranch::function_outcome(updated, state)),
            added_facts: Vec::new(),
            checked_facts: Vec::new(),
        })
    }
}
