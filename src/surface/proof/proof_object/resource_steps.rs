//! Predicate and resource unfold/fold/observation steps.

use super::*;
use crate::kernel::{IntegerTerm, SharedIntegerTerm};

impl<'a> Proof<'a> {
    fn apply_instance_rewrite(
        &self,
        binding: &ResourceInstanceBinding,
        resource: &ResourceClause,
        unfold: bool,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if !binding.children.is_empty() {
            return Err(self.step_error("parent-qualified resource handles are not supported; use `let { slot: child } = unfold(parent)` and the independent child name"));
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
            let lowered = lower_resource_clause_at_current_locals(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                before,
                outcome.map(|goal| &*goal.data.core.result),
            )?;
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
                .map_err(|message| {
                    // The kernel can only say the identity is absent. Here the
                    // reader's own initializer is in hand, so the one renderer
                    // names the field, the instance and the repair instead.
                    let message =
                        crate::surface::diagnostics::describe_unheld_model_field_initializer(
                            &expression,
                            before,
                            pre_state,
                            context.parsed_function.parameters(),
                            context.arguments,
                        )
                        .unwrap_or(message);
                    self.step_error(format!("fold field `{name}`: {message}"))
                })?;
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
        let rewrite = crate::kernel::rewrite_resource_instance_selecting_children(
            before,
            instance,
            definition,
            context.function.composite_resource_definitions(),
            self.facts().assumptions(),
            unfold,
            selected_children.as_deref(),
        )
        .map_err(|refusal| self.step_error(refusal.describe()))?;
        let clause_presentations = if unfold {
            let source_bindings = rewrite.body_clauses.first().and_then(|clause| {
                let variant = clause.arm.as_deref()?;
                context
                    .resource_environment
                    .get(instance.name())?
                    .composite_body()?
                    .matched
                    .as_ref()?
                    .arms
                    .iter()
                    .find(|arm| arm.variant == variant)
                    .map(|arm| arm.bindings.as_slice())
            });
            let in_scope = source_bindings.filter(|names| {
                names.iter().all(|name| {
                    self.state().locals().values.contains_key(name)
                        || self.state().locals().integer_values.contains_key(name)
                })
            });
            crate::surface::proof::resources::pair_instance_body_clause_presentations(
                context.resource_environment,
                context.click_function_environment,
                instance,
                &rewrite.body_clauses,
                &parameter_values(context.parsed_function.parameters(), context.arguments)?,
                in_scope,
            )?
        } else {
            Vec::new()
        };
        let after = rewrite.state;
        let added = rewrite.semantic_facts;
        let mut facts = self.facts().clone();
        for fact in &added {
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        if clause_presentations
            .iter()
            .any(|clause| !clause.matches_available_fact(&facts))
        {
            return Err(
                self.step_error("resource unfold clause presentation lacks its checked fact")
            );
        }
        for clause in clause_presentations {
            execution.presentation.resource_body_clauses.push(clause);
        }
        // The unfold exposed this arm's cells; name them in the snapshot so
        // the body's facts and the C's own reads of those cells share one
        // load identity. See `materialize_unfolded_instance_arm_cells`.
        //
        // The naming is decided under the premises the rewrite itself
        // published, not under the ones standing before it: an `unfold` whose
        // arm was decided only by refuting the others names that arm's cells
        // exactly as an arm decided by a `requires` does. That is one arm
        // publication per frontier, consumed whole.
        let after = if unfold {
            crate::surface::proof::resources::materialize_unfolded_instance_arm_cells(
                context.resource_environment,
                context.click_function_environment,
                context.parsed_function.parameters(),
                context.arguments,
                after,
                instance,
                facts.assumptions(),
            )
        } else {
            after
        };
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
        premises: Option<&[ClickProposition]>,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let mut referenced_names = BTreeSet::new();
        for argument in &application.arguments {
            collect_contract_expression_referenced_names(argument, &mut referenced_names);
        }
        // Unfolding refreshes the complete retained goal, not only the call
        // selected by this step. Keep every algebraic proof local named by
        // that goal available while it is lowered again. This remains
        // output-sensitive: unrelated proof locals are never scanned or
        // cloned.
        if let Some(goal) = self.surface_goal() {
            collect_click_proposition_referenced_names(goal, &mut referenced_names);
        }
        if let Some(premises) = premises {
            for premise in premises {
                collect_click_proposition_referenced_names(premise, &mut referenced_names);
            }
        }
        let local_algebraic_values = |inherited: BTreeMap<String, SpecAlgebraicExpression>| {
            referenced_names
                .iter()
                .filter_map(|name| {
                    self.local_algebraic_values()
                        .get(name)
                        .or_else(|| inherited.get(name))
                        .cloned()
                        .map(|value| (name.clone(), value))
                })
                .collect::<BTreeMap<_, _>>()
        };
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                let state = CState::new().with_memory(context.theorem_context.memory.clone());
                self.apply_function_unfold_in_state(
                    application,
                    premises,
                    context.theorem_context.values.clone(),
                    context.theorem_context.array_refs.clone(),
                    local_algebraic_values(
                        context
                            .structural_induction_setup
                            .as_ref()
                            .map(|setup| setup.algebraic_values.clone())
                            .unwrap_or_default(),
                    ),
                    &context.theorem_context.integer_values,
                    &state,
                    &state,
                    None,
                    &RecordedSnapshots::new(),
                    context.predicate_environment,
                    context.click_function_environment,
                    BTreeMap::new(),
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
                    premises,
                    values,
                    array_refs,
                    local_algebraic_values(BTreeMap::new()),
                    &crate::persistent::PersistentMap::default(),
                    context.pre_state,
                    context.state,
                    context.result,
                    context.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                    crate::surface::lowering::parameter_pointer_element_widths(context.parameters),
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
                    premises,
                    values,
                    array_refs,
                    local_algebraic_values(BTreeMap::new()),
                    &crate::persistent::PersistentMap::default(),
                    view.pre_state,
                    view.state,
                    view.result,
                    view.recorded_snapshots,
                    view.predicate_environment,
                    view.click_function_environment,
                    crate::surface::lowering::parameter_pointer_element_widths(view.parameters),
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
                    premises,
                    values,
                    array_refs,
                    local_algebraic_values(BTreeMap::new()),
                    &crate::persistent::PersistentMap::default(),
                    pre_state,
                    &execution.core.state,
                    None,
                    &execution.presentation.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                    crate::surface::lowering::parameter_pointer_element_widths(
                        context.parsed_function.parameters(),
                    ),
                )
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_function_unfold_in_state(
        &self,
        application: &ClickFunctionApplication,
        premises: Option<&[ClickProposition]>,
        values: BTreeMap<String, CValue>,
        array_refs: ClickArrayRefs,
        algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
        integer_values: &crate::persistent::PersistentMap<
            String,
            crate::kernel::SpecIntegerExpression,
        >,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
        recorded_snapshots: &RecordedSnapshots,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        parameter_pointer_element_widths: BTreeMap<String, u32>,
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
                arguments: checked_arguments.clone(),
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
                integer_values,
                pre_state,
                state,
                result,
                recorded_snapshots,
                predicate_environment,
                click_function_environment,
                &BTreeSet::from([application.name.clone()]),
                parameter_pointer_element_widths.clone(),
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not lower defining equation for `{}`: {message}",
                    application.name
                ))
            })?;

        // `unfold(f(args)) using { ... }` opens one layer too, but the layer
        // it opens is the range-fold law the listed guards select, stated
        // over `f(args)` rather than over the fold the declaration writes.
        // Its single fact is that equation, and the goal is refreshed through
        // it; the raw defining equation stays inside the step, where the
        // kernel law consumes it.
        if let Some(premises) = premises {
            let derived = self.derive_function_range_fold_equation(
                application,
                &definition,
                premises,
                &equality,
                &values,
                &array_refs,
                &algebraic_values,
                integer_values,
                pre_state,
                state,
                result,
                recorded_snapshots,
                predicate_environment,
                click_function_environment,
                &parameter_pointer_element_widths,
            )?;
            let mut facts = self.facts().clone();
            let added = (!facts.contains_top_level(&derived))
                .then(|| derived.clone())
                .into_iter()
                .collect::<Vec<_>>();
            facts = facts.with_kernel_checked_fact(derived.clone());
            let branch = match self.focused_obligation() {
                Some(Obligation::Proposition(goal)) => {
                    let Proposition::ConditionIs(
                        ConditionTerm::IntegerEqual(unfolded, replacement),
                        true,
                    ) = &derived
                    else {
                        return Err(self.step_error(
                            "the restated fold law did not produce an Integer equation",
                        ));
                    };
                    let kernel = crate::kernel::substitute_integer_term_in_proposition(
                        goal.kernel(),
                        unfolded,
                        replacement,
                    )
                    .unwrap_or_else(|| goal.kernel().clone());
                    // Refreshing only the kernel goal would leave every later
                    // tactic that dispatches on the written claim -- `arithmetic`
                    // over the `Integer` fragment among them -- reading a goal
                    // this step has already replaced. Rebuild the Surface
                    // spelling of the same refreshed claim, and install it only
                    // when it lowers back to exactly this kernel proposition.
                    let surface = goal.surface.as_deref().and_then(|surface_goal| {
                        let lower = |candidate: &ClickProposition| {
                            let candidate =
                                self.substitute_fixed_state_locals_in_proposition(candidate).ok()?;
                            let mut opaque_calls = BTreeSet::new();
                            crate::surface::validation::collect_click_function_calls_in_proposition(
                                &candidate,
                                &mut opaque_calls,
                            );
                            lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
                                &candidate,
                                facts.assumptions(),
                                &values,
                                &array_refs,
                                &algebraic_values,
                                integer_values,
                                pre_state,
                                state,
                                result,
                                recorded_snapshots,
                                predicate_environment,
                                click_function_environment,
                                &opaque_calls,
                                parameter_pointer_element_widths.clone(),
                            )
                            .ok()
                        };
                        self.refreshed_fold_law_surface_goal(
                            application,
                            &definition,
                            surface_goal,
                            &kernel,
                            &lower,
                        )
                    });
                    let complete = facts.contains(&kernel);
                    (!complete).then(|| {
                        self.refined_proposition(
                            self.refined_branch_state(facts.clone()),
                            kernel,
                            surface,
                            false,
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
            return Ok(CheckedFocusedTransition {
                locals: self.state().locals().clone(),
                branch,
                added_facts: added.clone(),
                checked_facts: added,
            });
        }

        let mut facts = self.facts().clone();
        let added_facts = (!facts.contains_top_level(&equality))
            .then(|| equality.clone())
            .into_iter()
            .collect::<Vec<_>>();
        facts = facts.with_kernel_checked_fact(equality.clone());

        let branch = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => {
                let mut original_surface = goal.surface.as_deref().cloned();
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
                        integer_values,
                        pre_state,
                        state,
                        result,
                        recorded_snapshots,
                        predicate_environment,
                        click_function_environment,
                        &opaque_calls,
                        parameter_pointer_element_widths,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not refresh the goal after function `unfold`: {message}"
                        ))
                    })?
                } else {
                    // Contextual numerals and synthesized C constants may have
                    // different surface nodes but denote the same typed call.
                    // Use the checked defining equality on the kernel goal and
                    // discard stale presentation after a successful rewrite.
                    match rewrite_proposition_by_exact_equality(
                        goal.kernel(),
                        &equality,
                        std::slice::from_ref(&equality),
                    ) {
                        Ok(rewritten) => {
                            original_surface = None;
                            rewritten
                        }
                        Err(_) => goal.kernel().clone(),
                    }
                };
                let complete = facts.contains(&kernel);
                (!complete).then(|| {
                    self.refined_proposition(
                        self.refined_branch_state(facts.clone()),
                        kernel,
                        surface.or(original_surface),
                        false,
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

    /// The `using` half of a pure-function unfold: the range-fold law the
    /// listed guards select, restated over the function application by
    /// `crate::kernel::prove_integer_range_fold_over_equal_terms`.
    ///
    /// Returns the facts to publish beside the defining equation: the
    /// predecessor instance of that equation for the append form, then the
    /// law's conclusion. Every premise the kernel theorem carries -- the two
    /// defining equations and the law's own guards -- is discharged here
    /// against exactly the listed evidence; nothing is searched.
    #[allow(clippy::too_many_arguments)]
    fn derive_function_range_fold_equation(
        &self,
        application: &ClickFunctionApplication,
        definition: &ClickFunctionDefinition,
        premises: &[ClickProposition],
        equality: &Proposition,
        values: &BTreeMap<String, CValue>,
        array_refs: &ClickArrayRefs,
        algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
        integer_values: &crate::persistent::PersistentMap<
            String,
            crate::kernel::SpecIntegerExpression,
        >,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
        recorded_snapshots: &RecordedSnapshots,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        parameter_pointer_element_widths: &BTreeMap<String, u32>,
    ) -> Result<Proposition, ClickError> {
        let name = &application.name;
        let lower =
            |proposition: &ClickProposition, what: &str| -> Result<Proposition, ClickError> {
                let proposition = self.substitute_fixed_state_locals_in_proposition(proposition)?;
                let mut opaque_calls = BTreeSet::new();
                crate::surface::validation::collect_click_function_calls_in_proposition(
                    &proposition,
                    &mut opaque_calls,
                );
                lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
                    &proposition,
                    self.facts().assumptions(),
                    values,
                    array_refs,
                    algebraic_values,
                    integer_values,
                    pre_state,
                    state,
                    result,
                    recorded_snapshots,
                    predicate_environment,
                    click_function_environment,
                    &opaque_calls,
                    parameter_pointer_element_widths.clone(),
                )
                .map_err(|message| self.step_error(format!("could not lower {what}: {message}")))
            };

        // Exactly the listed premises, each of which must already hold.
        let mut available = Vec::new();
        for premise in premises {
            let lowered = lower(premise, "an `unfold ... using` premise")?;
            if !self.facts().exact_available_across_effects(&lowered, &[]) {
                return Err(self.step_error(format!(
                    "`unfold({name}(...)) using` requires an unavailable exact premise: {}",
                    describe_pure_fact(&lowered, &[], &[])
                )));
            }
            available.push(lowered);
        }

        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(whole, folded), true) = equality
        else {
            return Err(self.step_error(format!(
                "`unfold({name}(...)) using` applies to an `Integer`-valued pure function whose body is a range fold"
            )));
        };
        let IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } = folded.as_ref()
        else {
            return Err(self.step_error(format!(
                "`unfold({name}(...)) using` requires the body of `{name}` to be a range fold over a symbolic range; this call's range is already reduced"
            )));
        };

        let empty = crate::kernel::prove_integer_range_fold_over_equal_terms(
            index.clone(),
            initial.as_ref().clone(),
            *accumulator,
            *item,
            body.as_ref().clone(),
            whole.as_ref().clone(),
            None,
        )
        .map_err(|reason| {
            self.step_error(format!(
                "the Integer fold empty law could not be stated over `{name}`: {reason}"
            ))
        })?;
        available.push(equality.clone());
        let mut empty_missing = Vec::new();
        if discharge_restated_fold_law(&empty, &available, &mut empty_missing) {
            let Proposition::Implies(_, conclusion) = empty.proposition() else {
                return Err(
                    self.step_error("the Integer fold law did not produce a guarded theorem")
                );
            };
            return Ok(conclusion.as_ref().clone());
        }

        let prior =
            self.function_range_fold_predecessor_application(application, definition, whole)?;
        let append = crate::kernel::prove_integer_range_fold_over_equal_terms(
            index.clone(),
            initial.as_ref().clone(),
            *accumulator,
            *item,
            body.as_ref().clone(),
            whole.as_ref().clone(),
            Some(prior.clone()),
        )
        .map_err(|reason| {
            self.step_error(format!(
                "the Integer fold append law could not be stated over `{name}` at the predecessor endpoint: {reason}"
            ))
        })?;
        let Proposition::Implies(append_guard, append_conclusion) = append.proposition() else {
            return Err(self.step_error("the Integer fold law did not produce a guarded theorem"));
        };
        // The law carries two defining equations beside its guards. One is
        // the equation this step just published; the other is that equation
        // at the predecessor endpoint, which only the surface can supply
        // because only it knows the declaration. Recognize it against the
        // predecessor application, and publish it beside the conclusion.
        let mut required = Vec::new();
        collect_conjunctive_premises(append_guard, &mut required);
        let mut predecessor_equality = false;
        let mut append_missing = Vec::new();
        for premise in required {
            if premise == equality {
                continue;
            }
            if let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) =
                premise
                && left.as_ref() == &prior
                && matches!(right.as_ref(), IntegerTerm::RangeFold { .. })
            {
                predecessor_equality = true;
                continue;
            }
            if !exact_fact_is_available(premise, &available)
                && !matches!(normalize_proposition(premise), SimpProposition::True)
            {
                append_missing.push(premise.clone());
            }
        }
        if !append_missing.is_empty() {
            return Err(self.step_error(format!(
                "`unfold({name}(...)) using` found no listed guard that decides the range. The empty-range equation needs {}; the append-last-cell equation needs {}.",
                describe_missing_fold_guards(&empty_missing),
                describe_missing_fold_guards(&append_missing)
            )));
        }
        if !predecessor_equality {
            return Err(self.step_error(format!(
                "the Integer fold append law over `{name}` did not state its predecessor endpoint"
            )));
        }
        Ok(append_conclusion.as_ref().clone())
    }

    /// `f(args)` with the argument that supplies the fold's end replaced by
    /// its predecessor, as a kernel term.
    ///
    /// The append form states the shorter fold as this application, so the
    /// fold's end must be a parameter of `f` and that parameter must not
    /// appear anywhere else in the fold. Under those two conditions the
    /// declared initial value and body are the same terms at both argument
    /// lists, and the two applications differ only in the fold's end
    /// endpoint. Nothing about the body is lowered again here: its reads
    /// were already checked over the longer range, and the append guards
    /// this step discharges keep the predecessor range inside it.
    fn function_range_fold_predecessor_application(
        &self,
        application: &ClickFunctionApplication,
        definition: &ClickFunctionDefinition,
        whole: &SharedIntegerTerm,
    ) -> Result<IntegerTerm, ClickError> {
        let name = &application.name;
        let ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } = definition.body()
        else {
            return Err(self.step_error(format!(
                "`unfold({name}(...)) using` requires the body of `{name}` to be exactly a range fold"
            )));
        };
        let Some(end_parameter) = fold_end_parameter_name(end).cloned() else {
            return Err(self.step_error(format!(
                "`unfold({name}(...)) using`: the append-last-cell equation restates the shorter fold as `{name}` at the predecessor endpoint, so the fold's end must be a parameter of `{name}`"
            )));
        };
        for (part, what) in [
            (start.as_ref(), "start"),
            (initial.as_ref(), "initial value"),
            (body.as_ref(), "body"),
        ] {
            if contract_expression_reads_binding(part, &end_parameter) {
                return Err(self.step_error(format!(
                    "`unfold({name}(...)) using`: the fold's {what} also reads `{end_parameter}`, so the shorter fold is not `{name}` at the predecessor endpoint"
                )));
            }
        }
        let position = definition
            .parameters()
            .iter()
            .position(|parameter| parameter.name() == end_parameter)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`unfold({name}(...)) using`: `{end_parameter}` is not a parameter of `{name}`"
                ))
            })?;
        crate::kernel::integer_range_fold_predecessor_application(whole.as_ref(), position)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`unfold({name}(...)) using` requires the call to remain the opaque application `{name}(...)` with an `int32` argument for `{end_parameter}`"
                ))
            })
    }

    /// The Surface spelling of the goal `unfold(f(args)) using { ... }` just
    /// refreshed, or `None` when this step cannot write one down.
    ///
    /// The kernel goal was refreshed by substituting the restated fold law's
    /// conclusion, so its written form has to be rebuilt from the declaration.
    /// The law replaces `f(args)` by one of exactly two expressions: the fold's
    /// initial value over an empty range, or the fold's body at the predecessor
    /// endpoint accumulated onto `f(args)` at that endpoint. Both are candidate
    /// spellings only; the one installed is the one that lowers back to exactly
    /// the refreshed kernel proposition, so a later tactic that dispatches on
    /// the written goal reads this step's checked claim rather than a guess.
    fn refreshed_fold_law_surface_goal(
        &self,
        application: &ClickFunctionApplication,
        definition: &ClickFunctionDefinition,
        surface_goal: &ClickProposition,
        refreshed_kernel: &Proposition,
        lower: &dyn Fn(&ClickProposition) -> Option<Proposition>,
    ) -> Option<ClickProposition> {
        let ContractExpression::RangeFold {
            end,
            initial,
            accumulator,
            item,
            body,
            ..
        } = definition.body()
        else {
            return None;
        };
        let substitutions = definition
            .parameters()
            .iter()
            .zip(&application.arguments)
            .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let substitute = |expression: &ContractExpression| {
            substitute_contract_expression(expression, &substitutions).ok()
        };
        let whole = ContractExpression::Call {
            name: application.name.clone(),
            arguments: application.arguments.clone(),
        };
        let mut candidates = Vec::new();
        if let Some(initial) = substitute(initial) {
            candidates.push(initial);
        }
        if let Some(position) = fold_end_parameter_name(end)
            .and_then(|end| {
                definition
                    .parameters()
                    .iter()
                    .position(|parameter| parameter.name() == end)
            })
            .filter(|position| *position < application.arguments.len())
            && let Some(body) = substitute(body)
        {
            let predecessor_end = ContractExpression::Subtract(
                Box::new(application.arguments[position].clone()),
                Box::new(ContractExpression::IntegerLiteral("1".to_string())),
            );
            let mut arguments = application.arguments.clone();
            arguments[position] = predecessor_end.clone();
            let cell = BTreeMap::from([
                (
                    accumulator.clone(),
                    ContractExpression::Call {
                        name: application.name.clone(),
                        arguments,
                    },
                ),
                (item.clone(), predecessor_end),
            ]);
            if let Ok(appended) = substitute_contract_expression(&body, &cell) {
                candidates.push(appended);
            }
        }
        for candidate in candidates {
            crate::instrumentation::record_deterministic_work(1);
            let equality = ClickProposition::Comparison {
                left: whole.clone(),
                operator: ComparisonOperator::Equal,
                right: candidate,
            };
            let Some(rewritten) =
                rewrite_click_proposition_by_surface_equality(surface_goal, &equality)
            else {
                continue;
            };
            if lower(&rewritten).as_ref() == Some(refreshed_kernel) {
                return Some(rewritten);
            }
        }
        None
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
                    false,
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
            Some((kernel, surface)) => {
                self.refined_proposition(goal_context, kernel, surface, false)
            }
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
            context.function,
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
        self.apply_outcome_resource_fold_with_closure(resource, ResourceBodyClosure::Initialize)
    }

    /// Closing an already open scope is checked by the same resource law as
    /// an explicit fold, with the scope's ownership-preservation policy.
    pub(in crate::surface::proof) fn close_outcome_resource_scope(
        &self,
        resource: &ResourceClause,
        preserve_exposed_body: bool,
    ) -> Result<Self, ClickError> {
        let transition = self.apply_outcome_resource_fold_with_closure(
            resource,
            ResourceBodyClosure::CloseOpen {
                preserve_exposed_body,
            },
        )?;
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: self.publish_checked_transition(transition)?,
            node: self.node.clone(),
        };
        Ok(successor)
    }

    fn apply_outcome_resource_fold_with_closure(
        &self,
        resource: &ResourceClause,
        closure: ResourceBodyClosure,
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
            &goal.data.core.effect_facts,
            self.facts().clone(),
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            outcome,
            context.predicate_environment,
            context.click_function_environment,
            &self.active_unfolded_predicates(),
            closure,
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
        let assumptions = self.facts().assumptions();
        let state = crate::kernel::construct_c_function_resource(
            &state,
            context.function,
            context.arguments,
            &value,
            &fact,
            assumptions,
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

/// Whether every premise of a restated fold law is exactly available,
/// collecting the ones that are not. A premise that normalizes to `true`
/// without any evidence counts as discharged, exactly as `apply ... using`
/// treats the fold laws' own guards.
fn discharge_restated_fold_law(
    theorem: &crate::kernel::Theorem,
    available: &[Proposition],
    missing: &mut Vec<Proposition>,
) -> bool {
    let Proposition::Implies(guard, _) = theorem.proposition() else {
        return false;
    };
    let mut required = Vec::new();
    collect_conjunctive_premises(guard, &mut required);
    for premise in required {
        if !exact_fact_is_available(premise, available)
            && !matches!(normalize_proposition(premise), SimpProposition::True)
        {
            missing.push(premise.clone());
        }
    }
    missing.is_empty()
}

/// Whether substituting this binding changes the expression. The parts of a
/// range fold other than its end must not read the parameter that supplies
/// that end, or the shorter fold would not be the same function applied at a
/// smaller endpoint. A substitution failure counts as an occurrence: the
/// check refuses rather than guesses.
fn contract_expression_reads_binding(expression: &ContractExpression, binding: &str) -> bool {
    let substitutions = BTreeMap::from([(
        binding.to_string(),
        ContractExpression::IntegerLiteral("0".to_string()),
    )]);
    substitute_contract_expression(expression, &substitutions)
        .map(|substituted| &substituted != expression)
        .unwrap_or(true)
}

/// The parameter name a range fold's end endpoint is written as, when it is
/// written as a bare name at all. The append form of the fold law restates the
/// shorter fold as the same application at the predecessor endpoint, so both
/// the law's own check and the refreshed goal's Surface spelling need it.
fn fold_end_parameter_name(end: &ContractExpression) -> Option<&String> {
    match end {
        ContractExpression::Binding(binding)
        | ContractExpression::CBinding(binding)
        | ContractExpression::CFragment(CExpression::Variable(binding)) => Some(binding),
        _ => None,
    }
}

fn collect_conjunctive_premises<'a>(
    proposition: &'a Proposition,
    facts: &mut Vec<&'a Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            collect_conjunctive_premises(left, facts);
            collect_conjunctive_premises(right, facts);
        }
        proposition => facts.push(proposition),
    }
}

/// The guards a restated fold law still wants, in the order the kernel
/// states them. A defining-equation premise is never listed: the step
/// produces those itself, so naming one would point the reader at evidence
/// they cannot write.
fn describe_missing_fold_guards(missing: &[Proposition]) -> String {
    let rendered = missing
        .iter()
        .filter(|premise| {
            !matches!(
                premise,
                Proposition::ConditionIs(ConditionTerm::IntegerEqual(_, _), true)
            )
        })
        .map(|premise| {
            format!(
                "`{}`",
                crate::surface::proof_diagnostics::render::render_proposition(premise)
            )
        })
        .collect::<Vec<_>>();
    if rendered.is_empty() {
        return "no further guard".to_string();
    }
    rendered.join(" and ")
}
