//! Predicate and resource unfold/fold/observation steps.

use super::*;
use crate::kernel::proof::InstanceUnfoldError;
use crate::kernel::{IntegerTerm, SharedIntegerTerm};

impl<'a> Proof<'a> {
    /// Whether `resource` names a declared family that is not an
    /// `authorized resource`. Population accounting covers only authorized
    /// families; every other family folds, unfolds and rewrites by its
    /// ordinary definition law.
    fn names_unauthorized_family(&self, resource: &ResourceClause) -> bool {
        match resource {
            ResourceClause::Quantified { resource, .. }
            | ResourceClause::Conditional { resource, .. } => {
                self.names_unauthorized_family(resource)
            }
            ResourceClause::Declared { name, .. } => {
                let ProofContext::Execution(context) = self.context.as_ref() else {
                    return false;
                };
                context
                    .resource_environment
                    .get(name)
                    .is_some_and(|definition| !definition.is_authorized())
            }
            _ => false,
        }
    }

    /// Whether folding `resource` can touch a population, by the kernel's
    /// propagated reach of its registered definition. An unregistered family
    /// is treated as reaching one.
    fn family_reaches_population(&self, resource: &ResourceClause) -> bool {
        match resource {
            ResourceClause::Quantified { resource, .. }
            | ResourceClause::Conditional { resource, .. } => {
                self.family_reaches_population(resource)
            }
            ResourceClause::Declared { name, .. } => {
                let ProofContext::Execution(context) = self.context.as_ref() else {
                    return true;
                };
                context
                    .function
                    .composite_resource_definition(name)
                    .is_none_or(|definition| definition.reaches_population())
            }
            _ => true,
        }
    }

    fn is_authority_control_resource(&self, resource: &ResourceClause) -> bool {
        let ResourceClause::Declared { name, .. } = resource else {
            return false;
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return false;
        };
        context
            .function
            .composite_resource_definition(name)
            .is_some_and(|definition| {
                definition.contains().iter().any(|spec| {
                    matches!(
                        spec.term(),
                        crate::kernel::ResourceTerm::PopulationAuthority { .. }
                    )
                })
            })
    }

    /// Ordinary wrappers transfer existing children; they do not create or
    /// destroy a member by exposing its private memory body.
    fn is_authority_transfer_wrapper(&self, resource: &ResourceClause) -> bool {
        let ResourceClause::Declared { name, .. } = resource else {
            return false;
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return false;
        };
        let Some(execution) = self.execution() else {
            return false;
        };
        let (state, result) = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => {
                (&*goal.data.core.state, Some(goal.data.core.result.native()))
            }
            _ => (&*execution.core.state, None),
        };
        let selected = if let Some(result) = result {
            lower_resource_clause_at_state_with_result(
                resource,
                context.parameter_binding(),
                state,
                &result,
            )
        } else {
            lower_resource_clause_at_state(resource, context.parameter_binding(), state)
        };
        if selected.is_ok_and(|selected| state.tracks_authority_member(&selected)) {
            return false;
        }
        let Some(definition) = context.resource_environment.get(name) else {
            return false;
        };
        let Some(body) = definition.composite_body() else {
            return false;
        };
        definition.resource_parameters().is_empty()
            && definition.fields().is_empty()
            && body.children.is_empty()
            && body.matched.is_none()
            && body.condition.is_none()
            && body.facts.is_empty()
            && body.witnesses.is_empty()
            && !body.contains.is_empty()
            && body.contains.iter().all(|child| {
                matches!(child, ResourceClause::Declared { name, .. } if name != "authority")
            })
    }

    fn apply_execution_population_member_exchange(
        &self,
        resource: &ResourceClause,
        source_resource: &ResourceClause,
        produce: bool,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let declared = match resource {
            ResourceClause::Declared { name, .. } => name,
            ResourceClause::Quantified { resource, .. } => match resource.as_ref() {
                ResourceClause::Declared { name, .. } => name,
                _ => {
                    return Err(self.step_error("member changes require a declared resource"));
                }
            },
            _ => {
                return Err(self.step_error("member changes require a declared resource"));
            }
        };
        let name = declared;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("population member change requires a C execution proof"));
        };
        let definition = context
            .resource_environment
            .get(name)
            .ok_or_else(|| self.step_error(format!("unknown resource `{name}`")))?;
        let Some(body) = definition.composite_body() else {
            return Err(self.step_error(format!(
                "`{name}` is abstract; its members require an ordinary producing contract"
            )));
        };
        let contains_nonprivate_resource = body.contains.iter().any(|clause| {
            !matches!(clause, ResourceClause::OwnMemory(_))
                && !matches!(clause, ResourceClause::Declared { name, .. } if name != "authority")
        });
        if !definition.resource_parameters().is_empty()
            || !definition.fields().is_empty()
            || !body.children.is_empty()
            || body.matched.is_some()
            || body.condition.is_some()
            || contains_nonprivate_resource
            || !body.witnesses.is_empty()
        {
            return Err(self.step_error(format!(
                "member fold/unfold of `{name}` requires a private body of owned memory or declared resources"
            )));
        }
        self.require_execution_frontier("population member change")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("population member change lost its C state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("population member change must precede function exit"));
        }
        let before_facts = self.facts().clone();
        let selected = lower_resource_clause_at_state(
            resource,
            context.parameter_binding(),
            &execution.core.state,
        )?;
        let compiled_definition = context
            .function
            .composite_resource_definition(name)
            .ok_or_else(|| self.step_error(format!("unknown compiled resource `{name}`")))?;
        let (after_state, witness) = execution
            .core
            .state
            .checked_population_member_exchange(
                &selected,
                produce,
                compiled_definition,
                before_facts.assumptions(),
            )
            .map_err(|message| {
                if let Some(index) = message
                    .strip_prefix("Requires member body fact #")
                    .and_then(|index| index.parse::<usize>().ok())
                    && let Some(fact) = body.facts.get(index)
                {
                    let fact = resource_argument_substitutions(
                        definition,
                        source_resource,
                        context.claim_label,
                        context.tactic_index,
                    )
                    .ok()
                    .and_then(|substitutions| {
                        substitute_click_proposition(fact, &substitutions).ok()
                    });
                    if let Some(fact) = fact {
                        return self
                            .step_error(format!("Requires {}", describe_click_proposition(&fact)));
                    }
                }

                if produce && message.contains("Requires the private body") {
                    let missing = resource_argument_substitutions(
                        definition,
                        resource,
                        context.claim_label,
                        context.tactic_index,
                    )
                    .ok()
                    .and_then(|substitutions| {
                        body.contains.iter().find_map(|clause| {
                            let clause =
                                instantiate_resource_clause(clause, &substitutions).ok()?;
                            let fact = lower_resource_clause_at_state(
                                &clause,
                                context.parameter_binding(),
                                &execution.core.state,
                            )
                            .ok()?;
                            (!execution
                                .core
                                .state
                                .resources()
                                .satisfies_fact(&fact, before_facts.assumptions()))
                            .then(|| describe_resource_clause(&clause))
                        })
                    });
                    if let Some(missing) = missing {
                        return self
                            .step_error(format!("{message}; missing resource fact `{missing}`"));
                    }
                }
                self.step_error(message)
            })?;
        let added_facts = if !produce && !compiled_definition.facts().is_empty() {
            let instantiated = crate::kernel::instantiate_private_member_body_facts(
                &selected,
                compiled_definition,
                &execution.core.state,
                before_facts.assumptions(),
            )
            .ok_or_else(|| {
                self.step_error("Requires ownership of every cell read by member body facts")
            })?;
            // Keep the written arguments with the facts this operation
            // introduces. Resolved pointer values are checking operands, not
            // source spellings for a later quantified instantiation.
            let substitutions = resource_argument_substitutions(
                definition,
                source_resource,
                context.claim_label,
                context.tactic_index,
            )?;
            for (index, kernel) in &instantiated.declared {
                let surface = substitute_click_proposition(&body.facts[*index], &substitutions)
                    .map_err(|message| self.step_error(message))?;
                execution
                    .presentation
                    .surface_propositions
                    .record_lowering(&surface, kernel)?;
            }
            instantiated.propositions
        } else {
            Vec::new()
        };
        let mut after_facts = before_facts.clone();
        for fact in &added_facts {
            after_facts = after_facts.with_kernel_checked_fact(fact.clone());
        }
        let entry_successor = execution
            .core
            .record_population_member_rewrite(
                context.function,
                context.arguments,
                &before_facts,
                &selected,
                produce,
                &witness,
                &after_state,
                &after_facts,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "kernel rejected checked population member change: {message}"
                ))
            })?;
        execution.core.state = entry_successor.unwrap_or(after_state).into();
        let branch = self
            .focused_branch()
            .expect("population member change requires an open goal")
            .with_state(BranchState {
                facts: after_facts,
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: added_facts.clone(),
            checked_facts: added_facts,
        })
    }

    pub(super) fn apply_release_view(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("release_view requires an execution proof"));
        };
        self.require_execution_frontier("release_view")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("release_view requires a running state"))?;
        let facts = self.facts().clone();
        let ResourceClause::ViewMemory(segment) = resource else {
            return Err(self.step_error("release_view requires one memory view"));
        };
        let mut segment = segment.clone();
        if let ProgramExpression::Variable(name) = &mut segment.base {
            *name = execution
                .core
                .reached_state()
                .locals()
                .resolve_binding(name);
        }
        let element_width =
            crate::surface::lowering::contract_segment_element_width_with_pointer_types(
                context.parameter_binding().parameters,
                &segment,
                None,
                None,
            );
        let selected = crate::kernel::MemorySegment::new(segment.base, segment.start, segment.end)
            .with_element_width(element_width);
        let successor = execution
            .core
            .record_view_release(&selected, facts.assumptions())
            .map_err(|error| {
                self.step_error(format!(
                    "cannot release `{}`. {error}",
                    crate::surface::validation::describe_resource_clause(resource),
                ))
            })?;
        execution.core.state = successor.into();
        let branch = self
            .focused_branch()
            .ok_or_else(|| self.step_error("release_view requires an open goal"))?
            .with_state(BranchState {
                facts,
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: Vec::new(),
            checked_facts: Vec::new(),
        })
    }

    fn apply_execution_population_authority_exchange(
        &self,
        resource: &ResourceClause,
        establish: bool,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let operation = if establish { "fold" } else { "unfold" };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(format!(
                "population authority `{operation}` requires a C execution proof"
            )));
        };
        self.require_execution_frontier("population authority exchange")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("population authority exchange lost its C state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error(format!(
                "population authority `{operation}` must run before function exit"
            )));
        }
        let before_facts = self.facts().clone();
        let selected = lower_resource_clause_at_state(
            resource,
            context.parameter_binding(),
            execution.core.reached_state(),
        )?;
        let after_state = execution
            .core
            .record_population_authority_rewrite(&before_facts, &selected, establish)
            .map_err(|message| self.step_error(message))?;
        execution.core.state = after_state.into();
        let branch = self
            .focused_branch()
            .expect("population authority exchange requires an open goal")
            .with_state(BranchState {
                facts: before_facts,
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: Vec::new(),
            checked_facts: Vec::new(),
        })
    }

    pub(super) fn apply_instance_rewrite(
        &self,
        binding: &ResourceInstanceBinding,
        resource: &ResourceClause,
        unfold: bool,
        saved_instance: Option<&crate::kernel::ResourceInstance>,
        witness_names: &[(String, String)],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if let ResourceClause::Named { resource, .. } = resource
            && let ResourceClause::Declared { name, .. } = resource.as_ref()
            && matches!(name.as_str(), "mutex_live" | "mutex_guard" | "mutex_use")
        {
            let operation = if unfold { "unfold" } else { "fold" };
            return Err(self.step_error(format!("`{name}` has no resource body to {operation}")));
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("instance fold/unfold requires a C execution proof"));
        };
        if let ResourceClause::Named { resource, .. } = resource
            && let ResourceClause::Declared { name, .. } = resource.as_ref()
            && context
                .resource_environment
                .get(name)
                .is_some_and(ResourceDefinition::is_sealed)
        {
            let operation = if unfold { "unfold" } else { "fold" };
            return Err(self.step_error(format!(
                "`{name}` is an abstract resource: it has no body, so no proof can {operation} \
                 it; only contracts produce and consume its instances"
            )));
        }
        let branch = self
            .focused_branch()
            .ok_or_else(|| self.step_error("instance rewrite requires an open goal"))?;
        let mut execution = branch
            .state
            .execution
            .as_deref()
            .cloned()
            .ok_or_else(|| self.step_error("instance rewrite has no execution state"))?;
        let outcome = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => Some(goal),
            _ => {
                self.require_execution_frontier("instance fold/unfold")?;
                None
            }
        };
        let before: &ExecutionState =
            outcome.map_or(&*execution.core.state, |goal| &*goal.data.core.state);
        let pre_state = context.old_reference_state(&execution.core.frontier, before);
        let constructed;
        let instance = if let Some(instance) = saved_instance {
            instance
        } else if let Some(fields) = &binding.fold_fields {
            if unfold || !binding.children.is_empty() {
                return Err(self.step_error("explicit fields require a fold construction"));
            }
            let ResourceClause::Named { resource, .. } = resource else {
                unreachable!()
            };
            // A proof `match` arm's bindings are proof locals, not C locals:
            // the fields below substitute them, and so do the resource's own
            // arguments, so `fold(cell_at(id), ...)` names the pointer a
            // `have` goal raising `id` does.
            let resource = &self.substitute_fixed_state_locals_in_resource_arguments(resource)?;
            let lowered = lower_resource_clause_at_current_locals_with_entry_and_assumptions(
                resource,
                context.parameter_binding(),
                pre_state,
                before,
                outcome
                    .map(|goal| goal.data.core.result.native())
                    .as_deref(),
                self.facts().assumptions(),
            )?;
            let ResourceFact::Own(Resource::Composite { name, arguments }, _) = lowered else {
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
            let values = parameter_values(context.parameter_binding())?;
            let array_refs = array_refs_for_parameters(
                context.parsed_function.parameters(),
                &values,
                &before.program_point(),
            );
            let (values, array_refs) = contract_environment_at_state(&values, &array_refs, before);
            let mut proposed = Vec::new();
            for (name, ty) in schema.fields() {
                let expression = supplied
                    .get(name.as_str())
                    .ok_or_else(|| self.step_error(format!("missing fold field `{name}`")))?;
                let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
                let (value, obligations) = capture_resource_field_initializer(
                    &expression,
                    ty,
                    self.facts().assumptions(),
                    ContractEnvironment::new(&values, &array_refs)
                        .with_parameters(context.parameter_binding()),
                    pre_state,
                    before,
                    None,
                    &execution.presentation.recorded_states,
                    context.spec_definitions,
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
                            context.parameter_binding(),
                        )
                        .unwrap_or(message);
                    self.step_error(format!("fold field `{name}`: {message}"))
                })?;
                for obligation in obligations {
                    crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                        self.step_error(format!(
                            "fold field `{name}` has an unproved evaluation obligation"
                        ))
                        .with_unresolved_requirement(&obligation),
                    )?;
                }
                proposed.push(value);
            }
            let identity = pre_state
                .owned_resource_instance(binding.instance()?)
                .map_or(binding.instance()?, |instance| instance.identity());
            constructed = crate::kernel::ResourceInstance::new_with_resource_arguments(
                identity,
                name,
                arguments,
                schema.clone(),
                proposed.into(),
                crate::surface::lowering::lower_resource_reference_arguments(resource, before)?,
            )
            .ok_or_else(|| self.step_error("invalid fold fields"))?;
            &constructed
        } else {
            before
                .resource_instance_at_path(binding.instance()?, &binding.children)
                .or_else(|| {
                    if !unfold {
                        before
                            .opened_resource_at_path(
                                binding.identity.instance()?,
                                &binding.children,
                            )
                            .or_else(|| {
                                binding
                                    .children
                                    .is_empty()
                                    .then(|| {
                                        pre_state
                                            .owned_resource_instance(binding.identity.instance()?)
                                    })
                                    .flatten()
                            })
                    } else {
                        None
                    }
                })
                .ok_or_else(|| {
                    self.step_error(
                        "resource instance is not owned here or has no retained fold template",
                    )
                })?
        };
        let definition = context
            .function
            .composite_resource_definition(instance.name())
            .ok_or_else(|| self.step_error("resource instance has no registered body"))?;
        // `let { field: name } = unfold(instance)` names the folded value of a
        // scalar field, as a matched constructor payload names its value. The
        // instance is consumed by this unfold, so the binder is the only
        // spelling of that value for the rest of the proof.
        let mut locals = if unfold {
            self.bind_unfolded_instance_fields(binding, instance, &execution)?
        } else {
            self.state().locals().clone()
        };
        let selected_children = (unfold || binding.fold_fields.is_some())
            .then_some(binding.child_bindings.as_ref())
            .flatten()
            .map(|children| {
                children
                    .iter()
                    .filter(|(slot, _, _)| {
                        !unfold
                            || !instance
                                .schema()
                                .fields()
                                .iter()
                                .any(|(field, _)| field == slot)
                    })
                    .map(|(slot, name, identity)| {
                        let identity = if unfold {
                            crate::kernel::model_fields::register_instance_spelling(
                                *identity, name,
                            );
                            *identity
                        } else {
                            let path = name
                                .split('.')
                                .skip(1)
                                .map(str::to_owned)
                                .collect::<Vec<_>>();
                            before
                                .resource_instance_at_path(*identity, &path)
                                .ok_or_else(|| {
                                    self.step_error(format!(
                                        "child `{name}` is not owned in folded form"
                                    ))
                                })?
                                .identity()
                        };
                        Ok((slot.clone(), identity))
                    })
                    .collect::<Result<Arc<[(String, InstanceId)]>, ClickError>>()
            })
            .transpose()?;
        let instance_value = instance.clone();
        let instance = &instance_value;
        let collecting =
            !unfold && crate::surface::proof::execution_planning::collecting_step_requirements();
        let assumptions = if collecting {
            self.facts()
                .assumptions()
                .clone()
                .retaining_required_obligations()
        } else {
            self.facts().assumptions().clone()
        };
        let (rewrite, facts) = if let Some(goal) = outcome {
            execution
                .core
                .rewrite_return_resource_instance_with_children_under(
                    context.function,
                    goal.path_index,
                    self.facts(),
                    instance,
                    unfold,
                    selected_children.clone(),
                    &assumptions,
                )
                .map_err(InstanceUnfoldError::Construction)
        } else if !unfold {
            execution
                .core
                .fold_resource_instance_with_children_under(
                    context.function,
                    context.arguments,
                    self.facts(),
                    instance,
                    selected_children.clone(),
                    &assumptions,
                )
                .map_err(InstanceUnfoldError::Construction)
        } else {
            execution.core.unfold_resource_instance_with_children(
                context.function,
                context.arguments,
                self.facts(),
                instance,
                selected_children.clone(),
                execution.presentation.refuting_exit_match_arm,
                |rewrite, facts| {
                    // Use the opening delta to name exposed cells. Later
                    // body facts must not rename a cell after publication.
                    let naming_assumptions = rewrite.naming_facts.iter().cloned().fold(
                        self.facts().assumptions().clone(),
                        PureFactContext::assume_proposition,
                    );
                    crate::surface::proof::resources::materialize_unfolded_instance_arm_cells(
                        context.resource_environment,
                        context.spec_definitions,
                        context.parameter_binding(),
                        rewrite.state.clone(),
                        instance,
                        facts.assumptions(),
                        &naming_assumptions,
                        rewrite.body_active,
                    )
                },
            )
        }
        .map_err(|error| {
            let refusal = match error {
                InstanceUnfoldError::Construction(refusal) => refusal,
                InstanceUnfoldError::Recording(error) => {
                    return self.step_error_resource_rewrite(error);
                }
            };
            let comparison = if crate::surface::proof_trace::enabled_for(self.claim_label()) {
                crate::surface::proof_trace::ChildArgumentTrace::from_refusal(
                    &refusal,
                    self.facts().assumptions(),
                )
                .map(|mut comparison| {
                    comparison.name_values(|left, right| self.trace_pointer_pair(left, right));
                    comparison
                })
            } else {
                None
            };
            let declaration = match &refusal {
                // The kernel names the fact as its declaration spells it, in
                // the kernel's own fact order; the surface body's list can
                // hold the facts in another order.
                crate::kernel::ResourceRewriteRefusal::BodyFactNotEstablished {
                    spelling: Some(spelling),
                    ..
                } => Some(spelling.clone()),
                crate::kernel::ResourceRewriteRefusal::BodyFactNotEstablished {
                    arm,
                    index,
                    ..
                }
                | crate::kernel::ResourceRewriteRefusal::BodyFactPrerequisiteNotEstablished {
                    arm,
                    index,
                    ..
                } => context
                    .resource_environment
                    .get(instance.name())
                    .and_then(|definition| {
                        let source = match arm {
                            None => definition.composite_body()?.facts().get(*index).cloned(),
                            Some(variant) => crate::surface::validation::resource_match_arm_scopes(
                                definition,
                                |name| {
                                    context
                                        .spec_definitions
                                        .functions
                                        .algebraic_type_definitions
                                        .get(name)
                                },
                                |name| context.resource_environment.get(name),
                            )
                            .ok()?
                            .into_iter()
                            .find(|(name, _, _)| name == variant)
                            .and_then(|(_, _, arm)| {
                                arm.composite_body()?.facts().get(*index).cloned()
                            }),
                        }?;
                        Some(crate::surface::printing::authored_click_proposition(
                            &source,
                        ))
                    }),
                _ => None,
            };
            // The kernel spells only an unmatched body's facts; an arm's fact
            // is named here as its declaration writes it, so the summary says
            // which fact failed rather than only its position.
            let mut summary = refusal.describe();
            if let (
                crate::kernel::ResourceRewriteRefusal::BodyFactNotEstablished {
                    spelling: None,
                    ..
                },
                Some(declaration),
            ) = (&refusal, &declaration)
            {
                summary.push_str(&format!(": `{declaration}`"));
            }
            // The instantiated fact the fold could not establish is the
            // refused step's goal, reported on the standard `goal:` line.
            let requirement = match &refusal {
                crate::kernel::ResourceRewriteRefusal::ChildArgumentNotEstablished {
                    actual,
                    required,
                    ..
                } => {
                    let term = |value: &AlgebraicValue| match value {
                        AlgebraicValue::Program(value) => Term::ProgramValue(value.clone().into()),
                        AlgebraicValue::Integer(value) => Term::Integer(value.clone().into()),
                        AlgebraicValue::Algebraic(value) => Term::Algebraic(value.clone().into()),
                    };
                    Some((
                        "goal",
                        Box::new(Proposition::Equal(term(actual), term(required))),
                        None,
                    ))
                }
                crate::kernel::ResourceRewriteRefusal::BodyFactNotEstablished {
                    proposition,
                    ..
                }
                | crate::kernel::ResourceRewriteRefusal::BodyFactPrerequisiteNotEstablished {
                    proposition,
                    ..
                } => Some(("goal", proposition.clone(), declaration)),
                _ => None,
            };
            // A fold of a resource that declares no field proposes the
            // hidden record its body facts read; the refusal shows it.
            let proposed = (!unfold
                && instance
                    .schema()
                    .fields()
                    .iter()
                    .all(|(name, _)| name.contains('.')))
            .then(|| Arc::new(instance.clone()));
            let error =
                self.step_error_with_proposed_record(summary, comparison, requirement, proposed);
            match &refusal {
                crate::kernel::ResourceRewriteRefusal::BodyResourceMissing(resource) => {
                    error.with_missing_resource(resource)
                }
                _ => error,
            }
        })?;
        if collecting {
            // Explicit constructors already provide the source of their
            // arguments and fields. Pair body clauses by the producer's
            // ordinal, rather than reconstructing those values from state.
            let mut written = BTreeMap::new();
            let source_body = if let (Some(fields), ResourceClause::Named { resource, .. }) =
                (&binding.fold_fields, resource)
                && let ResourceClause::Declared {
                    name, arguments, ..
                } = resource.as_ref()
                && let Some(source_definition) = context.resource_environment.get(name)
                && let Some(body) = source_definition.composite_body()
            {
                written.extend(source_definition.parameters().iter().zip(arguments).map(
                    |(parameter, argument)| {
                        // The application gives its argument a machine
                        // type. Keep it when the body fact moves the
                        // argument into an Integer arithmetic context.
                        let argument = if crate::surface::parser::has_arithmetic_spine(argument)
                            && crate::surface::lowering::pure_function_parameter_scalar_type(
                                parameter,
                            )
                            .is_some()
                        {
                            crate::surface::lowering::pure_function_parameter_argument(
                                parameter, argument,
                            )
                        } else {
                            argument.clone()
                        };
                        (parameter.name().to_owned(), argument)
                    },
                ));
                written.extend(fields.iter().cloned());
                // A field supplies the type of a contextual literal.
                // Preserve that type when the initializer is substituted
                // into an independently written obligation.
                for field in source_definition.fields() {
                    if *field.click_type() == ClickType::Integer
                        && let Some(value) = written.get_mut(field.name())
                    {
                        *value = SyntaxTerm::IntegerContext(Box::new(value.clone()));
                    } else if let Some(value) = written.get_mut(field.name()) {
                        // The kernel evaluates the initializer at the field's
                        // declared type. Keep that same conversion in the
                        // independently printed prerequisite: n + 1 for an
                        // int32 field must not become Integer arithmetic.
                        *value = crate::surface::lowering::pure_function_parameter_argument(
                            &FunctionParameter {
                                name: field.name().to_owned(),
                                click_type: field.click_type().clone(),
                                struct_name: None,
                                function_pointer_signature: None,
                                constant: false,
                                pointee_constant: false,
                                reference: false,
                            },
                            value,
                        );
                    }
                }
                match &body.matched {
                    None => Some(context.resource_environment.fold_source(name)?.body.clone()),
                    Some(matched) => match written.get(&matched.field) {
                        Some(SyntaxTerm::AlgebraicConstructor {
                            variant, arguments, ..
                        }) => {
                            let (bindings, arm) = context
                                .resource_environment
                                .fold_source(name)?
                                .arms
                                .get(variant)
                                .ok_or_else(|| {
                                    self.step_error("fold constructor has no source arm")
                                })?;
                            let arguments = arguments.clone();
                            // Constructor fields have their declared types,
                            // including the implicit object-pointer coercion
                            // of a void* field. Preserve that conversion in
                            // the source obligation just as constructor
                            // lowering does in the kernel term.
                            written.extend(bindings.iter().cloned().zip(arguments).map(
                                |((name, click_type), argument)| {
                                    let value = if click_type == ClickType::Integer {
                                        SyntaxTerm::IntegerContext(Box::new(argument))
                                    } else {
                                        crate::surface::lowering::pure_function_parameter_argument(
                                            &FunctionParameter {
                                                name: name.clone(),
                                                click_type,
                                                struct_name: None,
                                                function_pointer_signature: None,
                                                constant: false,
                                                pointee_constant: false,
                                                reference: false,
                                            },
                                            &argument,
                                        )
                                    };
                                    (name, value)
                                },
                            ));
                            Some(arm.clone())
                        }
                        _ => None,
                    },
                }
            } else {
                None
            };
            let selected_by_name = selected_children
                .as_deref()
                .unwrap_or(&[])
                .iter()
                .cloned()
                .collect::<BTreeMap<_, _>>();
            let mut child_renames = BTreeMap::new();
            if let Some(body) = source_body.as_ref() {
                let children = body
                    .children
                    .iter()
                    .map(|child| (&child.name, child.identity))
                    .chain(body.contains().iter().filter_map(|clause| {
                        if let ResourceClause::Named { binding, .. } = clause {
                            Some((&binding.name, binding.identity.instance()?))
                        } else {
                            None
                        }
                    }));
                for (child_name, child_identity) in children {
                    let actual = selected_by_name.get(child_name).ok_or_else(|| {
                        self.step_error("fold body child has no selected instance")
                    })?;
                    let name =
                        crate::kernel::model_fields::registered_instance_spelling(*actual)
                            .ok_or_else(|| self.step_error("fold body child has no source name"))?;
                    child_renames.insert(
                        child_name.clone(),
                        crate::surface::lowering::InstanceRename {
                            name: name.to_string(),
                            identity: child_identity.into(),
                            target_identity: Some(*actual),
                        },
                    );
                }
            }
            for clause in &rewrite.body_clauses {
                let declared = context.resource_environment.fold_source(instance.name())?;
                let body = match &clause.arm {
                    None => &declared.body,
                    Some(arm) => {
                        &declared
                            .arms
                            .get(arm)
                            .ok_or_else(|| self.step_error("fold body clause lost its source arm"))?
                            .1
                    }
                };
                let ordinal = if clause.arm.is_none() {
                    definition
                        .fact_source_index(clause.ordinal)
                        .ok_or_else(|| self.step_error("fold body clause lost its source index"))?
                } else {
                    clause.ordinal
                };
                let declared_fact = body
                    .facts()
                    .get(ordinal)
                    .ok_or_else(|| self.step_error("fold body clause lost its source ordinal"))?;
                let summary = crate::kernel::ResourceRewriteRefusal::BodyFactNotEstablished {
                    arm: clause.arm.clone(),
                    index: ordinal,
                    count: body.facts().len(),
                    spelling: Some(crate::surface::printing::authored_click_proposition(
                        declared_fact,
                    )),
                    proposition: Box::new(clause.proposition.clone()),
                }
                .describe();
                let mut refusal =
                    ClickError::new(summary).with_unresolved_requirement(&clause.obligation());
                if let Some(body) = source_body.as_ref() {
                    let source_ordinal = if clause.arm.is_none() {
                        definition
                            .fact_source_index(clause.ordinal)
                            .ok_or_else(|| {
                                self.step_error("fold body clause lost its source index")
                            })?
                    } else {
                        clause.ordinal
                    };
                    let source = body.facts().get(source_ordinal).ok_or_else(|| {
                        self.step_error("fold body clause lost its source ordinal")
                    })?;
                    let source = crate::surface::lowering::substitute_click_proposition_in(
                        source,
                        &crate::surface::lowering::ContractSubstitutions::for_fold_body(
                            &written,
                            &child_renames,
                        ),
                    )
                    .map_err(ClickError::new)?;
                    std::sync::Arc::make_mut(
                        refusal
                            .unresolved_requirement
                            .as_mut()
                            .expect("just attached"),
                    )
                    .surface = Some(source);
                }
                crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                    refusal,
                )?;
            }
        }
        if !witness_names.is_empty() {
            self.bind_unfold_witness_outputs(
                &mut locals,
                outcome.map_or(&*execution.core.state, |goal| &*goal.data.core.state),
                witness_names,
                definition
                    .witnesses()
                    .iter()
                    .map(|witness| witness.name())
                    .zip(&rewrite.witness_values),
            )?;
        }
        if unfold
            && let Some(crate::kernel::InstanceConsumption::Opened { children, .. }) = rewrite
                .state
                .resources()
                .instance_consumption(instance.identity())
        {
            let parent = crate::surface::printing::format_resource_call(resource);
            let aliases = selected_children
                .as_deref()
                .unwrap_or(&[])
                .iter()
                .map(|(slot, _)| slot.as_str())
                .collect::<BTreeSet<_>>();
            for (slot, identity) in children.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if !aliases.contains(slot.as_str()) {
                    crate::kernel::model_fields::register_instance_spelling(
                        *identity,
                        &format!("{parent}.{slot}"),
                    );
                }
            }
        }
        crate::kernel::model_fields::register_instance_spelling(instance.identity(), &binding.name);
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
                context.spec_definitions.functions,
                instance,
                &rewrite.body_clauses,
                &parameter_values(context.parameter_binding())?,
                in_scope,
            )?
        } else {
            Vec::new()
        };
        let after = rewrite.state;
        let added = rewrite.semantic_facts;
        // The kernel producer pairs these checked clauses with the facts it
        // introduced. Consume that result directly; comparing the freshly
        // produced facts again would reject equivalent retained carriers.
        for clause in clause_presentations {
            // Keep the producer's paired declaration spelling in the exact
            // source index as well as its binder metadata. A later fold can
            // state this obligation without recovering proof-local names.
            execution
                .presentation
                .surface_propositions
                .record_lowering(&clause.source, &clause.checked.proposition)?;
            execution.presentation.resource_body_clauses.push(clause);
        }
        let updated_branch = if let Some(goal) = outcome {
            execution.core.state = after.clone().into();
            let mut updated = goal.clone();
            let mut data = (*goal.data).clone();
            data.core.state = after.into();
            updated.data = Arc::new(data);
            OpenBranch::function_outcome(
                updated,
                BranchState {
                    facts,
                    execution: Some(Arc::new(execution)),
                },
            )
        } else {
            execution.core.state = after.into();
            branch.with_state(BranchState {
                facts,
                execution: Some(Arc::new(execution)),
            })
        };
        Ok(CheckedFocusedTransition {
            locals,
            branch: Some(updated_branch),
            added_facts: added.clone(),
            checked_facts: added,
        })
    }

    /// Select and open the exact written instance, retaining the template
    /// needed to restore its identity and fields at scope exit.
    pub(super) fn open_named_instance(
        &self,
        resource: &ResourceClause,
        state: &ExecutionState,
    ) -> Result<(CheckedFocusedTransition, OpenResourceRestoration), ClickError> {
        let ResourceClause::Named {
            binding,
            resource: definition,
        } = resource
        else {
            return Err(self.step_error("`with` after function exit requires a named resource"));
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("a named resource scope requires an execution proof");
        };
        if let ResourceClause::Declared { name, .. } = definition.as_ref()
            && context
                .resource_environment
                .get(name)
                .is_some_and(ResourceDefinition::is_authorized)
        {
            return Err(self
                .step_error("`with` on a named instance requires an ordinary composite resource"));
        }
        let instance = state
            .resource_instance_at_path(binding.instance()?, &binding.children)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`with` requires a held instance `{}`",
                    binding.name
                ))
            })?;
        let transition =
            self.apply_instance_rewrite(binding, resource, true, Some(instance), &[])?;
        Ok((
            transition,
            OpenResourceRestoration::Named(Arc::new(instance.clone())),
        ))
    }

    pub(in crate::surface::proof) fn open_outcome_resource_scope(
        &self,
        resource: &ResourceClause,
    ) -> Result<(Self, OpenResourceRestoration), ClickError> {
        let outcome = self.focused_outcome_data().ok_or_else(|| {
            self.step_error("`with` after function exit requires a returned outcome")
        })?;
        let (transition, restoration) = self.open_named_instance(resource, &outcome.core.state)?;
        let opened = Self {
            state: self.publish_checked_transition(transition)?,
            ..self.clone()
        };
        Ok((opened, restoration))
    }

    /// Close an ordinary named scope using the instance selected at its entry.
    pub(in crate::surface::proof) fn restore_open_instance(
        &self,
        resource: &ResourceClause,
        instance: &crate::kernel::ResourceInstance,
    ) -> Result<Self, ClickError> {
        let ResourceClause::Named { binding, .. } = resource else {
            unreachable!("a named scope retains its written resource binding")
        };
        let transition =
            self.apply_instance_rewrite(binding, resource, false, Some(instance), &[])?;
        Ok(Self {
            state: self.publish_checked_transition(transition)?,
            ..self.clone()
        })
    }

    pub(in crate::surface::proof) fn holds_open_instance(
        &self,
        instance: &crate::kernel::ResourceInstance,
    ) -> Result<bool, ClickError> {
        let state = if let Some(outcome) = self.focused_outcome_data() {
            &outcome.core.state
        } else {
            let execution = self
                .branch_execution()
                .ok_or_else(|| self.step_error("with block lost its execution state"))?;
            &execution.core.state
        };
        Ok(state.resources().owned_instance(instance.identity()) == Some(instance))
    }

    /// Retain the explicit fold written at a returning scope arm's close.
    pub(in crate::surface::proof) fn apply_explicit_open_instance_fold(
        &self,
        resource: &ResourceClause,
        instance: &crate::kernel::ResourceInstance,
    ) -> Result<Self, ClickError> {
        let restored = self.restore_open_instance(resource, instance)?;
        Ok(Self {
            node: ProofNode::step_child(
                &self.node,
                self.focused_branch_id(),
                Arc::new(ProofStep::FoldResource(resource.clone())),
            ),
            ..restored
        })
    }

    /// The proof locals after `let { field: name, ... } = unfold(instance)`
    /// binds each named C-typed field of `instance` to its folded C value,
    /// which lowers exactly as a matched constructor payload does.
    fn bind_unfolded_instance_fields(
        &self,
        binding: &ResourceInstanceBinding,
        instance: &crate::kernel::ResourceInstance,
        execution: &ExecutionProofState,
    ) -> Result<ProofLocals, ClickError> {
        let mut locals = self.state().locals().clone();
        let Some(children) = binding.child_bindings.as_ref() else {
            return Ok(locals);
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(locals);
        };
        for (slot, name, _) in children.iter() {
            let Some(index) = instance
                .schema()
                .fields()
                .iter()
                .position(|(field, _)| field == slot)
            else {
                continue;
            };
            if name == "result"
                || locals.values.contains_key(name)
                || locals.integer_values.contains_key(name)
                || execution.core.state.locals().contains_name(name)
                || context
                    .parsed_function
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.name() == name)
            {
                return Err(
                    self.step_error(format!("unfold field binding `{name}` is already in scope"))
                );
            }
            match instance.fields().get(index).expect("checked field index") {
                crate::kernel::ResourceFieldValue::Program(value) => {
                    locals.set_values(locals.values.with_inserted(
                        name.clone(),
                        SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.clone())),
                    ));
                }
                // Declaration expansion admits only C-typed field binders.
                crate::kernel::ResourceFieldValue::Integer(_)
                | crate::kernel::ResourceFieldValue::Algebraic(_) => {
                    return Err(self.step_error(format!(
                        "field `{slot}` of `{}` is not C-typed; an unfold pattern binds only C scalar and pointer fields",
                        instance.name()
                    )));
                }
            }
        }
        Ok(locals)
    }

    pub(super) fn apply_function_unfold(
        &self,
        application: &ClickFunctionApplication,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        self.apply_function_unfold_at(application, None)
    }

    /// `unfold(f(args))`, or with `selector` `unfold(at(selector, f(args)))`:
    /// the defining equation of the application at that program point,
    /// `at(selector, f(args)) == at(selector, body)`.
    pub(super) fn apply_function_unfold_at(
        &self,
        application: &ClickFunctionApplication,
        selector: Option<&ProgramPointSelector>,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let definitions = match self.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions,
            ProofContext::FixedState(context) => context.spec_definitions,
            ProofContext::Execution(context) => context.spec_definitions,
        };
        if definitions.predicates.get(&application.name).is_some() {
            return self.apply_local_predicate_unfold(&SyntaxProposition::PredicateCall {
                name: application.name.clone(),
                arguments: application.arguments.clone(),
            });
        }
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
        let local_algebraic_values = |inherited: BTreeMap<String, SpecAlgebraicExpression>| {
            referenced_names
                .iter()
                .filter_map(|name| {
                    self.known_algebraic_value(name)
                        .or_else(|| inherited.get(name))
                        .cloned()
                        .map(|value| (name.clone(), value))
                })
                .collect::<BTreeMap<_, _>>()
        };
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                // The defining equation and refreshed goal share this scope.
                // Select only named locals, with lexical binders taking
                // precedence over a same-named theorem parameter.
                let mut integer_values = context.theorem_context.integer_values.clone();
                for name in &referenced_names {
                    if let Some(value) = self.local_integer_values().get(name) {
                        integer_values = integer_values.with_inserted(name.clone(), value.clone());
                    }
                }
                let state = ExecutionState::at_point(&context.theorem_context.point);
                self.apply_function_unfold_in_state(
                    application,
                    context.theorem_context.values.clone(),
                    context.theorem_context.array_refs.clone(),
                    local_algebraic_values(
                        self.structural_induction_setup()
                            .map(|setup| setup.algebraic_values.clone())
                            .unwrap_or_default(),
                    ),
                    &integer_values,
                    FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                    context.spec_definitions,
                    BTreeMap::new(),
                    selector,
                )
            }
            ProofContext::FixedState(context) => {
                let values = parameter_values(context.parameter_binding)?;
                let array_refs = array_refs_for_parameters(
                    context.parameter_binding.parameters,
                    &values,
                    &context.fixed_state.state.program_point(),
                );
                let (values, array_refs) =
                    contract_environment_at_state(&values, &array_refs, context.fixed_state.state);
                self.apply_function_unfold_in_state(
                    application,
                    values,
                    array_refs,
                    local_algebraic_values(BTreeMap::new()),
                    &self.local_integer_values(),
                    context.fixed_state,
                    context.spec_definitions,
                    crate::surface::lowering::parameter_pointer_element_widths(
                        context.parameter_binding.parameters,
                    ),
                    selector,
                )
            }
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                let values = parameter_values(view.parameter_binding)?;
                let array_refs = array_refs_for_parameters(
                    view.parameter_binding.parameters,
                    &values,
                    &view.fixed_state.state.program_point(),
                );
                let (values, array_refs) =
                    contract_environment_at_state(&values, &array_refs, view.fixed_state.state);
                self.apply_function_unfold_in_state(
                    application,
                    values,
                    array_refs,
                    local_algebraic_values(BTreeMap::new()),
                    &self.local_integer_values(),
                    view.fixed_state,
                    view.spec_definitions,
                    crate::surface::lowering::parameter_pointer_element_widths(
                        view.parameter_binding.parameters,
                    ),
                    selector,
                )
            }
            ProofContext::Execution(context) => {
                let execution = self.execution().ok_or_else(|| {
                    self.step_error("function `unfold` lost its semantic execution state")
                })?;
                let values = parameter_values(context.parameter_binding())?;
                let array_refs = array_refs_for_parameters(
                    context.parsed_function.parameters(),
                    &values,
                    &execution.core.state.program_point(),
                );
                let (values, array_refs) =
                    contract_environment_at_state(&values, &array_refs, &execution.core.state);
                let pre_state =
                    context.old_reference_state(&execution.core.frontier, &execution.core.state);
                self.apply_function_unfold_in_state(
                    application,
                    values,
                    array_refs,
                    local_algebraic_values(BTreeMap::new()),
                    &self.local_integer_values(),
                    FixedStateFrame::new(
                        pre_state,
                        &execution.core.state,
                        None,
                        &execution.presentation.recorded_states,
                    ),
                    context.spec_definitions,
                    crate::surface::lowering::parameter_pointer_element_widths(
                        context.parsed_function.parameters(),
                    ),
                    selector,
                )
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_function_unfold_in_state(
        &self,
        application: &ClickFunctionApplication,
        values: ProgramValueBindings,
        array_refs: ClickArrayRefs,
        algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
        integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
        fixed_state: FixedStateFrame<'_>,
        spec_definitions: SpecDefinitions<'_>,
        parameter_pointer_element_widths: BTreeMap<String, u32>,
        selector: Option<&ProgramPointSelector>,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        // Both sides of an equation at a program point are read there.
        let at_point = |expression: SyntaxTerm| match selector {
            Some(selector) => SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(expression),
            },
            None => expression,
        };
        let definition = spec_definitions
            .functions
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
        let Some(definition_body) = definition.body() else {
            return Err(self.step_error(format!(
                "`unfold` cannot open `{}`: it is a library primitive operation with no definition; cite its axioms instead",
                application.name
            )));
        };
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
            .map(|(parameter, argument)| {
                (
                    parameter.binding_name(),
                    crate::surface::lowering::pure_function_parameter_argument_of_type(
                        parameter,
                        argument,
                        generics::syntactic_expression_type(argument, &variable_types).as_ref(),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let checked_body = substitute_contract_expression(definition_body, &checked_substitutions)
            .map_err(|message| {
                self.step_error(format!(
                    "could not instantiate function `{}` for `unfold`: {message}",
                    application.name
                ))
            })?;
        let checked_body = match definition.return_type() {
            ClickType::Algebraic(_) => select_known_unfold_body(&checked_body)
                .map_err(|message| self.step_error(message))?,
            ClickType::Program(ty) if ty.to_kernel_type() == ProgramType::Int32 => {
                select_known_unfold_body(&checked_body)
                    .map_err(|message| self.step_error(message))?
            }
            _ => checked_body,
        };
        let checked_body =
            crate::surface::lowering::pure_function_result_value(&definition, checked_body);
        let checked_equality = SyntaxProposition::Comparison {
            left: at_point(SyntaxTerm::Call {
                name: application.name.clone(),
                arguments: checked_arguments.clone(),
            }),
            operator: ComparisonOperator::Equal,
            right: at_point(checked_body),
        };
        let equality = lower_fixed_state_proposition_through_kernel_with(
            &checked_equality,
            self.facts().assumptions(),
            ContractEnvironment::new(&values, &array_refs),
            fixed_state,
            spec_definitions,
            FixedStateLoweringOptions {
                algebraic_values: Some(&algebraic_values),
                integer_values: Some(integer_values),
                opaque_click_functions: Some(&BTreeSet::from([application.name.clone()])),
                pointer_element_widths: parameter_pointer_element_widths.clone(),
                ..Default::default()
            },
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not lower defining equation for `{}`: {message}",
                application.name
            ))
        })?;

        // A decided range exposes its empty or append equation over the
        // named function, with ordinary obligations for its guards.
        let fold_equation = if matches!(&equality, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::IntegerEqual(_, folded), _)) if (matches!(folded.as_ref(), IntegerTerm::RangeFold { .. }))))
            && !self.goal().is_some_and(|goal| {
                crate::kernel::proof::propositions_are_alpha_equal(goal, &equality)
            }) {
            self.derive_function_range_fold_equation(application, &definition, &equality)?
        } else {
            None
        };
        if let Some((derived, predecessor_equation)) = fold_equation {
            let mut facts = self.facts().clone();
            let mut added = Vec::new();
            // The fold law consumes these checked definition instances.
            // Keep them available too, so equivalent functions retain
            // their common body rather than becoming unrelated opaque
            // predecessor calls after unfolding.
            for definition_equation in std::iter::once(equality.clone()).chain(predecessor_equation)
            {
                if !facts.contains_top_level(&definition_equation) {
                    added.push(definition_equation.clone());
                }
                facts = facts.with_kernel_checked_fact(definition_equation);
            }
            if !facts.contains_top_level(&derived) {
                added.push(derived.clone());
            }
            facts = facts.with_kernel_checked_fact(derived.clone());
            let branch = match self.focused_obligation() {
                Some(Obligation::Proposition(goal)) => {
                    let Some((OldConditionTerm::IntegerEqual(unfolded, replacement), true)) =
                        derived.old_condition()
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
                        let lower = |candidate: &SyntaxProposition| {
                            let candidate = self
                                .substitute_fixed_state_locals_in_proposition(candidate)
                                .ok()?;
                            let mut opaque_calls = BTreeSet::new();
                            crate::surface::validation::collect_click_function_calls_in_proposition(
                                &candidate,
                                &mut opaque_calls,
                            );
                            lower_fixed_state_proposition_through_kernel_with(
                                &candidate,
                                facts.assumptions(),
                                ContractEnvironment::new(&values, &array_refs),
                                fixed_state,
                                spec_definitions,
                                FixedStateLoweringOptions {
                                    algebraic_values: Some(&algebraic_values),
                                    integer_values: Some(integer_values),
                                    opaque_click_functions: Some(&opaque_calls),
                                    pointer_element_widths: parameter_pointer_element_widths
                                        .clone(),
                                    ..Default::default()
                                },
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
                    Some(self.refined_proposition(
                        self.refined_branch_state(facts.clone()),
                        kernel,
                        surface,
                        false,
                    ))
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

        // Unfold constructed this equation under the pre-step facts. Retain
        // that completed judgment on its return path, so a later `have` or
        // resource fold does not treat the equation as an ambient assumption.
        // No checker runs again over the equation produced above.
        if let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() {
            let branch_state = &self.focused_branch().expect("focused branch exists").state;
            let root = KernelProofObject::root(
                self.state().locals().clone(),
                OpenBranch::surface_proposition_at_outcome(
                    branch_state.clone(),
                    goal.data.clone(),
                    equality,
                    checked_equality,
                ),
            );
            let completion = root
                .publish_checked_result(self.state().locals().clone(), None, Vec::new(), Vec::new())
                .map_err(|_| self.step_error("checked unfold lost its proposition judgment"))?
                .completed_proposition()
                .ok_or_else(|| self.step_error("checked unfold did not close its proposition"))?;
            let mut execution = branch_state
                .execution
                .as_ref()
                .ok_or_else(|| self.step_error("return unfold lost its execution evidence"))?
                .as_ref()
                .clone();
            execution
                .core
                .record_return_proposition(goal.path_index, completion, self.facts())
                .map_err(|message| self.step_error(message))?;
            let mut state = self.refined_branch_state(facts);
            state.execution = Some(Arc::new(execution));
            return Ok(CheckedFocusedTransition::replacing(
                self.state().locals().clone(),
                Some(OpenBranch::function_outcome(goal.clone(), state)),
                added_facts.clone(),
                added_facts,
            ));
        }

        let branch = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => {
                let mut original_surface = goal.surface.as_deref().cloned();
                let substitutions = definition
                    .parameters()
                    .iter()
                    .zip(application.arguments.iter().zip(&checked_arguments))
                    .map(|(parameter, (argument, checked_argument))| {
                        (
                            parameter.binding_name(),
                            crate::surface::lowering::pure_function_parameter_argument_of_type(
                                parameter,
                                argument,
                                generics::syntactic_expression_type(
                                    checked_argument,
                                    &variable_types,
                                )
                                .as_ref(),
                            ),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();
                let surface_body = substitute_contract_expression(definition_body, &substitutions)
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate surface function `{}` for `unfold`: {message}",
                            application.name
                        ))
                    })?;
                let surface_body = select_known_unfold_body(&surface_body)
                    .map_err(|message| self.step_error(message))?;
                let surface_body =
                    crate::surface::lowering::pure_function_result_value(&definition, surface_body);
                let surface_application = SyntaxTerm::Call {
                    name: application.name.clone(),
                    arguments: application.arguments.clone(),
                };
                let surface_equality = SyntaxProposition::Comparison {
                    left: at_point(surface_application),
                    operator: ComparisonOperator::Equal,
                    right: at_point(surface_body),
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
                    lower_fixed_state_proposition_through_kernel_with(
                        &checked_surface,
                        facts.assumptions(),
                        ContractEnvironment::new(&values, &array_refs),
                        fixed_state,
                        spec_definitions,
                        FixedStateLoweringOptions {
                            algebraic_values: Some(&algebraic_values),
                            integer_values: Some(integer_values),
                            opaque_click_functions: Some(&opaque_calls),
                            pointer_element_widths: parameter_pointer_element_widths,
                            ..Default::default()
                        },
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
                    match facts.check_equality_rewrite(goal.kernel(), &equality) {
                        Ok(rewritten) => {
                            original_surface = None;
                            rewritten.proposition().clone()
                        }
                        Err(_) => goal.kernel().clone(),
                    }
                };
                Some(self.refined_proposition(
                    self.refined_branch_state(facts.clone()),
                    kernel,
                    surface.or(original_surface),
                    false,
                ))
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

    /// State one fold equation over the selected call, exposing the chosen
    /// law's guards to the ordinary obligation driver. An undecided range
    /// retains its raw defining equation.
    fn derive_function_range_fold_equation(
        &self,
        application: &ClickFunctionApplication,
        definition: &ClickFunctionDefinition,
        equality: &Proposition,
    ) -> Result<Option<(Proposition, Option<Proposition>)>, ClickError> {
        let name = &application.name;
        let Some((OldConditionTerm::IntegerEqual(whole, folded), true)) = equality.old_condition()
        else {
            return Err(self.step_error(format!(
                "`unfold({name}(...))` applies to an `Integer`-valued pure function whose body is a range fold"
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
            return Ok(None);
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
        let empty_range = {
            let Proposition::Implies(guard, _) = empty.proposition() else {
                return Err(self.step_error("the Integer fold law must be guarded"));
            };
            let mut required = Vec::new();
            collect_conjunctive_premises(guard, &mut required);
            let Some(Proposition::ConditionIs(condition, expected)) =
                required.into_iter().find(|premise| *premise != equality)
            else {
                return Err(self.step_error("the empty fold law must have a range guard"));
            };
            match self.facts().assumptions().decide(condition.old_form()) {
                Some(value) => value == *expected,
                None => {
                    // A written predecessor guard also selects the append
                    // case. Inspect only that guard, without instantiating
                    // a body whose range case is still unknown.
                    let guard = crate::kernel::integer_range_fold_predecessor_guard(index)
                        .map(|condition| Proposition::condition_is(condition, true));
                    if !guard.as_ref().is_some_and(|guard| {
                        self.facts().listed_premise_available(guard, &[], false)
                    }) {
                        return Ok(None);
                    }
                    false
                }
            }
        };
        if empty_range {
            let Proposition::Implies(guard, conclusion) = empty.proposition() else {
                unreachable!("the selected empty law is guarded")
            };
            let mut required = Vec::new();
            collect_conjunctive_premises(guard, &mut required);
            for premise in required {
                if premise != equality {
                    self.require_function_fold_guard(premise)?;
                }
            }
            return Ok(Some((conclusion.as_ref().clone(), None)));
        }
        {
            // Folds that capture their end, or do not have an endpoint
            // parameter, still admit their ordinary defining equation. Check
            // this source shape explicitly; do not hide a failed kernel law.
            let fold_body = definition
                .body()
                .map(lambdas::reduce_head_fully)
                .transpose()
                .map_err(|message| self.step_error(message))?;
            let Some(SyntaxTerm::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            }) = fold_body.as_deref()
            else {
                return Ok(None);
            };
            let Some(end_parameter) = fold_end_parameter_binding(end) else {
                return Ok(None);
            };
            if [start.as_ref(), initial.as_ref(), body.as_ref()]
                .into_iter()
                .any(|part| contract_expression_reads_binding(part, &end_parameter))
            {
                return Ok(None);
            }
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
        let mut predecessor_equality = None;
        for premise in required {
            if premise == equality {
                continue;
            }
            if let Some((OldConditionTerm::IntegerEqual(left, right), true)) =
                (premise).old_condition()
                && left.as_ref() == &prior
                && matches!(right.as_ref(), IntegerTerm::RangeFold { .. })
            {
                predecessor_equality = Some(premise.clone());
                continue;
            }
            self.require_function_fold_guard(premise)?;
        }
        if predecessor_equality.is_none() {
            return Err(self.step_error(format!(
                "the Integer fold append law over `{name}` did not state its predecessor endpoint"
            )));
        }
        Ok(Some((
            append_conclusion.as_ref().clone(),
            predecessor_equality,
        )))
    }

    /// One explicit law guard, checked from its exact fact key or emitted
    /// as an ordinary obligation. No premise or state history is searched.
    fn require_function_fold_guard(&self, guard: &Proposition) -> Result<(), ClickError> {
        if self.facts().listed_premise_available(guard, &[], false) {
            return Ok(());
        }
        crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
            self.step_error("`unfold` has an unproved range-fold guard")
                .with_unresolved_requirement(
                    &crate::kernel::ProofObligation::verification_condition(guard.clone()),
                ),
        )
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
        let fold_body = definition
            .body()
            .map(lambdas::reduce_head_fully)
            .transpose()
            .map_err(|message| self.step_error(message))?;
        let Some(SyntaxTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        }) = fold_body.as_deref()
        else {
            return Err(self.step_error(format!(
                "`unfold({name}(...))` requires the body of `{name}` to be exactly a range fold"
            )));
        };
        let Some(end_parameter) = fold_end_parameter_binding(end) else {
            return Err(self.step_error(format!(
                "`unfold({name}(...))`: the append-last-cell equation restates the shorter fold as `{name}` at the predecessor endpoint, so the fold's end must be a parameter of `{name}`"
            )));
        };
        for (part, what) in [
            (start.as_ref(), "start"),
            (initial.as_ref(), "initial value"),
            (body.as_ref(), "body"),
        ] {
            if contract_expression_reads_binding(part, &end_parameter) {
                return Err(self.step_error(format!(
                    "`unfold({name}(...))`: the fold's {what} also reads `{end_parameter}`, so the shorter fold is not `{name}` at the predecessor endpoint"
                )));
            }
        }
        let position = definition
            .parameters()
            .iter()
            .position(|parameter| parameter.binding_name() == end_parameter)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`unfold({name}(...))`: `{end_parameter}` is not a parameter of `{name}`"
                ))
            })?;
        crate::kernel::integer_range_fold_predecessor_application(whole.as_ref(), position)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`unfold({name}(...))` requires the call to remain the opaque application `{name}(...)` with an `int32` or `uint64` argument for `{end_parameter}`"
                ))
            })
    }

    /// The Surface spelling of the goal `unfold(f(args))` just
    /// refreshed, or `None` when this step cannot write one down.
    ///
    /// The kernel goal was refreshed by substituting the restated fold law's
    /// conclusion, so its written form has to be rebuilt from the declaration.
    /// The law replaces `f(args)` by one of exactly two expressions: the fold's
    /// initial value over an empty range, or the fold's body at the predecessor
    /// endpoint accumulated onto `f(args)` at that endpoint. Both are candidate
    /// spellings only; the installed candidate lowers to the refreshed kernel
    /// proposition or the same normalized Integer claim, or to true when a
    /// premise-free Integer certificate checks the refreshed proposition.
    /// Later tactics still check that original kernel goal.
    fn refreshed_fold_law_surface_goal(
        &self,
        application: &ClickFunctionApplication,
        definition: &ClickFunctionDefinition,
        surface_goal: &SyntaxProposition,
        refreshed_kernel: &Proposition,
        lower: &dyn Fn(&SyntaxProposition) -> Option<Proposition>,
    ) -> Option<SyntaxProposition> {
        let fold_body = lambdas::reduce_head_fully(definition.body()?).ok()?;
        let SyntaxTerm::RangeFold {
            end,
            initial,
            accumulator,
            item,
            body,
            ..
        } = fold_body.as_ref()
        else {
            return None;
        };
        let substitutions = definition
            .parameters()
            .iter()
            .zip(&application.arguments)
            .map(|(parameter, argument)| {
                (
                    parameter.binding_name(),
                    crate::surface::lowering::pure_function_parameter_argument(parameter, argument),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let substitute = |expression: &SyntaxTerm| {
            substitute_contract_expression(expression, &substitutions).ok()
        };
        let whole = SyntaxTerm::Call {
            name: application.name.clone(),
            arguments: application.arguments.clone(),
        };
        let mut candidates = Vec::new();
        if let Some(initial) = substitute(initial) {
            candidates.push(initial);
        }
        if let Some(position) = fold_end_parameter_binding(end)
            .and_then(|end| {
                definition
                    .parameters()
                    .iter()
                    .position(|parameter| parameter.binding_name() == end)
            })
            .filter(|position| *position < application.arguments.len())
            && let Some(body) = substitute(body)
        {
            let predecessor_end = SyntaxTerm::Subtract(
                Box::new(application.arguments[position].clone()),
                Box::new(SyntaxTerm::IntegerLiteral("1".to_string())),
            );
            let mut arguments = application.arguments.clone();
            arguments[position] = predecessor_end.clone();
            let cell = BTreeMap::from([
                (
                    accumulator.clone(),
                    SyntaxTerm::Call {
                        name: application.name.clone(),
                        arguments,
                    },
                ),
                (
                    item.clone(),
                    crate::surface::lowering::pure_function_parameter_argument(
                        &definition.parameters()[position],
                        &predecessor_end,
                    ),
                ),
            ]);
            if let Ok(appended) = substitute_contract_expression(&body, &cell) {
                candidates.push(appended);
            }
        }
        for candidate in candidates {
            crate::instrumentation::record_deterministic_work(1);
            let equality = SyntaxProposition::Comparison {
                left: whole.clone(),
                operator: ComparisonOperator::Equal,
                // The call supplied its Integer carrier. Keep that carrier
                // when its replacement is a bare numeral, especially in an
                // order comparison after the last function call disappears.
                right: crate::surface::lowering::pure_function_result_value(definition, candidate),
            };
            let Some(rewritten) =
                rewrite_click_proposition_by_surface_equality(surface_goal, &equality)
            else {
                continue;
            };
            let lowered = lower(&rewritten);
            if lowered.as_ref() == Some(refreshed_kernel) {
                return Some(rewritten);
            }
            let checked_claim =
                crate::kernel::proof::integer_arithmetic::integer_affine_claim(refreshed_kernel);
            // Constant folding in a source subexpression can change the raw
            // term structure without changing its checked Integer claim.
            // These are the same normalized claims used by the kernel's
            // Integer certificate checker; no ambient premises participate.
            if let (Some(source_claim), Some(checked_claim)) = (
                lowered
                    .as_ref()
                    .and_then(crate::kernel::proof::integer_arithmetic::integer_affine_claim),
                checked_claim.as_ref(),
            ) && source_claim == *checked_claim
            {
                return Some(rewritten);
            }
            // After the last Integer application disappears, ordinary
            // expression lowering can reduce the written comparison to true
            // (e.g. `0 - 0 == 0`). The refreshed kernel goal still retains
            // the Integer subtraction. Keep that spelling only when a
            // premise-free checked Integer certificate proves the same truth;
            // this changes presentation, never the kernel obligation.
            if lowered
                == Some(Proposition::condition_is(
                    OldConditionTerm::Constant(true),
                    true,
                ))
                && let Some(claim) = checked_claim
                && claim.terms.is_empty()
                && match claim.relation {
                    crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::Equal => {
                        claim.constant == num_bigint::BigInt::from(0)
                    }
                    crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::LessEqual => {
                        claim.constant <= num_bigint::BigInt::from(0)
                    }
                }
            {
                return Some(rewritten);
            }
        }
        None
    }

    /// Unfolds `names` in a goal's surface form. A signed character
    /// parameter passed to a predicate's `uint8` bytes first takes its
    /// explicit byte view, as contract lowering and call steps give it: the
    /// goal's kernel instance already reads those bytes as `uint8`, and a
    /// textual substitution would read them through the parameter's signed
    /// type, so the unfolded goal would differ from the same instance's
    /// unfolding anywhere else.
    pub(in crate::surface::proof) fn unfold_goal_surface(
        &self,
        predicates: &PredicateEnvironment,
        surface: &SyntaxProposition,
        names: &[String],
    ) -> Result<SyntaxProposition, String> {
        let parameters = match self.context.as_ref() {
            ProofContext::FixedState(context) => Some(context.parameter_binding.parameters),
            ProofContext::Execution(context) => Some(context.parameter_binding().parameters),
            ProofContext::Pure(_) => None,
        };
        let elaborated = parameters.and_then(|parameters| {
            crate::surface::lowering::elaborate_character_byte_views(surface, predicates, &|name| {
                parameters
                    .iter()
                    .find(|parameter| parameter.name() == name)
                    .map(crate::languages::interface::ImportedParameter::interface_type)
            })
        });
        unfold_surface_predicates(predicates, elaborated.as_ref().unwrap_or(surface), names)
    }

    /// Apply one checked kernel step on
    /// iterated guarded ownership. The kernel performs the step from the
    /// running state; this reads only its operands.
    pub(super) fn apply_execution_iterated_step(
        &self,
        tactic: &IteratedTactic,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let name = tactic.name();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(format!("`{name}` requires an execution-frontier proof")));
        };
        self.require_execution_frontier(&format!("`{name}`"))?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error(format!(
                "`{name}` must run before execution reaches function exit"
            )));
        }
        let state = &*execution.core.state;
        let evaluate = |expression: &SyntaxTerm| {
            let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
            let names = contract_expression_referenced_names(&expression);
            let (values, array_refs) =
                contract_environment_for_names(context.parameter_binding(), &names, state)?;
            evaluate_fixed_state_expression_through_kernel(
                &expression,
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &array_refs)
                    .with_parameters(context.parameter_binding()),
                FixedStateFrame::new(
                    context.old_reference_state(&execution.core.frontier, state),
                    state,
                    None,
                    &execution.presentation.recorded_states,
                ),
                context.spec_definitions,
                &BTreeSet::new(),
            )
            .map_err(|message| self.step_error(format!("`{name}` operand: {message}")))
        };
        let (target, unfold) = match tactic {
            IteratedTactic::Unfold(target) => (target, true),
            IteratedTactic::Fold(target) => (target, false),
        };
        let selected = match &target.point {
            Some(point) => selected_program_state(
                point,
                context.old_reference_state(&execution.core.frontier, state),
                &execution.presentation.recorded_states,
            )
            .map_err(|message| self.step_error(message))?,
            None => state,
        };
        let template = iterated_template_for_resource(
            context.resource_environment,
            &target.resource,
            name,
            context.parameter_binding(),
            selected,
            context.claim_label,
            context.tactic_index,
            self.facts().assumptions(),
        )?;
        let step = if let Some(index) = &target.index {
            let ProgramValue::Int32(index) = evaluate(index)? else {
                return Err(self.step_error(format!("`{name}` slot index must be int32")));
            };
            if unfold {
                crate::kernel::IteratedStep::UnfoldSlot { template, index }
            } else {
                crate::kernel::IteratedStep::FoldSlot { template, index }
            }
        } else if unfold {
            crate::kernel::IteratedStep::UnfoldClause { template }
        } else {
            crate::kernel::IteratedStep::FoldClause { template }
        };
        let after = execution
            .core
            .record_iterated_step(self.facts(), step)
            .map_err(|message| {
                self.step_error(format!(
                    "`{}` refused: {message}",
                    crate::surface::printing::describe_iterated_tactic(tactic)
                ))
            })?;
        execution.core.state = after.into();
        let branch = self
            .focused_branch()
            .expect("an iterated ownership step requires an open goal")
            .with_state(BranchState {
                facts: self.facts().clone(),
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: Vec::new(),
            checked_facts: Vec::new(),
        })
    }

    pub(super) fn apply_resource_subject_observation(
        &self,
        resource: &ResourceSubject,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("observe_memory");
        let view = self.premise_fixed_state_view().ok_or_else(|| {
            self.step_error("memory observation requires a concrete program state")
        })?;
        // Capture the descriptor just as a Resource theorem argument does.
        // The evidence is for current access even when the operands are saved.
        let descriptor = SyntaxProposition::Contains {
            parent: resource.clone(),
            child: ResourceSubject::Emp,
        };
        let Proposition::ResourceContains { parent, .. } =
            self.lower_surface_proposition_direct(&descriptor, "observation operand")?
        else {
            return Err(self.step_error("observation operand has unresolved span requirements"));
        };
        match parent.as_ref() {
            crate::kernel::Resource::Memory(range) => self.record_memory_observation(
                view.fixed_state.state,
                range,
                SyntaxProposition::ResourceViewable {
                    resource: resource.clone(),
                },
            ),
            crate::kernel::Resource::Instance(instance) => self.apply_named_observation(instance),
            _ => Err(self.step_error("observe requires one memory range or named instance")),
        }
    }

    fn apply_memory_observation(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("observe_memory");
        let resource = self.resolve_proof_resource_arguments(resource)?;
        let view = self.premise_fixed_state_view().ok_or_else(|| {
            self.step_error("memory observation requires a concrete program state")
        })?;
        let required = lower_resource_clause_at_current_locals_with_entry_and_assumptions(
            &resource,
            view.parameter_binding,
            view.fixed_state.pre_state,
            view.fixed_state.state,
            view.fixed_state.native_result().as_deref(),
            self.facts().assumptions(),
        )?;
        let range = required
            .memory_range()
            .ok_or_else(|| self.step_error("memory observation requires one memory range"))?;
        let (ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment)) = resource
        else {
            unreachable!()
        };
        let surface = SyntaxProposition::Loadable { segment };
        self.record_memory_observation(view.fixed_state.state, range, surface)
    }

    fn record_memory_observation(
        &self,
        state: &ExecutionState,
        range: &crate::kernel::MemoryRange,
        surface: SyntaxProposition,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let theorem = crate::kernel::observe_memory_view(state, range).ok_or_else(|| {
            self.step_error(
                "observe requires the exact memory range to be held as a unit owner or view",
            )
        })?;
        let proposition = theorem.proposition().clone();
        let mut locals = self.state().locals().clone();
        locals
            .surface_facts
            .record_lowering(&surface, &proposition)?;
        let added = (!self.facts().contains_top_level(&proposition))
            .then(|| proposition.clone())
            .into_iter()
            .collect();
        let facts = self.facts().with_kernel_checked_fact(proposition.clone());
        let complete = self
            .goal()
            .is_some_and(|goal| facts.introduced_goal_available(goal));
        Ok(self.checked_fact_transition(locals, facts, complete, added, vec![proposition]))
    }

    fn apply_named_observation(
        &self,
        instance: &crate::kernel::ResourceInstance,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(
                self.step_error("observing an instance requires an execution-frontier proof")
            );
        };
        self.require_execution_frontier("observe")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(
                self.step_error("`observe` must run before execution reaches function exit")
            );
        }
        let result = execution
            .core
            .record_named_resource_observation(
                context.function,
                context.arguments,
                self.facts(),
                instance,
            )
            .map_err(|message| self.step_error(format!("`observe` refused: {message}")))?;
        let presentations =
            crate::surface::proof::resources::pair_instance_body_clause_presentations(
                context.resource_environment,
                context.spec_definitions.functions,
                instance,
                &result.body_clauses,
                &ProgramValueBindings::new(),
                None,
            )?;
        for clause in presentations {
            execution
                .presentation
                .surface_propositions
                .record_lowering(&clause.source, &clause.checked.proposition)?;
            execution.presentation.resource_body_clauses.push(clause);
        }
        let facts = result
            .semantic_facts
            .iter()
            .fold(self.facts().clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.clone())
            });
        execution.core.state = result.state.into();
        let branch = self
            .focused_branch()
            .expect("resource observation requires an open goal")
            .with_state(BranchState {
                facts,
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: result.semantic_facts.clone(),
            checked_facts: result.semantic_facts,
        })
    }

    pub(super) fn apply_execution_resource_observation(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if matches!(
            resource,
            ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_)
        ) {
            return self.apply_memory_observation(resource);
        }
        if let ResourceClause::Named { binding, .. } = resource {
            self.require_execution_frontier("observe")?;
            let instance = self
                .execution()
                .and_then(|execution| {
                    execution
                        .core
                        .state
                        .resource_instance_at_path(binding.instance().ok()?, &binding.children)
                })
                .ok_or_else(|| {
                    self.step_error("`observe` requires a held folded resource instance")
                })?;
            return self.apply_named_observation(instance);
        }
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
        execution.core.materialize_observation_entry();
        let checked = observe_composite_resource_for_proof(
            context.function,
            context.resource_environment,
            resource,
            context.parameter_binding(),
            (*execution.core.state).clone(),
            self.facts().clone(),
            &mut execution.presentation.surface_propositions,
            &mut execution.core.function_entry_derivations,
            context.spec_definitions,
            context.claim_label,
            context.tactic_index,
        )?;
        let state = execution
            .core
            .record_resource_observation(
                context.function,
                context.arguments,
                &before_facts,
                &checked.observed_resource,
                checked.successor.input(),
                &checked.facts,
            )
            .map_err(|message| {
                self.step_error(format!("kernel rejected checked `observe`: {message}"))
            })?;
        execution.core.state = state.into();
        let branch = self
            .focused_branch()
            .expect("resource observation requires an open goal")
            .with_state(BranchState {
                facts: checked.facts,
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    /// `let { witness: name, ... } = unfold(resource)`: the unfold, with each
    /// named `let ... where` witness bound to its proof name as the value the
    /// body binds it to, so later facts and requirement spellings name it.
    pub(super) fn apply_execution_resource_unfold_naming_witnesses(
        &self,
        resource: &ResourceClause,
        names: &[(String, String)],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`let { ... } = unfold(...)` requires an execution proof"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, true, None, names);
        }
        if self.focused_outcome_data().is_some() {
            return Err(
                self.step_error("naming witnesses at function exit requires a named resource")
            );
        }
        let witnesses = super::super::resources::declared_resource_witness_values(
            context.resource_environment,
            resource,
            context.parameter_binding(),
            &execution.core.state,
            self.facts().assumptions(),
            context.spec_definitions,
            context.claim_label,
            context.tactic_index,
        )?;
        let mut transition = super::super::resources::with_unfold_witness_names(names, || {
            self.apply_execution_resource_unfold(resource, resource)
        })?;
        self.bind_unfold_witness_outputs(
            &mut transition.locals,
            &execution.core.state,
            names,
            witnesses.iter().map(|(slot, value)| (slot.as_str(), value)),
        )?;
        Ok(transition)
    }

    fn bind_unfold_witness_outputs<'w>(
        &self,
        locals: &mut ProofLocals,
        state: &ExecutionState,
        names: &[(String, String)],
        witnesses: impl IntoIterator<Item = (&'w str, &'w ProgramValue)>,
    ) -> Result<(), ClickError> {
        let witnesses = witnesses.into_iter().collect::<BTreeMap<_, _>>();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("resource witnesses require an execution proof");
        };
        for (slot, name) in names {
            let Some(&value) = witnesses.get(slot.as_str()) else {
                let known = witnesses
                    .keys()
                    .map(|witness| format!("`{witness}`"))
                    .collect::<Vec<_>>();
                return Err(self.step_error(format!(
                    "`{slot}` is not a witness of this resource's body{}",
                    if known.is_empty() {
                        ", which exposes none here".to_string()
                    } else {
                        format!("; its witnesses are {}", known.join(", "))
                    }
                )));
            };
            if name == "result"
                || locals.values.contains_key(name)
                || locals.integer_values.contains_key(name)
                || state.locals().contains_name(name)
                || context
                    .parsed_function
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.name() == name)
            {
                return Err(self.step_error(format!(
                    "unfold witness binding `{name}` is already in scope"
                )));
            }
            locals.set_values(locals.values.with_inserted(
                name.clone(),
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.clone())),
            ));
        }
        Ok(())
    }

    pub(super) fn apply_execution_resource_unfold(
        &self,
        resource: &ResourceClause,
        source_resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if self.execution().is_some()
            && !matches!(resource, ResourceClause::Named { .. })
            && !matches!(resource, ResourceClause::Declared { name, .. } if name == "authority")
            && !self.is_authority_control_resource(resource)
            && !self.is_authority_transfer_wrapper(resource)
            && !self.names_unauthorized_family(resource)
        {
            return self.apply_execution_population_member_exchange(
                resource,
                source_resource,
                false,
            );
        }
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, true, None, &[]);
        }
        if matches!(resource, ResourceClause::Declared { name, .. } if name == "authority") {
            return self.apply_execution_population_authority_exchange(resource, false);
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
        // An argument only the function's entry holds, `old(self.slot)`, is
        // its entry value: the unfold lowers its clause at the current state.
        let resource = &self.with_entry_arguments_resolved(resource, context, &execution)?;
        let checked = unfold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            source_resource,
            context.parameter_binding(),
            (*execution.core.state).clone(),
            self.facts().clone(),
            &mut execution.presentation.surface_propositions,
            context.spec_definitions,
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
                execution: Some(Arc::new(execution)),
            });
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(branch),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    /// `resource` with each `old(...)` argument replaced by its value at the
    /// function's entry, lowered once with the entry state so a later
    /// lowering at the current state reads the same value.
    fn with_entry_arguments_resolved(
        &self,
        resource: &ResourceClause,
        context: &ExecutionProofContext<'_>,
        execution: &ExecutionProofState,
    ) -> Result<ResourceClause, ClickError> {
        let ResourceClause::Declared { arguments, .. } = resource else {
            return Ok(resource.clone());
        };
        if !arguments
            .iter()
            .any(|argument| matches!(argument, SyntaxTerm::Old(_)))
        {
            return Ok(resource.clone());
        }
        let Some(entry) = context.constants.function_entry_state.as_ref() else {
            return Ok(resource.clone());
        };
        let lowered =
            crate::surface::lowering::lower_resource_clause_at_current_locals_with_entry_and_assumptions(
                resource,
                context.parameter_binding(),
                entry,
                &execution.core.state,
                None,
                self.facts().assumptions(),
            )?;
        let Resource::Composite {
            arguments: values, ..
        } = lowered.resource()
        else {
            return Ok(resource.clone());
        };
        let values = values.native_values().into_owned();
        let mut resolved = resource.clone();
        if let ResourceClause::Declared { arguments, .. } = &mut resolved {
            for (argument, value) in arguments.iter_mut().zip(values) {
                if let (SyntaxTerm::Old(_), AlgebraicValue::Program(value)) = (&*argument, value) {
                    *argument = SyntaxTerm::ProgramExpression(ProgramExpression::Value(value));
                }
            }
        }
        Ok(resolved)
    }

    /// Construct the fold successor; the driver owns its obligation proofs.
    pub(super) fn apply_primitive_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<Self, ClickError> {
        let _timing = crate::instrumentation::OperationTiming::new(
            self.claim_label(),
            "resource fold",
            "resource fold: apply selected fold",
        );
        let step = ProofStep::FoldResource(resource.clone());
        let at_outcome = self.focused_outcome_data().is_some();
        let transition = if at_outcome
            && let ResourceClause::Declared { name, .. } = resource
            && let ProofContext::Execution(context) = self.context.as_ref()
            && context
                .function
                .contract_interface()
                .is_ordinary_abstract_family(name)
        {
            self.apply_outcome_resource_construction(resource)?
        } else {
            // Resolve proof bindings before either the execution or
            // outcome path interprets ordinary resource arguments.
            let source_resource = resource;
            let resource = &self.resolve_proof_resource_arguments(resource)?;
            // A body fact over a witness an unfold named is spelled with
            // that name.
            let named_values = self
                .state()
                .locals()
                .values
                .iter()
                .filter_map(|(name, value)| match value {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(value)) => {
                        Some((value.clone(), name.clone()))
                    }
                    _ => None,
                })
                .collect();
            let mut transition =
                crate::surface::proof::surface_synthesis::with_proof_local_value_names(
                    named_values,
                    || {
                        if at_outcome {
                            self.apply_outcome_resource_fold(resource)
                        } else {
                            self.apply_execution_resource_fold(resource, source_resource)
                        }
                    },
                )?;
            transition.clear_existential_projection();
            transition
        };
        let state = self.publish_checked_transition(transition)?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(&self.node, self.focused_branch_id(), Arc::new(step)),
        })
    }

    pub(super) fn apply_execution_resource_fold(
        &self,
        resource: &ResourceClause,
        source_resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if self.execution().is_some()
            && !matches!(resource, ResourceClause::Named { .. })
            && !matches!(resource, ResourceClause::Declared { name, .. } if name == "authority")
            && !self.is_authority_control_resource(resource)
            && !self.is_authority_transfer_wrapper(resource)
            && !self.names_unauthorized_family(resource)
        {
            return self.apply_execution_population_member_exchange(
                resource,
                source_resource,
                true,
            );
        }
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, false, None, &[]);
        }
        if matches!(resource, ResourceClause::Declared { name, .. } if name == "authority") {
            return self.apply_execution_population_authority_exchange(resource, true);
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
        let family_reaches_population = self.family_reaches_population(resource);
        let checked = fold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            source_resource,
            context.claim_label,
            context.tactic_index,
            self.facts().clone(),
            context.parameter_binding(),
            &pre_state,
            (*execution.core.state).clone(),
            context.spec_definitions,
            family_reaches_population,
        )?;
        let selected = &checked.selected;
        execution
            .core
            .record_resource_rewrite_with_borrow_holds(
                context.function,
                context.arguments,
                &before_facts,
                selected,
                &checked.state,
                &checked.facts,
                None,
                &checked.borrow_holds,
                crate::surface::proof::execution_planning::collecting_step_requirements(),
            )
            .map_err(|error| {
                self.step_error(format!(
                    "kernel rejected checked resource `fold`: {}",
                    error.message
                ))
            })?;
        execution.core.state = checked.state.into();
        let branch = self
            .focused_branch()
            .expect("resource fold requires an open goal")
            .with_state(BranchState {
                facts: checked.facts,
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
        source_resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if self.execution().is_some()
            && !self.is_authority_transfer_wrapper(resource)
            && !matches!(resource, ResourceClause::Named { .. })
            && !self.names_unauthorized_family(resource)
        {
            return Err(self.step_error("resource unfold after function outcome is unavailable"));
        }
        if matches!(resource, ResourceClause::Declared { name, .. } if name == "authority") {
            return Err(self.step_error(
                "population authority `unfold` must run before the function reaches its outcome",
            ));
        }
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, true, None, &[]);
        }
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
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    goal.data.core.result.clone().into_native(),
                )),
            )]),
        )
        .map_err(|message| self.step_error(message))?;
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let mut execution =
            branch_state.execution.as_deref().cloned().ok_or_else(|| {
                self.step_error("outcome resource unfold lost its execution state")
            })?;
        let mut data = (*goal.data).clone();
        let checked = unfold_composite_resource_for_proof(
            context.resource_environment,
            &resource,
            source_resource,
            context.parameter_binding(),
            (*data.core.state).clone(),
            self.facts().clone(),
            &mut data.surface_propositions,
            context.spec_definitions,
            context.claim_label,
            context.tactic_index,
            false,
        )?;
        {
            execution
                .core
                .record_return_composite_resource_rewrite(
                    context.function,
                    goal.path_index,
                    self.facts(),
                    &checked.selected,
                    &goal.data.core,
                    &checked.state,
                    &checked.facts,
                    &checked.published_facts,
                    false,
                )
                .map_err(|message| self.step_error(message))?;
        }
        data.core.state = checked.state.into();
        let mut updated = goal.clone();
        updated.data = Arc::new(data);
        Ok(CheckedFocusedTransition {
            locals: self.state().locals().clone(),
            branch: Some(OpenBranch::function_outcome(
                updated,
                BranchState {
                    facts: checked.facts,
                    execution: Some(Arc::new(execution)),
                },
            )),
            added_facts: checked.added_facts.clone(),
            checked_facts: checked.added_facts,
        })
    }

    /// Applies one source-ordered composite fold to the focused branch's typed outcome.
    /// The result/state state and persistent fact root advance together in
    /// the returned Proof successor; no caller-owned outcome is mutated.
    pub(super) fn apply_outcome_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if self.execution().is_some()
            && !self.is_authority_transfer_wrapper(resource)
            && !matches!(resource, ResourceClause::Named { .. })
            && !self.names_unauthorized_family(resource)
        {
            return Err(self.step_error("resource fold after function outcome is unavailable"));
        }
        if let ResourceClause::Named { binding, .. } = resource {
            return self.apply_instance_rewrite(binding, resource, false, None, &[]);
        }
        if matches!(resource, ResourceClause::Declared { name, .. } if name == "authority") {
            return Err(self.step_error(
                "population authority `fold` must run before the function reaches its outcome",
            ));
        }
        self.apply_outcome_resource_fold_with_closure(
            resource,
            ResourceBodyClosure::Initialize,
            true,
        )
    }

    /// Closing an already open scope is checked by the same resource law as
    /// an explicit fold, with the scope's ownership-preservation policy.
    pub(in crate::surface::proof) fn close_outcome_resource_scope(
        &self,
        resource: &ResourceClause,
        restoration: &OpenResourceRestoration,
        contract_resources_established: bool,
    ) -> Result<Self, ClickError> {
        let OpenResourceRestoration::Declared {
            preserve_exposed_body,
        } = restoration
        else {
            let OpenResourceRestoration::Named(instance) = restoration else {
                unreachable!()
            };
            return self.restore_open_instance(resource, instance);
        };
        let transition = self.apply_outcome_resource_fold_with_closure(
            resource,
            ResourceBodyClosure::CloseOpen {
                preserve_exposed_body: *preserve_exposed_body,
            },
            !contract_resources_established,
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
        retain_return_exchange: bool,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource `fold` requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("outcome resource `fold` requires a focused outcome goal"));
        };
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let mut execution =
            branch_state.execution.as_deref().cloned().ok_or_else(|| {
                self.step_error("outcome resource `fold` lost its execution state")
            })?;
        let pre_state = execution
            .core
            .frontier
            .execution_start_state(&execution.core.state);
        let outcome = FunctionOutcome::Return {
            value: goal.data.core.result.clone(),
            state: Box::new((*goal.data.core.state).clone()),
        };
        let family_reaches_population = self.family_reaches_population(resource);
        let checked = fold_composite_resource_on_outcome_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            goal.path_index,
            &*goal.data.core.effect_facts,
            self.facts().clone(),
            context.parameter_binding(),
            pre_state,
            outcome,
            context.spec_definitions,
            closure,
            family_reaches_population,
        )?;
        let FunctionOutcome::Return { value, state } = checked.outcome else {
            unreachable!("folding a return outcome preserves its outcome kind")
        };
        // Ordinary macro folds keep their final contract-definition law.
        // Authority wrappers and guarded ownership need an execution exchange.
        // Named outputs also require the exact published frontier after an
        // ordinary refold, including a static wrapper with no guarded body.
        // Contracts with only ordinary outputs retain their definition law.
        let operational_exchange = match checked.selected.resource() {
            Resource::Composite { name, .. } => context
                .function
                .composite_resource_definition(name)
                .is_some_and(|definition| {
                    definition.contains().iter().any(|spec| {
                        matches!(
                            spec.term(),
                            crate::kernel::ResourceTerm::PopulationAuthority { .. }
                                | crate::kernel::ResourceTerm::Iterated(_)
                        )
                    })
                }),
            _ => false,
        };
        // The checked contract transition has its own resource evidence and
        // may bind outputs to their interface identities. A later scope close
        // still checks its body law, but does not exchange that final contract
        // presentation against the earlier C-body publication.
        if retain_return_exchange
            && *state != *goal.data.core.state
            && (operational_exchange
                || context
                    .function
                    .resource_ensures()
                    .iter()
                    .any(|spec| spec.is_instance())
                || (self.is_authority_transfer_wrapper(resource) && family_reaches_population))
        {
            let viewed = ResourceFact::View(checked.selected.resource().clone());
            let selected = if state
                .resources()
                .directly_supporting_fact(&checked.selected, self.facts().assumptions())
                .is_none()
                && goal
                    .data
                    .core
                    .state
                    .resources()
                    .directly_supporting_fact(&checked.selected, self.facts().assumptions())
                    .is_none()
            {
                &viewed
            } else {
                &checked.selected
            };
            execution
                .core
                .record_return_composite_resource_rewrite(
                    context.function,
                    goal.path_index,
                    self.facts(),
                    selected,
                    &goal.data.core,
                    &state,
                    &checked.facts,
                    &[],
                    crate::surface::proof::execution_planning::collecting_step_requirements(),
                )
                .map_err(|message| self.step_error(message))?;
        }
        if crate::surface::proof::execution_planning::collecting_step_requirements() {
            execution.core.prepare_return_definition_fold(
                goal.path_index,
                self.facts(),
                &checked.facts,
            );
        }
        let mut data = (*goal.data).clone();
        data.core.result = value;
        data.core.state = (*state).into();
        let mut updated = goal.clone();
        updated.data = Arc::new(data);
        let state = BranchState {
            facts: checked.facts,
            execution: Some(Arc::new(execution)),
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
    fn apply_outcome_resource_construction(
        &self,
        resource: &ResourceClause,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("abstract token `fold` requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("abstract token `fold` requires a focused outcome goal"));
        };
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let execution = branch_state
            .execution
            .as_deref()
            .ok_or_else(|| self.step_error("abstract token `fold` lost its execution state"))?;
        let value = goal.data.core.result.native();
        let state = (*goal.data.core.state).clone();
        let fact = lower_resource_clause_at_state_with_result(
            resource,
            context.parameter_binding(),
            &state,
            &value,
        )?;
        let assumptions = self.facts().assumptions();
        let state = crate::kernel::construct_program_function_resource(
            &state,
            context.function,
            context.arguments,
            &value,
            &fact,
            assumptions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "kernel rejected checked resource `fold`: {message}"
            ))
        })?;
        let mut data = (*goal.data).clone();
        data.core.state = state.into();
        let mut updated = goal.clone();
        updated.data = Arc::new(data);
        let state = BranchState {
            facts: self.facts().clone(),
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

/// Whether substituting this binding changes the expression. The parts of a
/// range fold other than its end must not read the parameter that supplies
/// that end, or the shorter fold would not be the same function applied at a
/// smaller endpoint. A substitution failure counts as an occurrence: the
/// check refuses rather than guesses.
fn contract_expression_reads_binding(
    expression: &SyntaxTerm,
    binding: &crate::kernel::BindingName,
) -> bool {
    let substitutions =
        BTreeMap::from([(binding.clone(), SyntaxTerm::IntegerLiteral("0".to_string()))]);
    substitute_contract_expression(expression, &substitutions)
        .map(|substituted| &substituted != expression)
        .unwrap_or(true)
}

/// The parameter a range fold uses directly as its end. The append law
/// restates the shorter fold as the same application at the predecessor.
fn fold_end_parameter_binding(end: &SyntaxTerm) -> Option<crate::kernel::BindingName> {
    match end {
        SyntaxTerm::Binding(binding) | SyntaxTerm::ProgramBinding(binding) => Some(binding.into()),
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(binding))
            if binding.named().is_some() =>
        {
            Some(binding.clone())
        }
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

mod search;

/// An explicit unfold selects known constructor arms. Substitute only each
/// selected scrutinee and the final body so nested matches keep linear work.
fn select_known_unfold_body(body: &SyntaxTerm) -> Result<SyntaxTerm, String> {
    let mut selected = body;
    let mut bindings = BTreeMap::new();
    while let SyntaxTerm::AlgebraicMatch { scrutinee, arms } = selected {
        crate::instrumentation::record_deterministic_work(1);
        let scrutinee = substitute_contract_expression(scrutinee, &bindings)?;
        let SyntaxTerm::AlgebraicConstructor {
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
        selected = &arm.body;
    }
    substitute_contract_expression(selected, &bindings)
}
