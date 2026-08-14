use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceBodyAccess {
    Finalize,
    Open,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceBodyClosure {
    Initialize,
    CloseOpen { preserve_exposed_body: bool },
}

pub(super) struct UnfoldedCompositeResource {
    pub(super) state: CState,
    pub(super) body_was_already_exposed: bool,
}

pub(super) fn materialize_counted_population_bodies(
    resource_environment: &ResourceEnvironment,
    _parameters: &[syntax::C0Parameter],
    _arguments: &[CExpression],
    mut state: CState,
    observed_population_families: &BTreeSet<String>,
    _predicate_environment: &PredicateEnvironment,
    _click_function_environment: &ClickFunctionEnvironment,
    _claim_label: &str,
) -> Result<(CState, Vec<Proposition>), ClickError> {
    let mut populations = Vec::<(String, Vec<CValue>, u32)>::new();
    for fact in state.resources().facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) => continue,
        };
        if resource_environment.get(name).is_none() {
            continue;
        }
        let quantity = fact
            .owned_quantity()
            .unwrap_or_else(|| u32::from(fact.is_view()));
        if quantity == 0 {
            continue;
        }
        if let Some(existing) =
            populations
                .iter_mut()
                .find(|(existing_name, existing_arguments, _)| {
                    existing_name == name && existing_arguments == arguments
                })
        {
            existing.2 = existing.2.saturating_add(quantity);
        } else {
            populations.push((name.clone(), arguments.clone(), quantity));
        }
    }

    let mut next_variable = COUNTED_POPULATION_VARIABLE_BASE;
    let mut facts = Vec::new();
    let mut family_totals = BTreeMap::<String, Bitvector32Term>::new();

    for (name, resource_arguments, visible_quantity) in populations {
        let observes_population = observed_population_families.contains(&name);
        let tracks_population_in_body = resource_environment
            .get(&name)
            .and_then(|definition| definition.composite_body())
            .is_some_and(|body| body.facts().iter().any(proposition_contains_resource_count));
        // A singleton ordinary resource does not need a persistent ghost
        // ledger merely so `open`/`unfold` can expose its body. Counts are
        // materialized when the proof observes them, when the body relates C
        // state to the population, or when visible multiplicity matters.
        if !observes_population && !tracks_population_in_body && visible_quantity == 1 {
            continue;
        }
        let count = if observes_population {
            let count = Bitvector32Term::Variable(Variable(next_variable));
            next_variable = next_variable.saturating_add(1);
            count
        } else {
            Bitvector32Term::Constant(visible_quantity)
        };
        state = state.with_counted_population(&name, resource_arguments.clone(), count.clone());
        facts.push(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(count.clone()),
                Box::new(Bitvector32Term::Constant(visible_quantity)),
            ),
            true,
        ));
        if let Some(total) = family_totals.get(&name).cloned() {
            facts.push(Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(total.clone(), count.clone()),
                false,
            ));
            family_totals.insert(name, Bitvector32Term::add(total, count));
        } else {
            family_totals.insert(name, count);
        }
    }

    Ok((state, facts))
}

pub(super) fn materialize_folded_composite_resource_cells(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    claim_label: &str,
) -> Result<CState, ClickError> {
    let memory = materialize_folded_composite_resource_memory(
        resource_environment,
        parameters,
        arguments,
        &state,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    Ok(state.with_memory(memory))
}

fn materialize_folded_composite_resource_memory(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Result<CMemory, String> {
    let mut memory = state.memory().clone();
    for resource in state.resources().facts() {
        let (name, resource_arguments) = match resource.resource() {
            CResource::Composite { name, arguments } => (name, arguments),
            CResource::Memory(_) | CResource::Token { .. } => {
                continue;
            }
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        if composite_body.condition().is_some() {
            continue;
        }
        let substitutions =
            resource_value_substitutions(definition, resource_arguments).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        memory = materialize_composite_resource_memory(
            name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            memory,
        )?;
    }
    Ok(memory)
}

pub(super) fn project_initial_composite_resource_cores(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &[Proposition],
    claim_label: &str,
    include_owned: bool,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CState, ClickError> {
    let assumptions = assumptions_from_propositions(available_pure_facts);
    for resource in state.resources().facts().to_vec() {
        let (name, resource_arguments, is_owned) = match resource {
            CResourceFact::View(CResource::Composite { name, arguments }) => {
                (name, arguments, false)
            }
            CResourceFact::Own(CResource::Composite { name, arguments }, _) => {
                (name, arguments, true)
            }
            _ => continue,
        };
        let Some(definition) = resource_environment.get(&name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        if is_owned && !include_owned {
            continue;
        }
        let substitutions =
            resource_value_substitutions(definition, &resource_arguments).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` setup failed: could not project composite resource core `{name}`: {message}"
                ))
            })?;
        let Some(body_active) = try_select_composite_resource_body(
            definition,
            &substitutions,
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not select composite resource core `{name}`: {message}"
            ))
        })?
        else {
            continue;
        };
        if !body_active {
            continue;
        }
        let (memory, contained_resources) = instantiate_composite_resource_body_resources(
            &name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            state.memory().clone(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not project composite resource core `{name}`: {message}"
            ))
        })?;
        let viewed_contained_resources = contained_resources
            .facts()
            .iter()
            .filter_map(CResourceFact::core)
            .collect::<Vec<_>>();
        let resources = state
            .resources()
            .clone()
            .try_compose_with_facts_delaying_normalization(
                viewed_contained_resources,
                &assumptions,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` setup failed: projecting composite resource core `{name}` produced {}",
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        state = state.with_memory(memory).with_resource_context(resources);
    }
    Ok(state)
}

pub(super) fn project_initial_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let result = CValue::Int32(Bitvector32Term::Constant(0));
    let projected_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        &format!("`{claim_label}` setup"),
    )?;
    project_folded_resource_observable_facts(
        resource_environment,
        parameters,
        arguments,
        state,
        state,
        &result,
        &projected_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))
}

pub(super) fn project_outcome_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    path_index: usize,
) -> Result<Vec<Proposition>, ClickError> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Ok(available_pure_facts.to_vec());
    };
    let projected_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        &format!("`{claim_label}` path {path_index}"),
    )?;
    project_folded_resource_observable_facts(
        resource_environment,
        parameters,
        arguments,
        pre_state,
        state,
        value,
        &projected_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}: could not project folded resource facts: {message}"
        ))
    })
}

fn project_resource_context_observable_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    resources: &ResourceContext,
    available_pure_facts: &[Proposition],
    context: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut propositions = available_pure_facts.to_vec();
    let facts = resources.observable_facts(&assumptions).map_err(|error| {
        ClickError::new(format!(
            "{context}: {}",
            describe_resource_context_validity_error(error, parameters, arguments)
        ))
    })?;
    for proposition in facts {
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
    Ok(propositions)
}

fn append_state_resource_context_observable_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &mut Vec<Proposition>,
    context: &str,
) -> Result<(), ClickError> {
    *available_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        context,
    )?;
    Ok(())
}

fn project_folded_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, String> {
    let mut propositions = available_pure_facts.to_vec();
    for resource in state.resources().facts() {
        project_held_resource_observable_facts(
            resource_environment,
            resource,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            &mut propositions,
            predicate_environment,
            click_function_environment,
        )?;
    }
    Ok(propositions)
}

pub(super) fn observe_composite_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    available_pure_facts: &mut Vec<Proposition>,
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CState, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "observe",
        claim_label,
        tactic_index,
    )?;
    let abstract_resource = lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    if !state
        .resources()
        .satisfies_fact(&abstract_resource, &assumptions)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `observe({})` failed: {}",
            describe_resource_clause(resource),
            describe_missing_resource_fact(
                &abstract_resource,
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let CResource::Composite {
        arguments: resource_arguments,
        ..
    } = abstract_resource.resource()
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `observe` expects a composite resource"
        )));
    };
    let surface_substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    let observation_pre_state = state.clone();
    let (memory, contained_resources) = apply_composite_observation_law(
        definition,
        resource_arguments,
        parameters,
        arguments,
        &state,
        &state,
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not observe `{}`: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let fact_state = observation_pre_state.clone().with_memory(memory.clone());
    record_observed_composite_surface_facts(
        definition,
        resource,
        &surface_substitutions,
        parameters,
        arguments,
        &observation_pre_state,
        &fact_state,
        available_pure_facts,
        surface_propositions,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not record observed `{}` facts: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let viewed_contained_resources = contained_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::core)
        .collect::<Vec<_>>();
    // Holding the folded composite certifies its instantiated body. Observation
    // only adds the body's duplicable cores, so it must not revalidate ownership.
    let resources = state
        .resources()
        .clone()
        .unchecked_with_facts(viewed_contained_resources);
    Ok(state.with_memory(memory).with_resource_context(resources))
}

#[allow(clippy::too_many_arguments)]
fn record_observed_composite_surface_facts(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    available_pure_facts: &[Proposition],
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    let composite_body = definition
        .composite_body()
        .expect("observing a composite resource requires a composite body");
    let Some(active) = try_select_composite_resource_body(
        definition,
        substitutions,
        parameters,
        arguments,
        pre_state,
        fact_state,
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )?
    else {
        return Ok(());
    };
    if !active {
        return Ok(());
    }
    let parent = lower_resource_clause(resource, parameters, arguments, fact_state.memory())
        .map_err(|error| error.message().to_string())?;
    let parent_subject = resource_clause_subject(resource);
    let mut owned_children = Vec::new();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!(
                    "could not instantiate resource `{}` contained resource: {message}",
                    definition.name()
                )
            })?;
        let lowered = lower_resource_clause(&contained, parameters, arguments, fact_state.memory())
            .map_err(|error| error.message().to_string())?;
        if let Some(child) = lowered.owned_resource() {
            let child_subject = resource_clause_subject(&contained);
            surface_propositions
                .record_lowering(
                    &ClickProposition::Contains {
                        parent: parent_subject.clone(),
                        child: child_subject.clone(),
                    },
                    &Proposition::CResourceContains {
                        parent: parent.resource().clone(),
                        child: child.clone(),
                    },
                )
                .map_err(|error| error.message().to_string())?;
            owned_children.push((child.clone(), child_subject));
        }
        let (ResourceClause::Read(segment) | ResourceClause::Write(segment)) = &contained else {
            continue;
        };
        if let Some(kernel) =
            resource_clause_loadable_prop(&contained, parameters, arguments, fact_state.memory())
                .map_err(|error| error.message().to_string())?
        {
            surface_propositions
                .record_lowering(
                    &ClickProposition::Loadable {
                        segment: segment.clone(),
                    },
                    &kernel,
                )
                .map_err(|error| error.message().to_string())?;
        }
    }
    for left_index in 0..owned_children.len() {
        for (right, right_subject) in &owned_children[left_index + 1..] {
            let (left, left_subject) = &owned_children[left_index];
            surface_propositions
                .record_lowering(
                    &ClickProposition::Separate {
                        left: left_subject.clone(),
                        right: right_subject.clone(),
                    },
                    &Proposition::CResourceSeparate {
                        left: left.clone(),
                        right: right.clone(),
                    },
                )
                .map_err(|error| error.message().to_string())?;
        }
    }
    for fact in composite_body.facts() {
        let surface = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        let kernel = lower_outcome_proposition(
            parameters,
            arguments,
            pre_state,
            fact_state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            &surface,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            format!(
                "could not lower resource `{}` fact `{}`: {message}",
                definition.name(),
                describe_click_proposition(&surface)
            )
        })?;
        surface_propositions
            .record_lowering(&surface, &kernel)
            .map_err(|error| error.message().to_string())?;
    }
    Ok(())
}

fn resource_clause_subject(resource: &ResourceClause) -> ResourceSubject {
    match resource {
        ResourceClause::Read(segment) | ResourceClause::Write(segment) => {
            ResourceSubject::Memory(segment.clone())
        }
        ResourceClause::Declared {
            kind,
            name,
            arguments,
            parameter_types,
            ..
        } => ResourceSubject::Declared {
            kind: *kind,
            name: name.clone(),
            arguments: arguments.clone(),
            parameter_types: parameter_types.clone(),
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_initial_composite_surface_facts(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &[Proposition],
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_resources: &mut BTreeSet<String>,
) -> Result<(), String> {
    let ResourceClause::Declared { name, .. } = resource else {
        return Ok(());
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(());
    };
    let Some(body) = definition.composite_body() else {
        return Ok(());
    };
    if !active_resources.insert(name.clone()) {
        return Ok(());
    }
    let result = (|| {
        let substitutions =
            resource_argument_substitutions(definition, resource, "initial resource projection", 0)
                .map_err(|error| error.message().to_string())?;
        let Some(true) = try_select_composite_resource_body(
            definition,
            &substitutions,
            parameters,
            arguments,
            state,
            state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            predicate_environment,
            click_function_environment,
        )?
        else {
            return Ok(());
        };
        for fact in body.facts() {
            let surface = substitute_click_proposition(fact, &substitutions)?;
            if !matches!(surface, ClickProposition::Separate { .. }) {
                continue;
            }
            let kernel = lower_outcome_proposition(
                parameters,
                arguments,
                state,
                state,
                &CValue::Int32(Bitvector32Term::Constant(0)),
                available_pure_facts,
                &surface,
                predicate_environment,
                click_function_environment,
            )?;
            if available_pure_facts.contains(&kernel) {
                surface_propositions
                    .record_lowering(&surface, &kernel)
                    .map_err(|error| error.message().to_string())?;
            }
        }
        Ok(())
    })();
    active_resources.remove(name);
    result
}

fn project_held_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CMemory, String> {
    let (name, resource_arguments) = match resource.resource() {
        CResource::Composite { name, arguments } => (name, arguments),
        CResource::Memory(_) | CResource::Token { .. } => {
            return Ok(state.memory().clone());
        }
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(state.memory().clone());
    };
    apply_composite_observation_law(
        definition,
        resource_arguments,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map(|(memory, _)| memory)
}

#[allow(clippy::too_many_arguments)]
fn try_select_composite_resource_body(
    definition: &ResourceDefinition,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Option<bool>, String> {
    let Some(condition) = definition
        .composite_body()
        .and_then(CompositeResourceBody::condition)
    else {
        return Ok(Some(true));
    };
    let condition = substitute_click_proposition(condition, substitutions).map_err(|message| {
        format!(
            "could not instantiate resource `{}` condition: {message}",
            definition.name()
        )
    })?;
    let lowered = lower_outcome_proposition(
        parameters,
        arguments,
        pre_state,
        state,
        result,
        available_pure_facts,
        &condition,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        format!(
            "could not lower resource `{}` condition `{}`: {message}",
            definition.name(),
            describe_click_proposition(&condition)
        )
    })?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let proves_condition = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_condition_exact_or_snapshot(condition, *value)
                || assumptions.decide(condition) == Some(*value)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.proves_condition_exact_or_snapshot(condition, !*value)
                    || assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        _ => assumptions.proves_exact(proposition) || assumptions.proves(proposition),
    };
    if proves_condition(&lowered) {
        return Ok(Some(true));
    }
    let negated = match &lowered {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    };
    if proves_condition(&negated) {
        return Ok(Some(false));
    }
    let is_atomic_condition = matches!(&lowered, Proposition::ConditionIs(_, _))
        || matches!(
            &lowered,
            Proposition::Not(body)
                if matches!(body.as_ref(), Proposition::ConditionIs(_, _))
        );
    if is_atomic_condition {
        // Conditional resource bodies are intentionally opaque while their
        // guard is undecided. A general contradiction search here can recurse
        // through every materialized heap snapshot in a recursive resource.
        return Ok(None);
    }
    if fact_conflicts_with_assumptions(&lowered, &assumptions) {
        return Ok(Some(false));
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn composite_resource_body_is_active(
    definition: &ResourceDefinition,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<bool, String> {
    try_select_composite_resource_body(
        definition,
        substitutions,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )?
    .ok_or_else(|| {
        format!(
            "resource `{}` condition is undecided: prove it or its negation before using its body",
            definition.name()
        )
    })
}

/// Applies the non-consuming observation law declared by a composite body.
/// The kernel algebra handles the folded resource fact itself; Click owns this
/// definitional layer because it requires source-level substitution and fact
/// lowering.
pub(super) fn apply_composite_observation_law(
    definition: &ResourceDefinition,
    resource_arguments: &[CValue],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(CMemory, ResourceContext), String> {
    let Some(composite_body) = definition.composite_body() else {
        return Ok((state.memory().clone(), ResourceContext::new()));
    };

    let substitutions =
        resource_value_substitutions(definition, resource_arguments).map_err(|message| {
            format!(
                "could not instantiate resource `{}` facts: {message}",
                definition.name()
            )
        })?;
    let Some(body_active) = try_select_composite_resource_body(
        definition,
        &substitutions,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )?
    else {
        return Ok((state.memory().clone(), ResourceContext::new()));
    };
    if !body_active {
        return Ok((state.memory().clone(), ResourceContext::new()));
    }
    let (memory, contained_resources) = instantiate_composite_resource_body_resources(
        definition.name(),
        composite_body,
        &substitutions,
        parameters,
        arguments,
        state.memory().clone(),
    )?;
    let owned_body_resources = contained_resources
        .facts()
        .iter()
        .filter(|fact| fact.is_own())
        .collect::<Vec<_>>();
    if !owned_body_resources.is_empty() {
        let assumptions = assumptions_from_propositions(available_pure_facts);
        if owned_body_resources
            .iter()
            .all(|fact| state.resources().satisfies_fact(fact, &assumptions))
        {
            // `open` retains the folded head for contract accounting while
            // exposing the unique owned body. Until that body is closed, do
            // not re-project its invariant at a newer memory/count snapshot.
            return Ok((memory, ResourceContext::new()));
        }
    }
    let fact_state = state.clone().with_memory(memory.clone());

    append_composite_definition_observable_facts(
        definition,
        composite_body,
        &CResource::Composite {
            name: definition.name().to_string(),
            arguments: resource_arguments.to_vec(),
        },
        &substitutions,
        &contained_resources,
        parameters,
        arguments,
        pre_state,
        &fact_state,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )?;
    Ok((memory, contained_resources))
}

fn append_composite_definition_observable_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    parent_resource: &CResource,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
    propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    append_resource_context_observable_facts(contained_resources, propositions);

    append_composite_resource_relation_facts(parent_resource, contained_resources, propositions);

    append_composite_resource_loadable_facts(
        definition,
        composite_body,
        substitutions,
        parameters,
        arguments,
        fact_state.memory(),
        propositions,
    )?;

    append_composite_resource_declared_facts(
        definition,
        composite_body,
        substitutions,
        contained_resources,
        parameters,
        arguments,
        pre_state,
        fact_state,
        result,
        propositions,
        predicate_environment,
        click_function_environment,
    )
}

fn append_composite_resource_relation_facts(
    parent_resource: &CResource,
    contained_resources: &ResourceContext,
    propositions: &mut Vec<Proposition>,
) {
    let owned_children = contained_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::owned_resource)
        .cloned()
        .collect::<Vec<_>>();
    for child in &owned_children {
        let proposition = Proposition::CResourceContains {
            parent: parent_resource.clone(),
            child: child.clone(),
        };
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
    for i in 0..owned_children.len() {
        for right in &owned_children[i + 1..] {
            let proposition = Proposition::CResourceSeparate {
                left: owned_children[i].clone(),
                right: right.clone(),
            };
            if !propositions.contains(&proposition) {
                propositions.push(proposition);
            }
        }
    }
}

fn append_composite_resource_loadable_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    propositions: &mut Vec<Proposition>,
) -> Result<(), String> {
    for contained in composite_body.contains() {
        let contained = instantiate_resource_clause(contained, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` contained resource for loadability: {message}",
                definition.name()
            )
        })?;
        append_resource_clause_loadable_fact(
            &contained,
            parameters,
            arguments,
            memory,
            propositions,
        )
        .map_err(|error| {
            format!(
                "could not project resource `{}` contained `{}` loadability: {}",
                definition.name(),
                describe_resource_clause(&contained),
                error.message()
            )
        })?;
    }
    Ok(())
}

fn append_resource_clause_loadable_fact(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    propositions: &mut Vec<Proposition>,
) -> Result<(), ClickError> {
    let Some(proposition) = resource_clause_loadable_prop(resource, parameters, arguments, memory)?
    else {
        return Ok(());
    };
    if !propositions.contains(&proposition) {
        propositions.push(proposition);
    }
    Ok(())
}

pub(super) fn append_lowered_resource_clause_loadable_fact(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    lowered: &CResourceFact,
    state: &CState,
    propositions: &mut Vec<Proposition>,
) {
    let (ResourceClause::Read(segment) | ResourceClause::Write(segment)) = resource else {
        return;
    };
    let Some(range) = lowered
        .memory_view_range()
        .or_else(|| lowered.memory_own_range())
    else {
        return;
    };
    let proposition = memory_range_loadable_prop(
        state.memory(),
        range,
        contract_segment_element_width(parameters, segment),
    );
    if !propositions.contains(&proposition) {
        propositions.push(proposition);
    }
}

fn append_composite_resource_declared_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
    propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    for fact in composite_body.facts() {
        let fact = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        let lowered = lower_outcome_proposition(
            parameters,
            arguments,
            pre_state,
            fact_state,
            result,
            propositions,
            &fact,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            format!(
                "could not lower resource `{}` pure fact `{}`: {message}\n  pure facts: {}\n  resource facts: {}",
                definition.name(),
                describe_click_proposition(&fact),
                describe_pure_facts(propositions),
                describe_resource_facts(contained_resources.facts(), parameters, arguments)
            )
        })?;
        if !propositions.contains(&lowered) {
            propositions.push(lowered);
        }
    }
    Ok(())
}

pub(super) fn append_resource_context_observable_facts(
    resources: &ResourceContext,
    propositions: &mut Vec<Proposition>,
) {
    let assumptions = assumptions_from_propositions(propositions);
    let facts = resources.observable_facts_assuming_valid(&assumptions);
    for proposition in facts {
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
}

fn describe_resource_context_validity_error(
    error: ResourceContextValidityError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            format!(
                "duplicate resource fact `{}`",
                describe_resource_fact(&resource, parameters, arguments)
            )
        }
        ResourceContextValidityError::OverlappingWriteResources { left, right } => {
            format!(
                "overlapping owned memory resource facts `owns {}` and `owns {}`",
                describe_memory_range(&left, parameters, arguments),
                describe_memory_range(&right, parameters, arguments)
            )
        }
    }
}

fn materialize_composite_resource_memory(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: CMemory,
) -> Result<CMemory, String> {
    let (memory, _) = instantiate_composite_resource_body_resources(
        name,
        composite_body,
        substitutions,
        parameters,
        arguments,
        memory,
    )?;
    Ok(memory)
}

/// Instantiates the resource-state side of a composite definition. The result
/// is provisional until the caller composes it with assumptions and checks
/// validity through `ResourceContext`.
pub(in crate::lang::click) fn instantiate_composite_resource_body_resources(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut memory: CMemory,
) -> Result<(CMemory, ResourceContext), String> {
    let mut resources = ResourceContext::new();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        let lowered =
            lower_resource_clause(&contained, parameters, arguments, &memory).map_err(|error| {
                format!(
                    "could not lower resource `{name}` contained `{}`: {}\n  {}",
                    describe_resource_clause(&contained),
                    error.message(),
                    describe_available_facts(&[], resources.facts(), parameters, arguments, &[])
                )
            })?;
        memory = materialize_composite_resource_cells(memory, &contained, &lowered, parameters);
        // This composite-body instantiation path has no fact assumptions yet.
        // Projection/packing paths check composition once assumptions are
        // available.
        resources = resources.unchecked_with_fact(lowered);
    }
    Ok((memory, resources))
}

fn resource_value_substitutions(
    definition: &ResourceDefinition,
    arguments: &[CValue],
) -> Result<BTreeMap<String, ContractExpression>, String> {
    if definition.parameters().len() != arguments.len() {
        return Err(format!(
            "resource `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            (
                parameter.name().to_string(),
                ContractExpression::CFragment(CExpression::Value(argument.clone())),
            )
        })
        .collect())
}

/// Applies the owned-composite equivalence from the folded fact to one
/// instantiated body. This is a definition law, not primitive consumption
/// behavior of the kernel's folded composite fact.
pub(super) fn unfold_composite_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &mut Vec<Proposition>,
    surface_propositions: &mut SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
    access: ResourceBodyAccess,
) -> Result<UnfoldedCompositeResource, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "unfold",
        claim_label,
        tactic_index,
    )?;
    let composite_body = definition
        .composite_body()
        .expect("composite_resource_law_definition should require a composite body");
    let substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    let body_active = composite_resource_body_is_active(
        definition,
        &substitutions,
        parameters,
        arguments,
        &state,
        &state,
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not select `unfold({})` body: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let contained_clauses = if body_active {
        composite_body.contains()
    } else {
        &[]
    };
    let body_facts = if body_active {
        composite_body.facts()
    } else {
        &[]
    };
    let mut abstract_resource =
        lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    if access == ResourceBodyAccess::Open
        && !state
            .resources()
            .satisfies_fact(&abstract_resource, &assumptions)
    {
        let viewed = CResourceFact::View(abstract_resource.resource().clone());
        if state.resources().satisfies_fact(&viewed, &assumptions) {
            abstract_resource = viewed;
        }
    }
    let opening_view = abstract_resource.is_view();
    let (requested_population_name, requested_population_arguments) =
        match abstract_resource.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name.clone(), arguments.clone())
            }
            CResource::Memory(_) => unreachable!("a declared resource lowered to memory"),
        };
    let tracks_population_in_body = composite_body
        .facts()
        .iter()
        .any(proposition_contains_resource_count);
    let (population_name, population_arguments, population_count) = match state
        .counted_population_proven_equal(
            &requested_population_name,
            &requested_population_arguments,
            &assumptions,
        ) {
        Some(population) => population,
        None if tracks_population_in_body => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` requires an active resource population",
                describe_resource_clause(resource)
            )));
        }
        None => (
            requested_population_name,
            requested_population_arguments,
            Bitvector32Term::Constant(1),
        ),
    };
    if access == ResourceBodyAccess::Finalize {
        let count = population_count;
        let final_unit = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(count),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            true,
        );
        if !assumptions.proves(&final_unit) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` can finalize only a population whose count is proved equal to 1",
                describe_resource_clause(resource)
            )));
        }
    }
    // The ordinary case holds the folded composite exactly. Removing that
    // representation must not normalize every unrelated resource in the
    // ambient context. Preserve the equality-aware fallback for callers whose
    // resource arguments are only propositionally equal.
    let folded_resources = if access == ResourceBodyAccess::Open {
        // Opening exposes the population body but does not consume one of its
        // units. Keeping the folded unit in the context is also essential for
        // certifying execution against the enclosing function contract.
        state
            .resources()
            .satisfies_fact(&abstract_resource, &assumptions)
            .then(|| state.resources().clone())
    } else {
        state
            .resources()
            .clone()
            .without_exact_representation(&abstract_resource)
            .or_else(|| {
                state
                    .resources()
                    .clone()
                    .without_fact(&abstract_resource, &assumptions)
            })
    };
    let already_unfolded = folded_resources.is_none();
    let resources = if let Some(resources) = folded_resources {
        resources
    } else {
        let mut remaining = state.resources().clone();
        for contained in contained_clauses {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not inspect canonical `unfold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let lowered = lower_resource_clause(&contained, parameters, arguments, state.memory())?;
            let Some(next) = remaining.without_fact(&lowered, &assumptions) else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
                    describe_resource_clause(resource),
                    describe_missing_resource_fact(
                        &abstract_resource,
                        available_pure_facts,
                        state.resources().facts(),
                        parameters,
                        arguments,
                        &[]
                    )
                )));
            };
            remaining = next;
        }
        state.resources().clone()
    };
    state = state.with_resource_context(resources);

    if already_unfolded && contained_clauses.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
            describe_resource_clause(resource),
            describe_missing_resource_fact(
                &abstract_resource,
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                &[]
            )
        )));
    }

    let mut unfolded_facts = Vec::new();
    for contained in contained_clauses {
        let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})`: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let mut lowered = lower_resource_clause(&contained, parameters, arguments, state.memory())?;
        if opening_view {
            lowered = CResourceFact::View(lowered.resource().clone());
        }
        unfolded_facts.push(lowered.clone());
        let visible_quantity = lowered
            .owned_quantity()
            .unwrap_or_else(|| u32::from(lowered.is_view()));
        if visible_quantity > 0 {
            let named = match lowered.resource() {
                CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                    Some((name, arguments))
                }
                CResource::Memory(_) => None,
            };
            if let Some((name, resource_arguments)) = named
                && state.counted_population(name, resource_arguments).is_none()
            {
                state = state.clone().with_counted_population(
                    name.clone(),
                    resource_arguments.clone(),
                    Bitvector32Term::Constant(visible_quantity),
                );
            }
        }
        let memory = materialize_composite_resource_cells(
            state.memory().clone(),
            &contained,
            &lowered,
            parameters,
        );
        state = state.with_memory(memory);
        append_resource_clause_loadable_fact(
            &contained,
            parameters,
            arguments,
            state.memory(),
            available_pure_facts,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not project `unfold({})` loadability: {}",
                describe_resource_clause(resource),
                error.message()
            ))
        })?;
    }

    let body_was_already_exposed = composite_body.condition().is_none()
        && unfolded_facts
            .iter()
            .all(|fact| state.resources().satisfies_fact(fact, &assumptions));

    // Validate the projected ownership before assuming facts supplied by the
    // same definition. A body may legitimately state separation that is
    // needed to normalize symbolic children, but it must not use a
    // contradictory separation claim to conceal a concretely overlapping
    // pair. This is one validity pass over the complete projection, not one
    // normalization per child.
    if !already_unfolded && !body_was_already_exposed {
        let ownership_assumptions = assumptions.clone().without_explicit_separation_facts();
        let projected = state
            .resources()
            .clone()
            .unchecked_with_facts(unfolded_facts.clone());
        if let Some(error) = projected.validity_error(&ownership_assumptions) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                describe_resource_clause(resource),
                describe_resource_context_validity_error(error, parameters, arguments)
            )));
        }
    }

    for fact in body_facts {
        let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})` fact: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
        let lowered_fact = lower_outcome_proposition(
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            &fact,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower `unfold({})` pure fact `{}`: {message}\n{}",
                describe_resource_clause(resource),
                describe_click_proposition(&fact),
                describe_proof_context(
                    available_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    &[]
                )
            ))
        })?;
        surface_propositions.record_lowering(&fact, &lowered_fact)?;
        available_pure_facts.push(lowered_fact);
    }

    // Project the complete body in one checked composition. Composing each
    // child separately renormalizes the same ambient resource context once
    // per child, making one simple `unfold` depend on the accumulated proof
    // history rather than the size of the resource body. The definition's
    // pure facts are simultaneous consequences of the same composite law, so
    // make them available while canonicalizing its children.
    if !already_unfolded && !body_was_already_exposed {
        let composition_assumptions = assumptions_from_propositions(available_pure_facts);
        let resources = state
            .resources()
            .clone()
            .try_compose_with_facts(unfolded_facts.clone(), &composition_assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                    describe_resource_clause(resource),
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        state = state.with_resource_context(resources);
    }

    let unfolded_resources = ResourceContext::new().unchecked_with_facts(unfolded_facts);
    append_composite_resource_relation_facts(
        abstract_resource.resource(),
        &unfolded_resources,
        available_pure_facts,
    );

    append_state_resource_context_observable_facts(
        parameters,
        arguments,
        &state,
        available_pure_facts,
        &format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})`",
            describe_resource_clause(resource)
        ),
    )?;

    // `unfold` changes the proof representation of the final visible unit;
    // it does not itself perform the function contract's logical consumption.
    // Keep the population identity/count so execution certification and the
    // eventual resource effect can replay that transition exactly.
    let _ = (population_name, population_arguments);

    Ok(UnfoldedCompositeResource {
        state,
        body_was_already_exposed,
    })
}

/// Applies the reverse composite definition law after proving the body's pure
/// facts and consuming its immediate contained resource state.
pub(super) fn fold_composite_resources_on_outcome(
    resource_environment: &ResourceEnvironment,
    resource_folds: &[ResourceClause],
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[ExecutionPureFact],
    available_pure_facts: &[Proposition],
    surface_propositions: &SurfacePropositionMap,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    mut outcome: CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    closure: ResourceBodyClosure,
) -> Result<CFunctionOutcome, ClickError> {
    for resource in resource_folds {
        let definition = composite_resource_law_definition(
            resource_environment,
            resource,
            "fold",
            claim_label,
            path_index,
        )?;
        let composite_body = definition
            .composite_body()
            .expect("composite_resource_law_definition should require a composite body");
        let substitutions =
            resource_argument_substitutions(definition, resource, claim_label, path_index)?;
        let (guard_result, guard_state) = match &outcome {
            CFunctionOutcome::Return { value, state } => (value, state),
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}",
                    describe_resource_clause(resource),
                    describe_function_outcome(&outcome, parameters, arguments)
                )));
            }
        };
        let body_active = composite_resource_body_is_active(
            definition,
            &substitutions,
            parameters,
            arguments,
            pre_state,
            guard_state,
            guard_result,
            available_pure_facts,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}: could not select `fold({})` body: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let mut closing_view = false;
        let mut folded_representation_already_present = false;
        if closure == ResourceBodyClosure::Initialize {
            let CFunctionOutcome::Return { value, state } = &mut outcome else {
                unreachable!("the return outcome was checked above");
            };
            let population = lower_resource_clause_at_state_with_result(
                resource, parameters, arguments, state, value,
            )?;
            let (name, population_arguments) = match population.resource() {
                CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                    (name, arguments)
                }
                CResource::Memory(_) => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` did not lower to a declared resource",
                        describe_resource_clause(resource)
                    )));
                }
            };
            let assumptions = assumptions_from_propositions(available_pure_facts);
            if state.resources().satisfies_fact(&population, &assumptions) {
                // Exact execution preserves the abstract contract resource
                // while the proof may still carry its exposed body. This is
                // representation state, independent of whether the resource
                // needs a persistent population ledger.
                folded_representation_already_present = true;
            }
            if let Some(count) = state.counted_population(name, population_arguments) {
                let singleton = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(count.clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                    true,
                );
                if !assumptions.proves(&singleton) {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` can restore an existing resource population only when its count is proved equal to 1",
                        describe_resource_clause(resource)
                    )));
                }
            } else {
                *state = state.clone().with_counted_population(
                    name.clone(),
                    population_arguments.clone(),
                    Bitvector32Term::Constant(1),
                );
            }
        } else {
            let CFunctionOutcome::Return { value, state } = &outcome else {
                unreachable!("the return outcome was checked above");
            };
            let population = lower_resource_clause_at_state_with_result(
                resource, parameters, arguments, state, value,
            )?;
            let assumptions = assumptions_from_propositions(available_pure_facts);
            if !state.resources().satisfies_fact(&population, &assumptions) {
                let viewed_population = CResourceFact::View(population.resource().clone());
                closing_view = state
                    .resources()
                    .satisfies_fact(&viewed_population, &assumptions);
            }
            let (name, population_arguments) = match population.resource() {
                CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                    (name, arguments)
                }
                CResource::Memory(_) => unreachable!("declared resource lowered to memory"),
            };
            if state
                .counted_population(name, population_arguments)
                .is_none()
                && composite_body
                    .facts()
                    .iter()
                    .any(proposition_contains_resource_count)
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: closing `open({})` requires its resource population to remain active",
                    describe_resource_clause(resource)
                )));
            }
        }
        let body_facts = if body_active {
            composite_body.facts()
        } else {
            &[]
        };
        let contained_clauses = if body_active {
            composite_body.contains()
        } else {
            &[]
        };
        let mut body_fact_context = available_pure_facts.to_vec();
        body_fact_context.extend(
            execution_pure_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        let body_assumptions = assumptions_from_propositions(&body_fact_context);
        for fact in body_facts {
            let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let required = if let Some(recorded) =
                surface_propositions.available_kernel(&fact, available_pure_facts)
            {
                recorded.clone()
            } else {
                let program_point_states = ProgramPointStates::new();
                lower_ensure_proposition_goal(
                    available_pure_facts,
                    &fact,
                    parameters,
                    arguments,
                    pre_state,
                    &outcome,
                    predicate_environment,
                    click_function_environment,
                    &program_point_states,
                    unfolded_predicates,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not lower exact `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?
            };
            // Available facts may spell this body fact through loads recorded
            // at an earlier snapshot. Decide those spellings with the bounded
            // replay matchers first: exact structural membership, the
            // snapshot-bridging relation with this execution's effect facts as
            // framing, and the direct separation-fact matcher. All of these do
            // work proportional to the fact being checked, so an exactly
            // available body fact never rides on the open-ended kernel search
            // below, which can consume a large share of the fold's budget.
            let exactly_available = exact_fact_is_available_across_effects(
                &required,
                available_pure_facts,
                execution_pure_facts,
            ) || directly_matching_separation_fact_under(
                &required,
                available_pure_facts,
                &body_assumptions,
            )
            .is_some();
            if !exactly_available
                && !matches!(normalize_proposition(&required), SimpProposition::True)
                && !body_assumptions.proves(&required)
            {
                // `proves` returns false when the active budget runs out
                // mid-derivation. Reporting that truncation as a missing fact
                // is misleading, so surface the budget state itself first.
                check_verification_deadline()?;
                let resources = match &outcome {
                    CFunctionOutcome::Return { state, .. } => state.resources().facts(),
                    _ => pre_state.resources().facts(),
                };
                let required_text = describe_pure_fact(&required, parameters, arguments);
                let identically_printed = available_pure_facts
                    .iter()
                    .filter(|fact| describe_pure_fact(fact, parameters, arguments) == required_text)
                    .count();
                let snapshot_note = if identically_printed > 0 {
                    format!(
                        "\n  note: {identically_printed} available fact(s) print identically but carry different memory-snapshot spellings, and the recorded execution effects do not prove the snapshots agree at the loaded pointers"
                    )
                } else {
                    String::new()
                };
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires an exact body fact: {}{snapshot_note}",
                    describe_resource_clause(resource),
                    describe_missing_pure_fact(
                        &required,
                        available_pure_facts,
                        resources,
                        parameters,
                        arguments,
                        execution_pure_facts,
                    )
                )));
            }
        }
        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}\n  execution pure facts: {}",
                describe_resource_clause(resource),
                describe_function_outcome(&outcome, parameters, arguments),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        };
        let mut post_state = state;
        // Range spellings in held resource facts embed loads at their
        // creation snapshot; carrying them to the fold point needs the
        // execution's store effect facts alongside the pure facts.
        let mut fold_facts = available_pure_facts.to_vec();
        fold_facts.extend(
            execution_pure_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        let assumptions = assumptions_from_propositions(&fold_facts);
        let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(&assumptions);
        let mut lowered_contained = Vec::new();
        let preserve_exposed_body = matches!(
            closure,
            ResourceBodyClosure::CloseOpen {
                preserve_exposed_body: true
            }
        );
        for contained in contained_clauses {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let mut lowered = lower_resource_clause_at_state_with_result(
                &contained,
                parameters,
                arguments,
                &post_state,
                &value,
            )?;
            if preserve_exposed_body {
                // This body belonged to the active population before `open`.
                // The scope used it in place, so closing must leave that one
                // authoritative representation intact.
                continue;
            } else if closing_view {
                // A folded view already projects these duplicable view
                // cores. Opening the body makes its facts available but does
                // not create a linear representation that must be consumed
                // again when the scope closes.
                continue;
            } else if folded_representation_already_present
                && !post_state
                    .resources()
                    .satisfies_fact(&lowered, &assumptions)
            {
                // Exact execution may retain the folded contract resource
                // and downgrade its simultaneously exposed body to views.
                // Close those views when they are the representation that is
                // actually present; an absent body still fails below.
                let viewed = CResourceFact::View(lowered.resource().clone());
                if post_state.resources().satisfies_fact(&viewed, &assumptions) {
                    lowered = viewed;
                }
            }
            lowered_contained.push(lowered);
        }
        let mut resources = post_state.resources().clone();
        for lowered in lowered_contained.as_slice() {
            // Prefer consuming an equivalent whole representation. Generic
            // range consumption is allowed to treat a requirement as a
            // subrange; when the two endpoints are framed spellings from
            // different snapshots, that would leave spurious fragments.
            let directly_matching = resources.facts().iter().find(|available| {
                let quantities_match = match (available, lowered) {
                    (
                        CResourceFact::Own(_, available_quantity),
                        CResourceFact::Own(_, lowered_quantity),
                    ) => available_quantity == lowered_quantity,
                    (CResourceFact::View(_), CResourceFact::View(_)) => true,
                    _ => false,
                };
                quantities_match
                    && c_resources_directly_match(
                        available.resource(),
                        lowered.resource(),
                        &assumptions,
                    )
            });
            if let Some(directly_matching) = directly_matching.cloned() {
                resources = resources
                    .without_exact_representation(&directly_matching)
                    .expect("the directly matched resource came from this context");
                continue;
            }
            let diagnostic_facts = resources.facts().to_vec();
            let Some(next) = resources.without_fact(lowered, &assumptions) else {
                let action = match closure {
                    ResourceBodyClosure::Initialize => {
                        format!("`fold({})`", describe_resource_clause(resource))
                    }
                    ResourceBodyClosure::CloseOpen { .. } => {
                        format!("closing `open({})`", describe_resource_clause(resource))
                    }
                };
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: {action} failed: {}",
                    describe_missing_resource_fact(
                        lowered,
                        available_pure_facts,
                        &diagnostic_facts,
                        parameters,
                        arguments,
                        execution_pure_facts
                    )
                )));
            };
            resources = next;
        }
        post_state = post_state.with_resource_context(resources);

        if closure == ResourceBodyClosure::Initialize && !folded_representation_already_present {
            let abstract_resource = lower_resource_clause_at_state_with_result(
                resource,
                parameters,
                arguments,
                &post_state,
                &value,
            )?;
            let resources = post_state
                .resources()
                .clone()
                .try_compose_with_fact(abstract_resource.clone(), &assumptions)
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` produced {}",
                        describe_resource_clause(resource),
                        describe_resource_context_validity_error(error, parameters, arguments)
                    ))
                })?;
            post_state = post_state.with_resource_context(resources);
        }
        outcome = CFunctionOutcome::Return {
            value,
            state: post_state,
        };
    }

    Ok(outcome)
}

/// Resolves the source declaration that supplies fold, unfold, and observation
/// laws for a composite resource fact.
fn composite_resource_law_definition<'a>(
    resource_environment: &'a ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    claim_label: &str,
    tactic_index: usize,
) -> Result<&'a ResourceDefinition, ClickError> {
    let ResourceClause::Declared { name, .. } = resource else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects a composite resource"
        )));
    };
    if matches!(action, "fold" | "unfold")
        && !matches!(
            resource,
            ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                ..
            }
        )
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects an owned composite resource"
        )));
    }
    if !matches!(
        resource,
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            ..
        }
    ) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects resource `{name}` to have a body"
        )));
    }
    let definition = resource_environment.get(name).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown resource `{name}`"
        ))
    })?;
    if definition.composite_body().is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects composite resource `{name}` to have a body"
        )));
    }
    Ok(definition)
}

pub(super) fn resource_argument_substitutions(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    let ResourceClause::Declared {
        name,
        arguments,
        parameter_types,
        ..
    } = resource
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: expected declared resource"
        )));
    };
    if definition.name() != name {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource definition mismatch for `{name}`"
        )));
    }
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource `{name}` expects {} argument(s), got {}",
            definition.parameters().len(),
            arguments.len()
        )));
    }
    let expected_types = definition
        .parameters()
        .iter()
        .map(FunctionParameter::c_type)
        .collect::<Vec<_>>();
    if parameter_types != &expected_types {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource `{name}` has malformed argument type metadata"
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

pub(super) fn instantiate_resource_clause(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

fn instantiate_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(base, substitutions)?,
            start: substitute_contract_expression(start, substitutions)?,
            end: substitute_contract_expression(end, substitutions)?,
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
        surface,
    })
}

fn materialize_composite_resource_cells(
    mut memory: CMemory,
    resource_clause: &ResourceClause,
    lowered: &CResourceFact,
    parameters: &[syntax::C0Parameter],
) -> CMemory {
    let Some((segment, range)) = (match resource_clause {
        ResourceClause::Read(segment) => lowered.memory_view_range().map(|range| (segment, range)),
        ResourceClause::Write(segment) => lowered.memory_own_range().map(|range| (segment, range)),
        ResourceClause::Declared { .. } => None,
    }) else {
        return memory;
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (range.start(), range.end())
    else {
        return memory;
    };
    if end < start {
        return memory;
    }

    let element_width = contract_segment_element_width(parameters, segment);
    let base_memory = memory.clone();
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            range.base().clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(base_memory.clone()),
            Box::new(pointer.clone()),
        );
        let value = match element_width {
            1 => CValue::UInt8(load),
            _ => CValue::Int32(load),
        };
        memory = memory.store(pointer, value);
    }
    memory
}
