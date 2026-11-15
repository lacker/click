//! Expanding composite resources into their member facts and instantiating composite and population propositions at a state.

use super::*;

/// Whether a composite fact names the base of `pointer` among its pointer
/// arguments by structure: the same pointer, or one that `pointer` is a
/// constant offset from.
pub(super) fn composite_names_pointer_base(composite: &ResourceFact, pointer: &Pointer) -> bool {
    let Resource::Composite { arguments, .. } = composite.resource() else {
        return false;
    };
    arguments.iter().any(|argument| {
        let AlgebraicValue::Program(ProgramValue::Pointer(argument)) = argument else {
            return false;
        };
        argument.pointer() == pointer
            || pointer
                .shared_element_index_from_base_with_width(argument.pointer(), 1)
                .is_some()
    })
}

pub(super) fn expand_composite_resource_context(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<ResourceFact>)> {
    let mut expanded = context.clone();
    let mut composites = Vec::new();
    let roots = context.composite_facts().cloned().collect::<Vec<_>>();
    for root in roots {
        expanded = expand_composite_resource_tree(
            &expanded,
            &root,
            definitions,
            memory,
            assumptions,
            &[],
            &mut composites,
        )?;
    }
    Some((expanded, composites))
}

pub(super) fn expand_composite_resource_tree(
    context: &ResourceContext,
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    assumptions: &PureFactContext,
    ancestors: &[String],
    composites: &mut Vec<ResourceFact>,
) -> Option<ResourceContext> {
    if !context.facts().contains(composite) {
        return Some(context.clone());
    }
    let Resource::Composite { name, .. } = composite.resource() else {
        return Some(context.clone());
    };
    let definition = &definitions[definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        })
        .ok()?];
    if definition.is_recursive() && ancestors.iter().any(|ancestor| ancestor == name) {
        return Some(context.clone());
    }
    let (mut expanded, children, _) = expand_composite_resource_fact_with_children(
        context,
        composite,
        definitions,
        memory,
        assumptions,
    )?;
    if expanded.facts().contains(composite) {
        return Some(expanded);
    }
    composites.push(composite.clone());
    let mut child_ancestors = ancestors.to_vec();
    child_ancestors.push(name.clone());
    for child in children {
        if matches!(child.resource(), Resource::Composite { .. }) {
            expanded = expand_composite_resource_tree(
                &expanded,
                &child,
                definitions,
                memory,
                assumptions,
                &child_ancestors,
                composites,
            )?;
        }
    }
    Some(expanded)
}

pub(in crate::kernel) fn expand_all_composite_resource_facts_and_propositions_at_state(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<Proposition>)> {
    expand_all_composite_resource_facts_and_propositions_with_state(
        context,
        definitions,
        state.memory(),
        assumptions,
        Some(state),
    )
}

pub(super) fn expand_all_composite_resource_facts_and_propositions_with_state(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    assumptions: &PureFactContext,
    population_state: Option<&ExecutionState>,
) -> Option<(ResourceContext, Vec<Proposition>)> {
    let (prepared, mut controls) = if let Some(state) = population_state {
        expand_checked_authority_controls(context, definitions, state, assumptions)?
    } else {
        (context.clone(), Vec::new())
    };
    let (expanded, composites) =
        expand_composite_resource_context(&prepared, definitions, memory, assumptions)?;
    controls.extend(composites);
    let mut propositions = Vec::new();
    // `assumptions` extended by `propositions[..extended]`: each composite's
    // facts are evaluated under every proposition before them, and the
    // context grows by the new ones instead of being rebuilt per composite.
    let mut fact_assumptions = assumptions.clone();
    let mut extended = 0;
    for composite in controls {
        // Preserve the bounds of each declared leaf before adjacent resources
        // normalize into a larger range. The proof can cite either slice.
        let loadable = evaluate_composite_resource_loadable_propositions(
            &composite,
            definitions,
            memory,
            assumptions,
        )?;
        propositions.extend(loadable);
        let relations = if let Some(state) = population_state
            && let Resource::Composite { name, .. } = composite.resource()
            && let Some(definition) = definitions
                .iter()
                .find(|definition| definition.name() == name)
            && definition
                .contains()
                .iter()
                .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
        {
            let (children, _) = state
                .checked_authority_wrapper_body(&composite, definition, assumptions)
                .ok()?;
            let child_context = ResourceContext::new()
                .try_compose_with_facts(children.clone(), assumptions)
                .ok()?;
            let mut relations = vec![Proposition::ResourceComposition(child_context)];
            for child in children {
                if let Some(owned) = child.owned_resource() {
                    relations.push(Proposition::ResourceContains {
                        parent: Box::new(composite.resource().clone()),
                        child: Box::new(owned.clone()),
                    });
                }
            }
            relations
        } else {
            evaluate_composite_resource_relation_propositions(
                &composite,
                definitions,
                memory,
                assumptions,
            )?
        };
        propositions.extend(relations);
        fact_assumptions =
            assumptions_with_propositions(&fact_assumptions, &propositions[extended..]);
        extended = propositions.len();
        let instantiated = instantiate_composite_resource_facts_with_state(
            &composite,
            definitions,
            memory,
            &expanded,
            &fact_assumptions,
            population_state,
        )?;
        propositions.extend(instantiated.propositions);
    }
    Some((expanded, propositions))
}

pub(in crate::kernel) fn evaluate_resource_population_fact_propositions(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    let mut populations = BTreeSet::<(String, ResourceArguments)>::new();
    for fact in context.facts() {
        let (name, arguments) = match fact.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                continue;
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                (name, arguments)
            }
            Resource::Memory(_)
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_) => continue,
        };
        if fact.owned_quantity_term().is_some() {
            populations.insert((name.clone(), arguments.clone()));
        }
    }
    let mut propositions = Vec::<Proposition>::new();
    for (name, arguments) in populations {
        let Some(definition) = definitions
            .iter()
            .find(|definition| definition.name() == name)
        else {
            continue;
        };
        if definition.parameters().len() != arguments.len() {
            return None;
        }
        // Resource expansion checks ownership relations, but a composite's
        // declared pure facts must also be checked from the kernel-side body
        // state. A body with no facts has no additional proposition to
        // validate here.
        if definition.facts().is_empty() {
            continue;
        }
        let body_active = {
            let mut population_state = state.clone();
            for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                let argument = argument.as_program_value()?;
                if parameter.program_type() != argument.program_type() {
                    return None;
                }
                population_state.locals.set_typed(
                    parameter.name().to_string(),
                    argument.clone(),
                    parameter.program_type(),
                );
            }
            bind_composite_witnesses(definition, &arguments, &mut population_state, assumptions)?;
            let mut budget = ExecutionBudget::beside_live_state();
            let evaluation_assumptions = assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .prefer_symbolic_external_loads()
                // Opening a held composite assumes the body its fold established.
                .assume_entry_clause_extents()
                .assume_held_resource_domains();
            match evaluate_composite_resource_body_condition(
                definition,
                &population_state,
                &evaluation_assumptions,
                &mut budget,
            ) {
                Some(active) => active,
                None => continue,
            }
        };
        let mut population_state = state.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let argument = argument.as_program_value()?;
            if parameter.program_type() != argument.program_type() {
                return None;
            }
            population_state.locals.set_typed(
                parameter.name().to_string(),
                argument.clone(),
                parameter.program_type(),
            );
        }
        bind_composite_witnesses(definition, &arguments, &mut population_state, assumptions)?;
        let mut budget = ExecutionBudget::beside_live_state();
        let evaluation_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads()
            // Opening a held composite assumes the body its fold established.
            .assume_entry_clause_extents()
            .assume_held_resource_domains();
        if !body_active {
            continue;
        }
        // Definition facts are justified by the population body, even while
        // that body is opaque in the surface proof context. Expose the body
        // only in this kernel-local state so heap-dependent invariants can
        // discharge their own loadability obligations.
        if definition
            .contains()
            .iter()
            .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
        {
            let head = ResourceFact::own(Resource::Composite {
                name: name.clone(),
                arguments: arguments.clone(),
            });
            let (projected, _) = match population_state.checked_authority_wrapper_projection(
                &head,
                definition,
                &evaluation_assumptions,
            ) {
                Ok(projected) => projected,
                Err(_) => return None,
            };
            population_state.resources = projected;
        } else {
            for contained in definition.contains() {
                let body_resource = evaluate_function_resource_spec(
                    &population_state,
                    contained,
                    &evaluation_assumptions,
                    &mut budget,
                )
                .ok()?
                .ok()?;
                if !population_state
                    .resources
                    .satisfies_fact(&body_resource, &evaluation_assumptions)
                {
                    population_state.resources = population_state
                        .resources
                        .try_compose_with_facts_delaying_normalization(
                            [body_resource],
                            &evaluation_assumptions,
                        )
                        .ok()?;
                }
            }
        }
        let mut fact_assumptions = assumptions.clone();
        let mut pending = definition.facts().iter().enumerate().collect::<Vec<_>>();
        while !pending.is_empty() {
            let mut next_pending = Vec::new();
            let mut made_progress = false;
            for (fact_index, population_fact) in pending {
                let evaluation_assumptions = fact_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
                    // Opening a held composite assumes the body its fold established.
                    .assume_entry_clause_extents()
                    .assume_held_resource_domains();
                // Resource-definition loadability facts are symbolic summaries;
                // their owning range supplies the concrete validity check when
                // the resource is used. Do not turn an unconstrained summary
                // endpoint into a failed definition during population setup.
                let Ok(paths) = lower_spec_proposition_at_state_without_range_guards(
                    &population_state,
                    population_fact,
                    None,
                    &evaluation_assumptions,
                    &mut budget,
                ) else {
                    return None;
                };
                let [path] = paths.as_slice() else {
                    next_pending.push((fact_index, population_fact));
                    continue;
                };
                if !path.obligations.iter().all(|obligation| {
                    if required_obligation_is_exactly_discharged(
                        &fact_assumptions,
                        obligation.proposition(),
                    ) {
                        return true;
                    }
                    let Proposition::MemoryLoadable {
                        memory: obligation_memory,
                        base,
                        bytes,
                        wide: false,
                    } = obligation.proposition()
                    else {
                        return false;
                    };
                    memory_states_proven_equal_at_pointer(
                        obligation_memory,
                        population_state.memory(),
                        base,
                        &fact_assumptions,
                    ) && bytes.as_const().is_some_and(|bytes| {
                        resource_context_has_read(
                            population_state.resources(),
                            base,
                            bytes,
                            &fact_assumptions,
                        )
                    })
                }) {
                    next_pending.push((fact_index, population_fact));
                    continue;
                }
                for obligation in &path.obligations {
                    fact_assumptions =
                        fact_assumptions.assume_proposition(obligation.proposition().clone());
                }
                for path_fact in &path.facts {
                    let proposition = path_fact.proposition().clone();
                    if !propositions.contains(&proposition) {
                        propositions.push(proposition.clone());
                    }
                    fact_assumptions = fact_assumptions.assume_proposition(proposition);
                }
                if !propositions.contains(&path.proposition) {
                    propositions.push(path.proposition.clone());
                }
                fact_assumptions = fact_assumptions.assume_proposition(path.proposition.clone());
                made_progress = true;
            }
            if !made_progress {
                return None;
            }
            pending = next_pending;
        }
    }
    Some(propositions)
}

pub(in crate::kernel) fn evaluate_composite_resource_relation_propositions(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    let Resource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = ExecutionState::new().with_memory(memory.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_program_value()?;
        if parameter.program_type() != argument.program_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // Opening a held composite assumes the body its fold established.
        .assume_entry_clause_extents()
        .assume_held_resource_domains();
    let mut child_facts = Vec::new();
    let mut children = Vec::new();
    let body_active = evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )?;
    for contained in if body_active {
        definition.contains()
    } else {
        &[]
    } {
        let child_result = evaluate_function_resource_spec(
            &state,
            contained,
            &evaluation_assumptions,
            &mut budget,
        );
        let Ok(Ok(child)) = child_result else {
            return None;
        };
        state.resources = state.resources.clone().unchecked_with_fact(child.clone());
        if composite.is_own()
            && let Some(owned_child) = child.owned_resource()
        {
            children.push(owned_child.clone());
        }
        child_facts.push(child);
    }
    let mut propositions = Vec::new();
    if composite.is_own() {
        // The child context is the compact authority for ownership-derived
        // separation. Publishing one carrier lets certification answer
        // member-pair queries on demand instead of materializing O(N^2)
        // `ResourceSeparate` propositions.
        let child_context = ResourceContext::new()
            .try_compose_with_facts(child_facts, assumptions)
            .ok()?;
        propositions.push(Proposition::ResourceComposition(child_context));
    }
    for child in &children {
        propositions.push(Proposition::ResourceContains {
            parent: Box::new(composite.resource().clone()),
            child: Box::new(child.clone()),
        });
    }
    Some(propositions)
}

/// The held body's exact ranges, including their pointer designations and
/// selected extents. Later clauses may read the cells declared before them
/// in a scratch view context; the caller's composite remains folded.
pub(in crate::kernel) fn evaluate_composite_resource_memory_ranges(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    assumptions: &PureFactContext,
) -> Option<Vec<MemoryRange>> {
    let Resource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = ExecutionState::new().with_memory(memory.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_program_value()?;
        if parameter.program_type() != argument.program_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // Opening a held composite assumes the body its fold established.
        .assume_entry_clause_extents()
        .assume_held_resource_domains();
    if !evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )? {
        return Some(Vec::new());
    }

    let mut ranges = Vec::new();
    let mut clauses = definition
        .contains()
        .iter()
        .filter(|resource| resource.memory_segment().is_some())
        .peekable();
    while let Some(resource) = clauses.next() {
        let outcome =
            evaluate_function_resource_spec(&state, resource, &evaluation_assumptions, &mut budget);
        let evaluated = match outcome.ok()? {
            Ok(resource) => resource,
            Err(_) => return None,
        };
        let range = evaluated.memory_range()?;
        ranges.push(range.clone());
        // Later body cells may be addressed through this one. The held
        // composite already supplies its declared cell; expose only a view
        // in this scratch evaluation, leaving the actual head folded.
        if clauses.peek().is_some() {
            state.resources = state
                .resources
                .clone()
                .unchecked_with_fact(ResourceFact::view_memory(range.clone()));
        }
    }
    Some(ranges)
}

pub(in crate::kernel) fn evaluate_composite_resource_loadable_propositions(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    let ranges =
        evaluate_composite_resource_memory_ranges(composite, definitions, memory, assumptions)?;
    let mut propositions = Vec::new();
    for range in ranges {
        propositions.extend(crate::kernel::admitted_memory_range_extent_facts(&range));
        propositions.push(range.loadable_fact(memory));
    }
    Some(propositions)
}

pub(in crate::kernel) fn evaluate_composite_resource_fact_propositions(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    instantiate_composite_resource_facts(composite, definitions, memory, resources, assumptions)
        .map(|instantiated| instantiated.propositions)
}

/// One state-specific instantiation of the resource's already-lowered
/// definition. The indexed declared facts retain source correspondence for
/// presentation, without lowering the Click source a second time.
pub(crate) struct InstantiatedCompositeResourceFacts {
    pub(crate) propositions: Vec<Proposition>,
    pub(crate) declared: Vec<(usize, Proposition)>,
}

pub(crate) fn instantiate_composite_resource_facts(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<InstantiatedCompositeResourceFacts> {
    instantiate_composite_resource_facts_with_state(
        composite,
        definitions,
        memory,
        resources,
        assumptions,
        None,
    )
}

/// Private member invariants may read only their own body, even when the
/// ambient proof owns other memory. Otherwise opening one member after an
/// unrelated write could publish a false current invariant.
pub(crate) fn instantiate_private_member_body_facts(
    composite: &ResourceFact,
    definition: &CompositeResourceDefinition,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<InstantiatedCompositeResourceFacts> {
    let memory = state.memory();
    let definitions = std::slice::from_ref(definition);
    let singleton = ResourceContext::new().unchecked_with_fact(composite.clone());
    let body =
        expand_composite_resource_fact(&singleton, composite, definitions, memory, assumptions)?;
    // Keep the current verification model and population state, but bind only
    // this definition's parameters. Mutating a cloned caller-local map would
    // copy the whole frame for every member fact instantiation.
    let mut fact_state = state.clone();
    fact_state.locals = LocalEnvironment::new();
    instantiate_composite_resource_facts_with_state(
        composite,
        definitions,
        memory,
        &body,
        &assumptions.clone().require_owned_expression_loads(),
        Some(&fact_state),
    )
}

pub(super) fn instantiate_composite_resource_facts_with_state(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &Memory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
    population_state: Option<&ExecutionState>,
) -> Option<InstantiatedCompositeResourceFacts> {
    let Resource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = population_state
        .cloned()
        .unwrap_or_else(ExecutionState::new)
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_program_value()?;
        if parameter.program_type() != argument.program_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut result = Vec::new();
    let mut declared = Vec::new();
    let mut budget = ExecutionBudget::beside_live_state();
    let mut fact_assumptions = assumptions.clone();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // Opening a held composite assumes the body its fold established.
        .assume_entry_clause_extents()
        .assume_held_resource_domains();
    if !evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )? {
        return Some(InstantiatedCompositeResourceFacts {
            propositions: result,
            declared,
        });
    }
    let mut pending = definition.facts().iter().enumerate().collect::<Vec<_>>();
    while !pending.is_empty() {
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for (index, fact) in pending {
            let evaluation_assumptions = fact_assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .prefer_symbolic_external_loads()
                // Opening a held composite assumes the body its fold established.
                .assume_entry_clause_extents()
                .assume_held_resource_domains();
            // Resource-definition loadability facts are symbolic summaries;
            // their owning range supplies the concrete validity check when
            // the resource is used. Do not turn an unconstrained summary
            // endpoint into a failed definition during population setup.
            let Ok(paths) = lower_spec_proposition_at_state_without_range_guards(
                &state,
                fact,
                None,
                &evaluation_assumptions,
                &mut budget,
            ) else {
                return None;
            };
            let [path] = paths.as_slice() else {
                next_pending.push((index, fact));
                continue;
            };
            if !path.obligations.iter().all(|obligation| {
                if required_obligation_is_exactly_discharged(
                    &fact_assumptions,
                    obligation.proposition(),
                ) {
                    return true;
                }
                let Proposition::MemoryLoadable {
                    memory: obligation_memory,
                    base,
                    bytes,
                    wide: false,
                } = obligation.proposition()
                else {
                    return false;
                };
                memory_states_proven_equal_at_pointer(
                    obligation_memory,
                    memory,
                    base,
                    &fact_assumptions,
                ) && bytes.as_const().is_some_and(|bytes| {
                    resource_context_has_read(resources, base, bytes, &fact_assumptions)
                })
            }) {
                next_pending.push((index, fact));
                continue;
            }
            for obligation in &path.obligations {
                fact_assumptions =
                    fact_assumptions.assume_proposition(obligation.proposition().clone());
            }
            for path_fact in &path.facts {
                let proposition = path_fact.proposition().clone();
                if !result.contains(&proposition) {
                    result.push(proposition.clone());
                }
                fact_assumptions = fact_assumptions.assume_proposition(proposition);
            }
            if !result.contains(&path.proposition) {
                result.push(path.proposition.clone());
            }
            declared.push((
                definition.fact_source_index(index)?,
                path.proposition.clone(),
            ));
            fact_assumptions = fact_assumptions.assume_proposition(path.proposition.clone());
            made_progress = true;
        }
        if !made_progress {
            return None;
        }
        pending = next_pending;
    }
    Some(InstantiatedCompositeResourceFacts {
        propositions: result,
        declared,
    })
}
