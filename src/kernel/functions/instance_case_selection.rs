//! Selecting the case of a resource instance whose body matches on its model: the matched arm, its read projections and body facts, and the checks on unmatched children.

use super::*;

/// The facts a constructor case exposes for the exact folded resource field
/// the proof matched.
///
/// This is the read-only half of an instance unfold: it binds the selected
/// arm's constructor payloads and evaluates that arm's facts against its own
/// immediate memory body, but it neither publishes the body's ownership nor
/// changes `state`.  The projection identifies one held instance directly;
/// no ambient resource or premise scan is needed.  Any mismatch or unsupported
/// body shape fails closed by publishing no facts.
pub(in crate::kernel) fn matched_resource_instance_case_clauses(
    state: &ExecutionState,
    projection: &ResourceFieldProjection,
    model: &AlgebraicTerm,
    constructor: &AlgebraicTerm,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Vec<ResourceBodyClauseRecord> {
    matched_resource_instance_case_read_projection(
        state,
        projection,
        model,
        constructor,
        definitions,
        assumptions,
    )
    .0
}

pub(super) fn matched_resource_instance_case_read_projection(
    state: &ExecutionState,
    projection: &ResourceFieldProjection,
    model: &AlgebraicTerm,
    constructor: &AlgebraicTerm,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> (Vec<ResourceBodyClauseRecord>, Vec<Proposition>) {
    if projection.at_entry {
        return (Vec::new(), Vec::new());
    }
    if !projection.children.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let Some(instance) = state.owned_resource_instance(projection.identity) else {
        return (Vec::new(), Vec::new());
    };
    let Ok(definition_index) =
        definitions.binary_search_by(|definition| definition.name().cmp(instance.name()))
    else {
        return (Vec::new(), Vec::new());
    };
    let definition = &definitions[definition_index];
    let Some(matched) = definition.matched.as_ref() else {
        return (Vec::new(), Vec::new());
    };
    if projection.field_index != matched.field_index
        || !matches!(
            instance.fields().get(projection.field_index),
            Some(AlgebraicValue::Algebraic(field_model)) if field_model == model
        )
    {
        return (Vec::new(), Vec::new());
    }
    let Ok((arm, selected_constructor)) =
        selected_instance_match_arm(instance, definition, definitions, assumptions)
    else {
        return (Vec::new(), Vec::new());
    };
    // A matched child has its own folded instance and field scope. Publishing
    // facts about it without performing the explicit child-selection rewrite
    // would conflate the parent's proof match with an ownership unfold. Keep
    // this read-only publication to flat arms; recursive arms still acquire
    // their facts through `let { ... } = unfold(parent)`.
    if !arm.children.is_empty() {
        return (Vec::new(), Vec::new());
    }
    if &selected_constructor != constructor {
        return (Vec::new(), Vec::new());
    }
    let AlgebraicTermNode::Constructor { fields, .. } = &constructor.node else {
        return (Vec::new(), Vec::new());
    };
    if fields.len() != arm.bindings.len()
        || fields.len() != arm.binding_types.len()
        || fields.len() != arm.binding_variables.len()
    {
        return (Vec::new(), Vec::new());
    }

    let Ok(mut evaluation) = instance_body_evaluation(state, instance, definition) else {
        return (Vec::new(), Vec::new());
    };
    let mut integer_bindings = BTreeMap::new();
    let mut algebraic_bindings = BTreeMap::new();
    for (index, value) in fields.iter().enumerate() {
        let name = &arm.bindings[index];
        match (
            &arm.binding_types[index],
            arm.binding_variables[index],
            value,
        ) {
            (
                AlgebraicValueType::Program(_) | AlgebraicValueType::ObjectPointer(_, _),
                None,
                AlgebraicValue::Program(value),
            ) => {
                let ty = value.program_type();
                evaluation.locals.set_typed(name.clone(), value.clone(), ty);
            }
            (AlgebraicValueType::Integer, Some(variable), AlgebraicValue::Integer(value)) => {
                if integer_bindings.insert(variable, value.clone()).is_some() {
                    return (Vec::new(), Vec::new());
                }
            }
            (AlgebraicValueType::Algebraic { .. }, None, AlgebraicValue::Algebraic(value)) => {
                algebraic_bindings.insert(name.clone(), value.clone());
            }
            _ => return (Vec::new(), Vec::new()),
        }
    }

    let mut budget = ExecutionBudget::beside_live_state();
    let Some(active) = evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut budget,
    ) else {
        return (Vec::new(), Vec::new());
    };
    if !active {
        return (Vec::new(), Vec::new());
    }
    let Ok(Ok((body_resources, _))) = evaluate_function_resource_context_with_normalization(
        &evaluation,
        &arm.contains,
        &[],
        assumptions,
        &mut budget,
        false,
    ) else {
        return (Vec::new(), Vec::new());
    };
    evaluation.resources = body_resources.clone();
    let mut supporting_facts = body_resources.observable_facts_assuming_valid(assumptions);
    for fact in body_resources.facts() {
        if let Some(coverage) = fact.allocation_bounds_fact(assumptions) {
            supporting_facts.push(coverage);
        }
        let Some(range) = fact.memory_range() else {
            continue;
        };
        supporting_facts.extend(crate::kernel::admitted_memory_range_extent_facts(range));
        supporting_facts.push(range.loadable_fact(&state.memory));
    }
    supporting_facts.push(Proposition::ResourceComposition(body_resources));
    let mut body_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    // These are state read facts and ownership containment, not child
    // ownership. They are justified only by the exact currently owned head.
    let mut read_projection = supporting_facts
        .iter()
        .filter(|fact| matches!(fact, Proposition::MemoryLoadable { .. }))
        .cloned()
        .collect::<Vec<_>>();
    for fact in evaluation.resources.facts() {
        if let Some(child) = fact.owned_resource() {
            read_projection.push(Proposition::ResourceContains {
                parent: Box::new(Resource::Instance(instance.clone())),
                child: Box::new(child.clone()),
            });
        }
    }
    for fact in supporting_facts {
        body_assumptions = body_assumptions.assume_proposition(fact);
    }

    lower_selected_resource_body_clauses(
        &evaluation,
        &arm.facts,
        Some(&arm.variant),
        &integer_bindings,
        &algebraic_bindings,
        &body_assumptions,
        None,
        &mut budget,
    )
    .map(|(records, _retained)| (records, read_projection))
    .unwrap_or_default()
}

/// The body facts of folded instances whose selected constructors are already
/// known at a call boundary.
///
/// A produced resource instance is still folded when its caller receives it,
/// but a contract ensure can state the constructor of its matched field. In
/// that case the arm's bound payloads are no longer unknown: the arm fact
/// `p->kid == kid`, for example, is a consequence of holding the instance
/// together with `link.link == Linked(kid)`. Publish that fact for the call's
/// resource transfer so an owned `child_ref(p->kid)` requirement can match the
/// caller's `child_ref(kid)` without making the proof unfold the instance.
///
/// This is read-only publication. It does not move ownership or expose the
/// arm's memory resources, and it is restricted to instances explicitly bound
/// by the selected resource call. An instance without exact constructor
/// evidence contributes nothing.
/// A returned named head carries its verified body's pure invariants. Only
/// the explicit outputs are visited, after ensures have selected their model.
/// Memory state readability and containment follow the exact owned head; no child
/// ownership or permanent view is published.
pub(super) fn checked_returned_instance_body_facts(
    outputs: &ResourceContext,
    interface: &FunctionContractInterface,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let mut publication_state = state.clone().with_resource_context(outputs.clone());
    // Outputs name actual instance identities. Contract lexical bindings map
    // source handles to those identities and must not remap them a second time.
    publication_state.resource_bindings = None;
    let state = &publication_state;
    let mut facts = Vec::new();
    let mut seen = BTreeSet::new();
    for fact in outputs.facts() {
        let ResourceFact::Own(Resource::Instance(instance), _) = fact else {
            continue;
        };
        let Some(definition) = interface.composite_resource_definition(instance.name()) else {
            continue;
        };
        let singleton =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(fact.clone());
        let publication = publish_instance_arms(
            &singleton,
            std::slice::from_ref(definition),
            state,
            assumptions,
        );
        let decided = publication
            .model_facts
            .iter()
            .cloned()
            .fold(assumptions.clone(), PureFactContext::assume_proposition);
        facts.extend(publication.model_facts);
        facts.extend(publication.arm_facts);
        let Some(matched) = definition.matched.as_ref() else {
            continue;
        };
        let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(matched.field_index)
        else {
            continue;
        };
        let Ok((_, constructor)) = selected_instance_match_arm(
            instance,
            definition,
            interface.composite_resource_definitions(),
            &decided,
        ) else {
            continue;
        };
        let projection = ResourceFieldProjection {
            identity: instance.identity(),
            children: Vec::new(),
            field_index: matched.field_index,
            at_entry: false,
        };
        let (clauses, read_projection) = matched_resource_instance_case_read_projection(
            state,
            &projection,
            model,
            &constructor,
            interface.composite_resource_definitions(),
            &decided,
        );
        facts.extend(read_projection);
        facts.extend(clauses.into_iter().filter_map(|clause| {
            (!matches!(
                clause.proposition,
                Proposition::ConditionIs(ConditionTerm::Constant(false), true)
            ))
            .then_some(clause.proposition)
        }));
    }
    // The returned owner justifies these consequences even when the caller
    // already holds them. Deduplicate this batch only; admission handles
    // existing facts without forcing the caller's deferred identity index.
    facts.retain(|fact| seen.insert(fact.clone()));
    facts
}

pub(super) fn selected_resource_instance_case_facts(
    state: &ExecutionState,
    bound_instances: Option<&BTreeMap<Variable, Variable>>,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let Some(bound_instances) = bound_instances else {
        return Vec::new();
    };
    state
        .resources()
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            Resource::Instance(instance)
                if fact.is_own() && bound_instances.values().any(|id| *id == instance.identity) =>
            {
                Some(instance)
            }
            _ => None,
        })
        .flat_map(|instance| {
            let definition = definitions
                .iter()
                .find(|definition| definition.name() == instance.name())?;
            let matched = definition.matched.as_ref()?;
            let AlgebraicValue::Algebraic(model) = instance.fields().get(matched.field_index)?
            else {
                return None;
            };
            let (_, constructor) =
                selected_instance_match_arm(instance, definition, definitions, assumptions).ok()?;
            let projection = ResourceFieldProjection {
                identity: instance.identity,
                children: Vec::new(),
                field_index: matched.field_index,
                at_entry: false,
            };
            Some(
                matched_resource_instance_case_clauses(
                    state,
                    &projection,
                    model,
                    &constructor,
                    definitions,
                    assumptions,
                )
                .into_iter()
                // A post-call heap cell may have no materialized value yet.
                // Lowering its arm equality against that incomplete state
                // can simplify it to `false`; publishing that as a premise
                // would make every subsequent obligation vacuous.
                .filter_map(|clause| {
                    (!matches!(
                        clause.proposition,
                        Proposition::ConditionIs(ConditionTerm::Constant(false), true)
                    ))
                    .then_some(clause.proposition)
                }),
            )
        })
        .flatten()
        .collect()
}

/// Values of field loads stated by the selected arm of an exactly bound,
/// owned resource instance. This is a call-local interpretation of the
/// resource invariant, not a change to C memory. Only an equality between a
/// load and a constructor C binding qualifies, and the arm must own the loaded
/// bytes. The ordinary resource transfer still has to find the requested
/// resource unit after the argument is resolved.
pub(super) fn selected_instance_resource_load_values(
    state: &ExecutionState,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> BTreeMap<(Pointer, ProgramType), ProgramValue> {
    let Some(bindings) = state.resource_bindings.as_ref() else {
        return BTreeMap::new();
    };
    let mut values = BTreeMap::new();
    let mut conflicting = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for identity in bindings.values().copied().filter(|id| seen.insert(*id)) {
        let Some(instance) = state.resources().owned_instance(identity) else {
            continue;
        };
        let Ok(index) = definitions.binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(instance.name())
        }) else {
            continue;
        };
        let definition = &definitions[index];
        let Ok((arm, constructor)) =
            selected_instance_match_arm(instance, definition, definitions, assumptions)
        else {
            continue;
        };
        let AlgebraicTermNode::Constructor { fields, .. } = &constructor.node else {
            continue;
        };
        // Only the selected arm's parameter and constructor bindings are
        // needed. A whole caller-state clone here would charge every call
        // for unrelated live resources.
        let Some(mut evaluation) = (|| {
            if definition.parameters.len() != instance.arguments().len() {
                return None;
            }
            let mut evaluation = ExecutionState::new().with_memory(state.memory().clone());
            for (parameter, argument) in definition.parameters.iter().zip(instance.arguments()) {
                let value = argument.as_program_value()?;
                if value.program_type() != parameter.program_type() {
                    return None;
                }
                evaluation.locals.set_typed(
                    parameter.name().to_owned(),
                    value.clone(),
                    parameter.program_type(),
                );
            }
            Some(evaluation)
        })() else {
            continue;
        };
        if fields.len() != arm.bindings.len() {
            continue;
        }
        for (name, field) in arm.bindings.iter().zip(fields) {
            if let AlgebraicValue::Program(value) = field {
                evaluation
                    .locals
                    .set_typed(name.clone(), value.clone(), value.program_type());
            }
        }
        let mut budget = ExecutionBudget::beside_live_state();
        let mut owned_memory = ResourceContext::new_with_equalities(assumptions);
        for resource in &arm.contains {
            let Ok(Ok(fact @ ResourceFact::Own(Resource::Memory(_), _))) =
                evaluate_function_resource_spec(&evaluation, resource, assumptions, &mut budget)
            else {
                continue;
            };
            owned_memory = owned_memory.unchecked_with_fact(fact);
        }
        for fact in &arm.facts {
            let SpecProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = fact
            else {
                continue;
            };
            let candidate = [(left, right), (right, left)]
                .into_iter()
                .find_map(|(load, value)| {
                    let SpecExpression::MemoryLoad {
                        memory: SpecMemory::Current,
                        pointer,
                        value_type,
                    } = load
                    else {
                        return None;
                    };
                    let SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) =
                        value
                    else {
                        return None;
                    };
                    if !arm.bindings.contains(name) {
                        return None;
                    }
                    let value = evaluation.locals.get(name)?.clone().into_native();
                    if !value_type.accepts(&value) {
                        return None;
                    }
                    let paths =
                        crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
                            &evaluation,
                            pointer,
                            None,
                            assumptions,
                            &mut budget,
                        )
                        .ok()?;
                    let [path] = paths.as_slice() else {
                        return None;
                    };
                    if !path.obligations.is_empty() {
                        return None;
                    }
                    let native = path.value.native();
                    let ProgramValue::Pointer(address) = native.as_ref() else {
                        return None;
                    };
                    resource_context_has_read(
                        &owned_memory,
                        address.pointer(),
                        value_type.byte_width(),
                        assumptions,
                    )
                    .then(|| ((address.pointer().clone(), *value_type), value))
                });
            let Some((key, value)) = candidate else {
                continue;
            };
            if conflicting.contains(&key) {
                continue;
            }
            if values.get(&key).is_some_and(|previous| previous != &value) {
                values.remove(&key);
                conflicting.insert(key);
            } else {
                values.insert(key, value);
            }
        }
    }
    values
}

/// Checks the named children of an unmatched instance body against their own
/// definitions. Each is of another family, since an unmatched body has no
/// submodel to descend to, and each field is the parent's field of the same
/// type. The work is this body's children and their schemas.
pub(super) fn check_unmatched_instance_children(
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    definitions: &[CompositeResourceDefinition],
) -> Result<(), &'static str> {
    let mut names = BTreeSet::new();
    let mut bindings = BTreeSet::new();
    let reserved = definition
        .parameters
        .iter()
        .map(|parameter| parameter.name())
        .chain(
            instance
                .schema()
                .fields()
                .iter()
                .map(|(name, _)| name.as_str()),
        )
        .collect::<BTreeSet<_>>();
    for child in &definition.children {
        crate::instrumentation::record_deterministic_work(1);
        if child.resource == definition.name() {
            return Err("an unmatched resource body cannot own a child of its own family");
        }
        let child_definition = child_composite_definition(definition, definitions, child)?;
        let child_schema = child_definition
            .instance_schema
            .as_ref()
            .ok_or("resource child requires a field-bearing definition")?;
        if child.name.is_empty()
            || reserved.contains(child.name.as_str())
            || !names.insert(child.name.as_str())
            || child.binding == Variable(u64::MAX)
            || !bindings.insert(child.binding)
            || child.arguments.len() != child_definition.parameters.len()
            || child.field_bindings.len() != child_schema.fields().len()
            || child_schema.fields().iter().zip(&child.field_bindings).any(
                |((_, field_type), source)| match source {
                    ResourceChildField::Parent(index) => {
                        instance.schema().fields().get(*index).map(|(_, ty)| ty) != Some(field_type)
                    }
                    ResourceChildField::Constructor(_) => true,
                },
            )
        {
            return Err("invalid resource child schema");
        }
    }
    Ok(())
}

/// Whether an instance body's unnamed clauses can move as a whole on fold and
/// unfold: owned memory and owned, field-free declared resources. A declared
/// resource stays folded inside the body, exactly as the parent's caller
/// would hold it. Quantities use the ordinary checked resource evaluation
/// and exact consumption rules; views cannot be exchanged as ownership.
pub(super) fn instance_body_clauses_are_exchangeable(contains: &[ResourceSpec]) -> bool {
    contains.iter().all(|body| {
        !body.is_view()
            && match body.family() {
                ResourceFamily::Parameter => false,
                ResourceFamily::Memory
                | ResourceFamily::Iterated
                | ResourceFamily::MutexGuard
                | ResourceFamily::MutexLive
                | ResourceFamily::MutexUse => true,
                ResourceFamily::Composite
                | ResourceFamily::Token
                | ResourceFamily::PopulationAuthority => true,
                // A publication right is not yet held inside a resource body.
                ResourceFamily::Instance | ResourceFamily::Publication => false,
            }
    })
}

pub(in crate::kernel) fn selected_instance_match_arm<'a>(
    instance: &ResourceInstance,
    definition: &'a CompositeResourceDefinition,
    definitions: &'a [CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<(&'a ResourceMatchArm, AlgebraicTerm), &'static str> {
    let body = definition
        .matched
        .as_ref()
        .ok_or("missing resource match body")?;
    if definition.condition.is_some()
        || !definition.contains.is_empty()
        || !definition.children.is_empty()
        || !definition.facts.is_empty()
        || !body.algebraic_type.has_consistent_root_schema()
        || body.algebraic_type.rigid
        || instance
            .schema()
            .fields()
            .get(body.field_index)
            .map(|(_, ty)| ty)
            != Some(&ResourceFieldType::Algebraic(body.algebraic_type.clone()))
        || body.arms.len() != body.algebraic_type.variants.len()
    {
        return Err("invalid resource match schema");
    }
    let mut variants = BTreeSet::new();
    let schema_variants = body
        .algebraic_type
        .variants
        .iter()
        .map(|variant| (variant.name.as_str(), &variant.fields))
        .collect::<BTreeMap<_, _>>();
    let reserved = definition
        .parameters
        .iter()
        .map(|parameter| parameter.name())
        .chain(
            instance
                .schema()
                .fields()
                .iter()
                .map(|(name, _)| name.as_str()),
        )
        .collect::<BTreeSet<_>>();
    for arm in &body.arms {
        let mut names = BTreeSet::new();
        if !variants.insert(&arm.variant)
            || schema_variants
                .get(arm.variant.as_str())
                .is_none_or(|fields| {
                    **fields != arm.binding_types
                        || fields.len() != arm.bindings.len()
                        || arm.binding_variables.len() != arm.bindings.len()
                })
            || arm.bindings.iter().any(|name| {
                name.is_empty() || !names.insert(name) || reserved.contains(name.as_str())
            })
            || arm.binding_variables.iter().zip(&arm.binding_types).any(
                |(variable, binding_type)| match binding_type {
                    AlgebraicValueType::Integer => variable.is_none(),
                    _ => variable.is_some(),
                },
            )
            || !instance_body_clauses_are_exchangeable(&arm.contains)
        {
            return Err("invalid resource match arm");
        }
        let mut integer_binding_variables = BTreeSet::new();
        for (variable, binding_type) in arm.binding_variables.iter().zip(&arm.binding_types) {
            if binding_type == &AlgebraicValueType::Integer
                && !integer_binding_variables.insert(variable.expect("checked above"))
            {
                return Err("resource match Integer bindings reuse an identity");
            }
        }
        let mut child_names = BTreeSet::new();
        let mut child_bindings = BTreeSet::new();
        for child in &arm.children {
            // A child is checked against its own definition, which is the
            // parent's for a directly recursive child and another declared
            // resource otherwise.
            let child_definition = child_composite_definition(definition, definitions, child)?;
            let child_schema = if child_definition.name() == definition.name() {
                instance.schema()
            } else {
                child_definition
                    .instance_schema
                    .as_ref()
                    .ok_or("resource match child requires a field-bearing definition")?
            };
            if child.name.is_empty()
                || reserved.contains(child.name.as_str())
                || names.contains(&child.name)
                || !child_names.insert(&child.name)
                || child.binding == Variable(u64::MAX)
                || !child_bindings.insert(child.binding)
                || child.arguments.len() != child_definition.parameters.len()
                || child.field_bindings.len() != child_schema.fields().len()
            {
                return Err("invalid recursive child schema");
            }
            for ((_, field_type), source) in child_schema.fields().iter().zip(&child.field_bindings)
            {
                let matches = match source {
                    ResourceChildField::Constructor(index) => {
                        let expected = match field_type {
                            ResourceFieldType::Integer => AlgebraicValueType::Integer,
                            ResourceFieldType::Program(ty) => AlgebraicValueType::Program(*ty),
                            ResourceFieldType::Algebraic(ty) => ty.value_type(),
                        };
                        arm.binding_types.get(*index) == Some(&expected)
                    }
                    ResourceChildField::Parent(index) => {
                        instance.schema().fields().get(*index).map(|(_, ty)| ty) == Some(field_type)
                    }
                };
                if !matches {
                    return Err(
                        "recursive child fields must be immediate constructor bindings of the declared type",
                    );
                }
            }
            // In particular, a same-family child's model is bound to a field
            // of this constructor, never to the whole parent model or to a
            // parent field. A child of another family has no such field; its
            // own matched field is already checked above, against its own
            // declared type.
            if child_definition.name() == definition.name()
                && !matches!(
                    child.field_bindings[body.field_index],
                    ResourceChildField::Constructor(index)
                        if arm.binding_types.get(index)
                            == Some(&body.algebraic_type.value_type())
                )
            {
                return Err("recursive child model must be a proper submodel");
            }
        }
    }
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Err("resource match field is not algebraic");
    };
    // Fold and unfold bind the arm's fields, so they need the constructor
    // itself: an arm merely entailed by the premises (D7) grants reading, not
    // the values a rewrite would substitute.
    let Some(ResourceModelArmSelection::Constructor(constructor)) =
        select_resource_model_arm(model, assumptions)
    else {
        return Err("resource match requires constructor evidence for the instance field");
    };
    let AlgebraicTermNode::Constructor { variant, .. } = &constructor.node else {
        unreachable!()
    };
    let arm = body
        .arms
        .iter()
        .find(|arm| &arm.variant == variant)
        .ok_or("unknown resource match constructor")?;
    Ok((arm, constructor))
}

/// Which arm of a matched resource model one section's premises select.
///
/// `Constructor` carries the model's own constructor application, so the arm's
/// bindings have values. `Variant` names the arm without naming its fields:
/// the premises rule out every other variant, or witness this one, but no
/// premise says what it holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceModelArmSelection {
    Constructor(AlgebraicTerm),
    Variant(String),
}

impl ResourceModelArmSelection {
    pub fn variant(&self) -> &str {
        match self {
            Self::Constructor(constructor) => match &constructor.node {
                AlgebraicTermNode::Constructor { variant, .. } => variant,
                _ => unreachable!("a selected constructor term is a constructor application"),
            },
            Self::Variant(variant) => variant,
        }
    }
}

/// What one frontier's premises say about a matched resource model: the arm
/// they select, the arms they leave possible, or nothing.
///
/// `Possible` carries two or more variants, so a caller never has to ask a
/// second question to tell "one arm" from "several": `Selected` is the answer
/// that grants an arm's own cells and facts, `Possible` the answer that grants
/// only what every survivor agrees on, and `Open` the answer that grants
/// nothing and keeps the instance folded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceModelArmDecision {
    Selected(ResourceModelArmSelection),
    Possible(Vec<String>),
    Open,
}

/// The one arm decision in Click: premises plus constructor exhaustiveness
/// against one matched model value.
///
/// Every frontier that decides a matched instance's arms reaches this
/// function, through [`publish_instance_arms`] for a whole context or through
/// [`select_resource_model_arm`] for one model. Contract lowering asks it for
/// a `requires`-selected arm; a loop head asks the same question with its
/// invariants playing the part of the requirements, and a fold or unfold asks
/// it through [`selected_instance_match_arm`], which needs the stronger
/// `Constructor` answer because it binds the arm's fields.
///
/// The answer is decided, never searched: a constructor premise answers
/// outright, an existential premise witnesses one variant, and disequalities
/// against field-free constructors rule variants out. One variant left is
/// `Selected`; two or more, with at least one ruled out, is `Possible`; any
/// other state of evidence is `Open`. A context that has ruled out every
/// declared variant is inconsistent and not this decision's business to
/// exploit, so it is `Open` too.
///
/// Cost is the number of premises about this exact value plus the declared
/// variants of its type. Unrelated premises are never visited.
pub fn decide_resource_model_arm(
    model: &AlgebraicTerm,
    assumptions: &PureFactContext,
) -> ResourceModelArmDecision {
    if let Some(constructor) = assumptions.known_algebraic_constructor(model) {
        return ResourceModelArmDecision::Selected(ResourceModelArmSelection::Constructor(
            constructor,
        ));
    }
    let AlgebraicTermNode::Variable(variable) = &model.node else {
        return ResourceModelArmDecision::Open;
    };
    let declared = model
        .algebraic_type
        .variants
        .iter()
        .map(|variant| variant.name.as_str())
        .collect::<BTreeSet<_>>();
    if declared.is_empty() {
        return ResourceModelArmDecision::Open;
    }
    let mut witnessed = BTreeMap::new();
    let mut excluded = BTreeMap::new();
    for (premise, evidence) in assumptions.algebraic_variant_evidence(*variable) {
        if !declared.contains(evidence.variant.as_str()) {
            continue;
        }
        match evidence.kind {
            AlgebraicVariantEvidenceKind::Witnessed => {
                witnessed.insert(evidence.variant.as_str(), premise);
            }
            AlgebraicVariantEvidenceKind::Excluded => {
                excluded.insert(evidence.variant.as_str(), premise);
            }
        }
    }
    // A witness names its arm directly. Two witnesses would need the context
    // to be inconsistent, which is not this decision's business to exploit.
    // Cite what decided the arm, so an expansion of the selected arm names the
    // premises a reader would look for.
    if let [(variant, premise)] = witnessed.iter().collect::<Vec<_>>().as_slice() {
        super::super::assumptions::record_reasoning_provenance(assumptions, premise);
        return ResourceModelArmDecision::Selected(ResourceModelArmSelection::Variant(
            (**variant).to_owned(),
        ));
    }
    if !witnessed.is_empty() {
        return ResourceModelArmDecision::Open;
    }
    let excluded_variants = excluded.keys().copied().collect::<BTreeSet<_>>();
    let possible = declared
        .difference(&excluded_variants)
        .copied()
        .collect::<Vec<_>>();
    let decision = match possible.as_slice() {
        [] => return ResourceModelArmDecision::Open,
        [only] => ResourceModelArmDecision::Selected(ResourceModelArmSelection::Variant(
            (*only).to_owned(),
        )),
        _ if excluded.is_empty() => return ResourceModelArmDecision::Open,
        several => ResourceModelArmDecision::Possible(
            several
                .iter()
                .map(|variant| (*variant).to_owned())
                .collect(),
        ),
    };
    for premise in excluded.values() {
        super::super::assumptions::record_reasoning_provenance(assumptions, premise);
    }
    decision
}

/// The arm one frontier's premises select, when they select exactly one.
///
/// A thin reading of [`decide_resource_model_arm`]: the callers that can only
/// act on a decided arm — a fold, an unfold, a termination measure — ask this
/// one instead of matching the three-way answer.
pub fn select_resource_model_arm(
    model: &AlgebraicTerm,
    assumptions: &PureFactContext,
) -> Option<ResourceModelArmSelection> {
    match decide_resource_model_arm(model, assumptions) {
        ResourceModelArmDecision::Selected(selection) => Some(selection),
        ResourceModelArmDecision::Possible(_) | ResourceModelArmDecision::Open => None,
    }
}

pub(in crate::kernel) fn instance_body_evaluation(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
) -> Result<ExecutionState, &'static str> {
    let mut evaluation = state.clone();
    {
        // A local interpretation of proposed fields, never ownership or a
        // persistent open handle. Guards may refer to these fields as well.
        evaluation.instance_field_scope = evaluation
            .instance_field_scope
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone())));
    }
    if definition.matched.is_some() {
        // An arm's C names are lexical parameters and constructor bindings,
        // never incidental locals of the function currently opening it.
        evaluation.locals = LocalEnvironment::default();
    }
    evaluation.resource_bindings = Some(std::sync::Arc::new(BTreeMap::from([(
        Variable(u64::MAX),
        instance.identity,
    )])));
    // A C-typed field is stable model data of this instance, so the body may
    // name it wherever it may name a matched constructor payload: as a memory
    // endpoint or a child argument. The binding is the instance's own field
    // value, proposed on fold and published on unfold. Parameters are bound
    // afterwards and keep their own names; the surface refuses a field that
    // shares one. The work is this instance's own schema.
    for ((name, _), value) in instance
        .schema()
        .fields()
        .iter()
        .zip(instance.fields.iter())
    {
        if let AlgebraicValue::Program(value) = value {
            evaluation
                .locals
                .bind_logical_typed(name.clone(), value.clone(), value.program_type());
        }
    }
    for (parameter, value) in definition.parameters.iter().zip(instance.arguments.iter()) {
        let value = value
            .as_program_value()
            .ok_or("resource argument is not a C value")?;
        if value.program_type() != parameter.program_type() {
            return Err("resource argument type mismatch");
        }
        evaluation.locals.bind_logical_typed(
            parameter.name().to_owned(),
            value.clone(),
            parameter.program_type(),
        );
    }
    Ok(evaluation)
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/instance_case_selection.rs");
}
