use super::*;

pub(in crate::lang::click) fn unfold_structural_invariant_proposition(
    predicate_environment: &PredicateEnvironment,
    proposition: &ClickProposition,
    unfolded_predicates: &[String],
) -> Result<ClickProposition, String> {
    if unfolded_predicates.is_empty() {
        return Ok(proposition.clone());
    }

    for name in unfolded_predicates {
        if predicate_environment.get(name).is_none() {
            return Err(format!("unknown predicate `{name}`"));
        }
    }

    let mut active = BTreeSet::new();
    unfold_click_predicates_in_proposition_with_active(
        predicate_environment,
        unfolded_predicates,
        proposition,
        &mut active,
    )
}

pub(in crate::lang::click) fn unfold_click_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    unfolded_predicates: &[String],
    proposition: &ClickProposition,
    active: &mut BTreeSet<String>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::PredicateCall { name, arguments }
            if unfolded_predicates
                .iter()
                .any(|predicate| predicate == name) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_click_predicate_definition(definition, arguments)?;
            let unfolded = unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                &unfolded,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: left.clone(),
            operator: *operator,
            right: right.clone(),
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: left.clone(),
            right: right.clone(),
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: parent.clone(),
            child: child.clone(),
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: segment.clone(),
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: expression.clone(),
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                proposition,
                active,
            )?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::ForAll { c_type, name, body } => Ok(ClickProposition::ForAll {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::Exists { c_type, name, body } => Ok(ClickProposition::Exists {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments.clone(),
            })
        }
    }
}

pub(in crate::lang::click) fn instantiate_click_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
) -> Result<ClickProposition, String> {
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "predicate `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }

    let substitutions = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect::<BTreeMap<_, _>>();
    substitute_click_proposition(definition.body(), &substitutions)
}

pub(in crate::lang::click) fn substitute_click_proposition(
    proposition: &ClickProposition,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: substitute_contract_expression(left, substitutions)?,
            operator: *operator,
            right: substitute_contract_expression(right, substitutions)?,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: substitute_resource_subject(left, substitutions)?,
            right: substitute_resource_subject(right, substitutions)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: substitute_resource_subject(parent, substitutions)?,
            child: substitute_resource_subject(child, substitutions)?,
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: substitute_contract_segment(segment, substitutions)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: substitute_contract_expression(expression, substitutions)?,
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(substitute_click_proposition(proposition, substitutions)?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            substitute_click_proposition(body, substitutions)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::ForAll { c_type, name, body } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(item);
            Ok(ClickProposition::RangeAll {
                start: substitute_contract_expression(start, substitutions)?,
                end: substitute_contract_expression(end, substitutions)?,
                item: item.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(item);
            Ok(ClickProposition::RangeAny {
                start: substitute_contract_expression(start, substitutions)?,
                end: substitute_contract_expression(end, substitutions)?,
                item: item.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_contract_expression(argument, substitutions))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    }
}

fn substitute_contract_segment(
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

fn substitute_resource_subject(
    resource: &ResourceSubject,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceSubject, String> {
    match resource {
        ResourceSubject::Memory(segment) => Ok(ResourceSubject::Memory(
            substitute_contract_segment(segment, substitutions)?,
        )),
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceSubject::Declared {
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

pub(in crate::lang::click) fn apply_contract_lets_to_requirement(
    requirement: Requirement,
    bindings: &[ContractLetBinding],
) -> Result<Requirement, String> {
    match requirement {
        Requirement::Labeled { label, requirement } => Ok(Requirement::Labeled {
            label,
            requirement: Box::new(apply_contract_lets_to_requirement(*requirement, bindings)?),
        }),
        Requirement::LoadableSegment { segment } => Ok(Requirement::LoadableSegment {
            segment: apply_contract_lets_to_segment(segment, bindings)?,
        }),
        Requirement::Resource(resource) => Ok(Requirement::Resource(
            apply_contract_lets_to_resource_clause(resource, bindings)?,
        )),
        Requirement::Proposition(proposition) => Ok(Requirement::Proposition(
            apply_contract_lets_to_proposition(proposition, bindings)?,
        )),
    }
}

pub(in crate::lang::click) fn apply_contract_lets_to_ensure_clause(
    clause: EnsureClause,
    bindings: &[ContractLetBinding],
) -> Result<EnsureClause, String> {
    let EnsureClause {
        name,
        ensure,
        proof,
    } = clause;
    let ensure = match ensure {
        Ensure::Proposition(proposition) => {
            Ensure::Proposition(apply_contract_lets_to_proposition(proposition, bindings)?)
        }
        Ensure::Resource(resource) => {
            Ensure::Resource(apply_contract_lets_to_resource_clause(resource, bindings)?)
        }
    };
    Ok(EnsureClause {
        name,
        ensure,
        proof,
    })
}

pub(in crate::lang::click) fn apply_contract_lets_to_resource_clause(
    resource: ResourceClause,
    bindings: &[ContractLetBinding],
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(apply_contract_lets_to_segment(
            segment, bindings,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access,
            kind,
            name,
            arguments: arguments
                .into_iter()
                .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types,
        }),
    }
}

fn apply_contract_lets_to_resource_subject(
    resource: ResourceSubject,
    bindings: &[ContractLetBinding],
) -> Result<ResourceSubject, String> {
    match resource {
        ResourceSubject::Memory(segment) => Ok(ResourceSubject::Memory(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceSubject::Declared {
            kind,
            name,
            arguments: arguments
                .into_iter()
                .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types,
        }),
    }
}

pub(in crate::lang::click) fn apply_contract_lets_to_effect_clause(
    clause: EffectClause,
    bindings: &[ContractLetBinding],
) -> Result<EffectClause, String> {
    let EffectClause { effect, proof } = clause;
    Ok(EffectClause {
        effect: apply_contract_lets_to_effect(effect, bindings)?,
        proof,
    })
}

pub(in crate::lang::click) fn apply_contract_lets_to_effect(
    effect: Effect,
    bindings: &[ContractLetBinding],
) -> Result<Effect, String> {
    match effect {
        Effect::Immutable => Ok(Effect::Immutable),
        Effect::Mutable(segments) => Ok(Effect::Mutable(
            segments
                .into_iter()
                .map(|segment| apply_contract_lets_to_segment(segment, bindings))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

pub(in crate::lang::click) fn apply_contract_lets_to_segment(
    segment: ContractSegment,
    bindings: &[ContractLetBinding],
) -> Result<ContractSegment, String> {
    let substitutions = contract_let_substitutions(bindings);
    let surface = match segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(&base, &substitutions)?,
            start: substitute_contract_expression(&start, &substitutions)?,
            end: substitute_contract_expression(&end, &substitutions)?,
        },
        surface => surface,
    };
    let segment = ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, &substitutions)?,
        start: substitute_c_fragment(&segment.start, &substitutions)?,
        end: substitute_c_fragment(&segment.end, &substitutions)?,
        surface,
    };
    reject_contract_where_let_references(
        &contract_segment_referenced_names(&segment),
        bindings,
        "memory segment expressions",
    )?;
    Ok(segment)
}

pub(in crate::lang::click) fn reject_contract_where_let_references(
    referenced_names: &BTreeSet<String>,
    bindings: &[ContractLetBinding],
    context: &str,
) -> Result<(), String> {
    if let Some(binding) = bindings.iter().find(|binding| {
        binding.where_condition().is_some() && referenced_names.contains(&binding.name)
    }) {
        return Err(format!(
            "`let ... where` `{}` cannot be used in {context} yet",
            binding.name
        ));
    }
    Ok(())
}

pub(in crate::lang::click) fn apply_contract_lets_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    let proposition = apply_contract_let_expressions_to_proposition(proposition, bindings)?;
    wrap_contract_where_lets_proposition(proposition, bindings)
}

pub(in crate::lang::click) fn apply_contract_let_expressions_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: apply_contract_lets_to_expression(left, bindings)?,
            operator,
            right: apply_contract_lets_to_expression(right, bindings)?,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: apply_contract_lets_to_resource_subject(left, bindings)?,
            right: apply_contract_lets_to_resource_subject(right, bindings)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: apply_contract_lets_to_resource_subject(parent, bindings)?,
            child: apply_contract_lets_to_resource_subject(child, bindings)?,
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: apply_contract_lets_to_segment(segment, bindings)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: apply_contract_lets_to_expression(expression, bindings)?,
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector,
            proposition: Box::new(apply_contract_let_expressions_to_proposition(
                *proposition,
                bindings,
            )?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            apply_contract_let_expressions_to_proposition(*body, bindings)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::ForAll { c_type, name, body } => {
            let scoped = contract_lets_without_name(bindings, &name);
            Ok(ClickProposition::ForAll {
                c_type,
                name,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            let scoped = contract_lets_without_name(bindings, &name);
            Ok(ClickProposition::Exists {
                c_type,
                name,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            Ok(ClickProposition::RangeAll {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            Ok(ClickProposition::RangeAny {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    }
}

pub(in crate::lang::click) fn wrap_contract_where_lets_proposition(
    mut proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    for (index, binding) in bindings.iter().enumerate().rev() {
        let Some(condition) = binding.where_condition() else {
            continue;
        };
        let condition =
            apply_contract_let_expressions_to_proposition(condition.clone(), &bindings[..index])?;
        let Some(c_type) = binding.c_type else {
            return Err(format!(
                "`let ... where` `{}` requires an explicit type annotation",
                binding.name
            ));
        };
        proposition = ClickProposition::Exists {
            c_type,
            name: binding.name.clone(),
            body: Box::new(ClickProposition::And(
                Box::new(condition),
                Box::new(proposition),
            )),
        };
    }
    Ok(proposition)
}

pub(in crate::lang::click) fn apply_contract_lets_to_expression(
    expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> Result<ContractExpression, String> {
    let referenced_names = contract_expression_referenced_names(&expression);
    let referenced_bindings = bindings
        .iter()
        .filter(|binding| binding.value().is_some() && referenced_names.contains(&binding.name))
        .cloned()
        .collect::<Vec<_>>();
    let substitutions = contract_let_substitutions(bindings);
    let expression = substitute_contract_expression(&expression, &substitutions)?;
    Ok(wrap_contract_lets_expression(
        expression,
        &referenced_bindings,
    ))
}

pub(in crate::lang::click) fn wrap_contract_lets_expression(
    mut expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> ContractExpression {
    for binding in bindings.iter().rev() {
        let Some(value) = binding.value() else {
            continue;
        };
        expression = ContractExpression::Let {
            name: binding.name.clone(),
            c_type: binding.c_type,
            value: Box::new(value.clone()),
            body: Box::new(expression),
        };
    }
    expression
}

pub(in crate::lang::click) fn contract_lets_without_name(
    bindings: &[ContractLetBinding],
    name: &str,
) -> Vec<ContractLetBinding> {
    bindings
        .iter()
        .filter(|binding| binding.name != name)
        .cloned()
        .collect()
}

pub(in crate::lang::click) fn contract_expression_referenced_names(
    expression: &ContractExpression,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_contract_expression_referenced_names(expression, &mut names);
    names
}

pub(in crate::lang::click) fn collect_contract_expression_referenced_names(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::CFragment(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        ContractExpression::Field { base, .. } => {
            collect_contract_expression_referenced_names(base, names);
        }
        ContractExpression::CBinding(name) => {
            names.insert(name.clone());
        }
        ContractExpression::Old(expression) | ContractExpression::BitwiseNot(expression) => {
            collect_contract_expression_referenced_names(expression, names);
        }
        ContractExpression::At { expression, .. } => {
            collect_contract_expression_referenced_names(expression, names);
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_proposition_referenced_names(condition, names);
            collect_contract_expression_referenced_names(then_branch, names);
            collect_contract_expression_referenced_names(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            collect_contract_expression_referenced_names(initial, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_names(body, &mut body_names);
            body_names.remove(accumulator);
            body_names.remove(item);
            names.extend(body_names);
        }
        ContractExpression::Let {
            name, value, body, ..
        } => {
            collect_contract_expression_referenced_names(value, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_names(body, &mut body_names);
            body_names.remove(name);
            names.extend(body_names);
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(in crate::lang::click) fn collect_click_proposition_referenced_names(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ClickProposition::Separate { left, right } => {
            collect_resource_subject_referenced_names(left, names);
            collect_resource_subject_referenced_names(right, names);
        }
        ClickProposition::Contains { parent, child } => {
            collect_resource_subject_referenced_names(parent, names);
            collect_resource_subject_referenced_names(child, names);
        }
        ClickProposition::Loadable { segment } => {
            names.extend(contract_segment_referenced_names(segment));
        }
        ClickProposition::Defined { expression } => {
            collect_contract_expression_referenced_names(expression, names);
        }
        ClickProposition::At { proposition, .. } => {
            collect_click_proposition_referenced_names(proposition, names);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_proposition_referenced_names(left, names);
            collect_click_proposition_referenced_names(right, names);
        }
        ClickProposition::Not(body) => collect_click_proposition_referenced_names(body, names),
        ClickProposition::ForAll { name, body, .. }
        | ClickProposition::Exists { name, body, .. } => {
            let mut body_names = BTreeSet::new();
            collect_click_proposition_referenced_names(body, &mut body_names);
            body_names.remove(name);
            names.extend(body_names);
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            let mut body_names = BTreeSet::new();
            collect_click_proposition_referenced_names(body, &mut body_names);
            body_names.remove(item);
            names.extend(body_names);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(in crate::lang::click) fn contract_let_substitutions(
    bindings: &[ContractLetBinding],
) -> BTreeMap<String, ContractExpression> {
    bindings
        .iter()
        .filter_map(|binding| {
            binding
                .value()
                .map(|value| (binding.name.clone(), value.clone()))
        })
        .collect()
}

pub(in crate::lang::click) fn substitute_contract_expression(
    expression: &ContractExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractExpression, String> {
    match expression {
        ContractExpression::CBinding(_) => Ok(expression.clone()),
        ContractExpression::CFragment(CExpression::Variable(name)) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| expression.clone())),
        ContractExpression::CFragment(expression) => {
            substitute_c_fragment_as_contract(expression, substitutions)
        }
        ContractExpression::Field {
            base,
            field,
            lowered,
        } => Ok(ContractExpression::Field {
            base: Box::new(substitute_contract_expression(base, substitutions)?),
            field: field.clone(),
            lowered: substitute_c_fragment(lowered, substitutions)?,
        }),
        ContractExpression::Old(expression) => Ok(ContractExpression::Old(Box::new(
            substitute_contract_expression(expression, substitutions)?,
        ))),
        ContractExpression::At {
            selector,
            expression,
        } => Ok(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(substitute_contract_expression(expression, substitutions)?),
        }),
        ContractExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_contract_expression(expression, substitutions)?,
        ))),
        ContractExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_contract_expression(base, substitutions)?),
            Box::new(substitute_contract_expression(index, substitutions)?),
        )),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => Ok(ContractExpression::If {
            condition: Box::new(substitute_click_proposition(condition, substitutions)?),
            then_branch: Box::new(substitute_contract_expression(then_branch, substitutions)?),
            else_branch: Box::new(substitute_contract_expression(else_branch, substitutions)?),
        }),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(accumulator);
            scoped.remove(item);
            Ok(ContractExpression::RangeFold {
                start: Box::new(substitute_contract_expression(start, substitutions)?),
                end: Box::new(substitute_contract_expression(end, substitutions)?),
                initial: Box::new(substitute_contract_expression(initial, substitutions)?),
                accumulator: accumulator.clone(),
                item: item.clone(),
                body: Box::new(substitute_contract_expression(body, &scoped)?),
            })
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ContractExpression::Let {
                name: name.clone(),
                c_type: *c_type,
                value: Box::new(substitute_contract_expression(value, substitutions)?),
                body: Box::new(substitute_contract_expression(body, &scoped)?),
            })
        }
        ContractExpression::Call { name, arguments } => Ok(ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

pub(in crate::lang::click) fn substitute_c_fragment_as_contract(
    expression: &CExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractExpression, String> {
    match expression {
        CExpression::Value(_) => Ok(ContractExpression::CFragment(expression.clone())),
        CExpression::Variable(name) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ContractExpression::CFragment(expression.clone()))),
        CExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_c_fragment_as_contract(expression, substitutions)?,
        ))),
        CExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_c_fragment_as_contract(base, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(index, substitutions)?),
        )),
        _ => Ok(ContractExpression::CFragment(substitute_c_fragment(
            expression,
            substitutions,
        )?)),
    }
}

pub(in crate::lang::click) fn substitute_c_fragment(
    expression: &CExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<CExpression, String> {
    match expression {
        CExpression::Value(_) => Ok(expression.clone()),
        CExpression::Variable(name) => {
            let Some(substitution) = substitutions.get(name) else {
                return Ok(expression.clone());
            };
            contract_expression_as_c_fragment(substitution).ok_or_else(|| {
                format!(
                    "cannot substitute non-C-fragment expression for `{name}` inside C fragment `{expression:?}`"
                )
            })
        }
        CExpression::AddressOf(body) => Ok(CExpression::AddressOf(Box::new(
            substitute_c_fragment(body, substitutions)?,
        ))),
        CExpression::PointerOffsetBytes { pointer, bytes } => Ok(CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_c_fragment(pointer, substitutions)?),
            bytes: *bytes,
        }),
        CExpression::LessThan(left, right) => Ok(CExpression::LessThan(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::LessEqual(left, right) => Ok(CExpression::LessEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::GreaterThan(left, right) => Ok(CExpression::GreaterThan(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::GreaterEqual(left, right) => Ok(CExpression::GreaterEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Equal(left, right) => Ok(CExpression::Equal(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::NotEqual(left, right) => Ok(CExpression::NotEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Not(body) => Ok(CExpression::Not(Box::new(substitute_c_fragment(
            body,
            substitutions,
        )?))),
        CExpression::And(left, right) => Ok(CExpression::And(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Or(left, right) => Ok(CExpression::Or(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            substitute_c_fragment(expression, substitutions)?,
        ))),
        CExpression::Load(body) => Ok(CExpression::Load(Box::new(substitute_c_fragment(
            body,
            substitutions,
        )?))),
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => Ok(CExpression::TypedLoad {
            pointer: Box::new(substitute_c_fragment(pointer, substitutions)?),
            value_type: *value_type,
        }),
        CExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(substitute_c_fragment(base, substitutions)?),
            Box::new(substitute_c_fragment(index, substitutions)?),
        )),
    }
}

pub(in crate::lang::click) fn contract_expression_as_c_fragment(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Field { lowered, .. } => Some(lowered.clone()),
        ContractExpression::CBinding(name) => Some(CExpression::Variable(name.clone())),
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(CExpression::BitwiseNot(Box::new(
            contract_expression_as_c_fragment(expression)?,
        ))),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_as_c_fragment(base)?),
            Box::new(contract_expression_as_c_fragment(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

pub(in crate::lang::click) fn c_comparison_operator(
    operator: ComparisonOperator,
) -> CComparisonOperator {
    match operator {
        ComparisonOperator::Equal => CComparisonOperator::Equal,
        ComparisonOperator::NotEqual => CComparisonOperator::NotEqual,
        ComparisonOperator::LessThan => CComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => CComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => CComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => CComparisonOperator::GreaterEqual,
    }
}

pub(in crate::lang::click) fn contract_expression_to_c_fragment(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Field { lowered, .. } => Some(lowered.clone()),
        ContractExpression::CBinding(name) => Some(CExpression::Variable(name.clone())),
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(CExpression::BitwiseNot(Box::new(
            contract_expression_to_c_fragment(expression)?,
        ))),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_to_c_fragment(base)?),
            Box::new(contract_expression_to_c_fragment(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}
