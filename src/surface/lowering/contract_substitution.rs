use super::*;
use crate::kernel::{bits32_constant, constant_u32};
use std::borrow::Cow;
use std::sync::Arc;

pub(in crate::surface) fn unfold_surface_predicates(
    predicate_environment: &PredicateEnvironment,
    proposition: &ClickProposition,
    selected_definitions: &[String],
) -> Result<ClickProposition, String> {
    for name in selected_definitions {
        if predicate_environment.get(name).is_none() {
            return Err(format!("unknown predicate `{name}`"));
        }
    }

    unfold_selected_predicates_in_proposition(
        predicate_environment,
        &|name| selected_definitions.contains(name),
        proposition,
        &mut BTreeSet::new(),
        false,
    )
}

pub(in crate::surface) fn unfold_click_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    selected_definitions: &[String],
    proposition: &ClickProposition,
    active: &mut BTreeSet<String>,
) -> Result<ClickProposition, String> {
    unfold_selected_predicates_in_proposition(
        predicate_environment,
        &|name| {
            selected_definitions
                .iter()
                .any(|predicate| predicate == name)
        },
        proposition,
        active,
        true,
    )
}

/// Uses the caller's membership index without exporting its unfolding history.
pub(in crate::surface) fn unfold_selected_predicates_in_proposition(
    predicate_environment: &PredicateEnvironment,
    selected: &impl Fn(&String) -> bool,
    proposition: &ClickProposition,
    active: &mut BTreeSet<String>,
    recursive: bool,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Value(expression) => {
            let reduced = lambdas::reduce_head_fully(expression)?;
            if let ContractExpression::Proposition(body) = reduced.as_ref() {
                unfold_selected_predicates_in_proposition(
                    predicate_environment,
                    selected,
                    body,
                    active,
                    recursive,
                )
            } else {
                Ok(ClickProposition::Value(reduced.into_owned()))
            }
        }

        ClickProposition::PredicateCall { name, arguments } if selected(name) => {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_click_predicate_definition(definition, arguments)?;
            let unfolded = if recursive {
                unfold_selected_predicates_in_proposition(
                    predicate_environment,
                    selected,
                    &unfolded,
                    active,
                    true,
                )?
            } else {
                unfolded
            };
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
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => Ok(ClickProposition::FloatClassification {
            expression: expression.clone(),
            classification: *classification,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: left.clone(),
            right: right.clone(),
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: parent.clone(),
            child: child.clone(),
        }),
        ClickProposition::ResourceViewable { resource } => Ok(ClickProposition::ResourceViewable {
            resource: resource.clone(),
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: segment.clone(),
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: expression.clone(),
        }),
        ClickProposition::IsA { class, pointer } => Ok(ClickProposition::IsA {
            class: class.clone(),
            pointer: pointer.clone(),
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                proposition,
                active,
                recursive,
            )?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                left,
                active,
                recursive,
            )?),
            Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                right,
                active,
                recursive,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                left,
                active,
                recursive,
            )?),
            Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                right,
                active,
                recursive,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                body,
                active,
                recursive,
            )?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                left,
                active,
                recursive,
            )?),
            Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                right,
                active,
                recursive,
            )?),
        )),
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::ForAll {
            click_type: interface_type.clone(),
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                body,
                active,
                recursive,
            )?),
        }),
        ClickProposition::Exists {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::Exists {
            click_type: interface_type.clone(),
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                body,
                active,
                recursive,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            written_item: written_item.clone(),
            body: Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                body,
                active,
                recursive,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            written_item: written_item.clone(),
            body: Box::new(unfold_selected_predicates_in_proposition(
                predicate_environment,
                selected,
                body,
                active,
                recursive,
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

pub(in crate::surface) fn instantiate_click_predicate_definition(
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

    // Surface-only rewriting may not carry the surrounding C type
    // environment (for example `same(value, value)`). Kernel unfolding
    // independently reconstructs and checks the concrete instance from its
    // typed arguments. Keep the generic surface body when syntax alone cannot
    // recover the instance; parameter substitution can still eliminate every
    // generic binding from bodies such as `left == right`.
    let instantiated;
    let definition = match generics::instantiate_predicate_for_surface_call(
        definition,
        arguments,
        &BTreeMap::new(),
    ) {
        Ok(value) => {
            instantiated = value;
            &instantiated
        }
        Err(_) => definition,
    };
    let substitutions = definition
        .parameters()
        .iter()
        .zip(arguments)
        // Retain the call's declared machine conversion in its surface body,
        // just as pure function unfolding does. In particular, a range bound
        // must not infer its binder type from the literal's original type.
        .map(|(parameter, argument)| {
            (
                parameter.name().to_string(),
                pure_function_parameter_argument(parameter, argument),
            )
        })
        .collect::<BTreeMap<_, _>>();
    substitute_click_proposition(definition.body(), &substitutions)
}

/// Substitutes into a proposition. A `&BTreeMap` of value substitutions
/// converts on its own; a caller whose pass also renames resource instances
/// builds a [`ContractSubstitutions`] and passes that.
///
/// Throughout the substitution family, the `_in` twin of an entry point takes
/// an already-built pass: that is what the recursion uses, and what a caller
/// holding a `&ContractSubstitutions` calls.
pub(in crate::surface) fn substitute_click_proposition<'a>(
    proposition: &ClickProposition,
    substitutions: impl Into<ContractSubstitutions<'a>>,
) -> Result<ClickProposition, String> {
    substitute_click_proposition_in(proposition, &substitutions.into())
}

pub(in crate::surface) fn substitute_click_proposition_in(
    proposition: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ClickProposition, String> {
    if substitutions.source.is_some() {
        let mut names = BTreeSet::<crate::kernel::BindingName>::new();
        collect_click_proposition_referenced_bindings(proposition, &mut names);
        let selected = substitutions.selected(names);
        return substitute_click_proposition_in(proposition, &selected);
    }

    match proposition {
        proposition @ (ClickProposition::At { .. }
        | ClickProposition::And(..)
        | ClickProposition::Or(..)
        | ClickProposition::Not(..)
        | ClickProposition::Implies(..)) => {
            substitute_click_proposition_logical(proposition, substitutions)
        }
        proposition => substitute_click_proposition_nonlogical(proposition, substitutions),
    }
}

#[inline(never)]
fn substitute_click_proposition_logical(
    proposition: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ClickProposition, String> {
    let mut pending = vec![(proposition, false)];
    let mut values = Vec::new();
    while let Some((proposition, finish)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if finish {
            let right = values.pop().expect("a logical child was substituted");
            let value = match proposition {
                ClickProposition::At { selector, .. } => ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(right),
                },
                ClickProposition::Not(_) => ClickProposition::Not(Box::new(right)),
                ClickProposition::And(..)
                | ClickProposition::Or(..)
                | ClickProposition::Implies(..) => {
                    let left = values
                        .pop()
                        .expect("both logical children were substituted");
                    let (left, right) = (Box::new(left), Box::new(right));
                    match proposition {
                        ClickProposition::And(..) => ClickProposition::And(left, right),
                        ClickProposition::Or(..) => ClickProposition::Or(left, right),
                        ClickProposition::Implies(..) => ClickProposition::Implies(left, right),
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!("only logical nodes have a finish frame"),
            };
            values.push(value);
            continue;
        }
        match proposition {
            ClickProposition::At {
                proposition: body, ..
            }
            | ClickProposition::Not(body) => {
                pending.push((proposition, true));
                pending.push((body, false));
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push((proposition, true));
                pending.push((right, false));
                pending.push((left, false));
            }
            proposition => values.push(substitute_click_proposition_nonlogical(
                proposition,
                substitutions,
            )?),
        }
    }
    Ok(values
        .pop()
        .expect("the selected proposition was substituted"))
}

fn substitute_click_proposition_nonlogical(
    proposition: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Value(expression) => Ok(ClickProposition::Value(
            substitute_contract_expression_in(expression, substitutions)?,
        )),

        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: substitute_contract_expression_in(left, substitutions)?,
            operator: *operator,
            right: substitute_contract_expression_in(right, substitutions)?,
        }),
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => Ok(ClickProposition::FloatClassification {
            expression: substitute_contract_expression_in(expression, substitutions)?,
            classification: *classification,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: substitute_resource_subject(left, substitutions)?,
            right: substitute_resource_subject(right, substitutions)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: substitute_resource_subject(parent, substitutions)?,
            child: substitute_resource_subject(child, substitutions)?,
        }),
        ClickProposition::ResourceViewable { resource } => Ok(ClickProposition::ResourceViewable {
            resource: substitute_resource_subject(resource, substitutions)?,
        }),
        ClickProposition::Loadable { segment } => {
            // A saved array argument is a Surface pointer expression. Keep
            // current-memory viewability through that saved pointer rather
            // than forcing it back into a C-only segment spelling.
            match substitute_resource_subject(
                &ResourceSubject::Memory(segment.clone()),
                substitutions,
            )? {
                ResourceSubject::Memory(segment) => Ok(ClickProposition::Loadable { segment }),
                resource => Ok(ClickProposition::ResourceViewable { resource }),
            }
        }
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: substitute_contract_expression_in(expression, substitutions)?,
        }),
        ClickProposition::IsA { class, pointer } => Ok(ClickProposition::IsA {
            class: class.clone(),
            pointer: substitute_contract_expression_in(pointer, substitutions)?,
        }),
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => {
            let scoped = substitutions.without_binding(name);
            let original_name = name.clone();
            let (name, body) = prepare_click_proposition_binding_body(name, body, &scoped)?;
            Ok(ClickProposition::ForAll {
                click_type: interface_type.clone(),
                written_name: written_name.clone().or_else(|| {
                    (name != original_name)
                        .then(|| original_name.written().map(str::to_owned))
                        .flatten()
                }),
                name,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => {
            let scoped = substitutions.without_binding(name);
            let original_name = name.clone();
            let (name, body) = prepare_click_proposition_binding_body(name, body, &scoped)?;
            Ok(ClickProposition::Exists {
                click_type: interface_type.clone(),
                written_name: written_name.clone().or_else(|| {
                    (name != original_name)
                        .then(|| original_name.written().map(str::to_owned))
                        .flatten()
                }),
                name,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => {
            let scoped = substitutions.without_binding(item);
            let original_item = item.clone();
            let (item, body) = prepare_click_proposition_binding_body(item, body, &scoped)?;
            let written_item = written_item.clone().or_else(|| {
                (item != original_item)
                    .then(|| original_item.written().map(str::to_owned))
                    .flatten()
            });
            Ok(ClickProposition::RangeAll {
                start: substitute_contract_expression_in(start, substitutions)?,
                end: substitute_contract_expression_in(end, substitutions)?,
                item,
                written_item,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => {
            let scoped = substitutions.without_binding(item);
            let original_item = item.clone();
            let (item, body) = prepare_click_proposition_binding_body(item, body, &scoped)?;
            let written_item = written_item.clone().or_else(|| {
                (item != original_item)
                    .then(|| original_item.written().map(str::to_owned))
                    .flatten()
            });
            Ok(ClickProposition::RangeAny {
                start: substitute_contract_expression_in(start, substitutions)?,
                end: substitute_contract_expression_in(end, substitutions)?,
                item,
                written_item,
                body: Box::new(body),
            })
        }
        ClickProposition::PredicateCall { name, .. }
            if crate::kernel::TerminationAtomKind::from_spelling(name).is_some() =>
        {
            Ok(proposition.clone())
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_contract_expression_in(argument, substitutions))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        _ => unreachable!("logical proposition dispatched to nonlogical substitution"),
    }
}

fn prepare_click_proposition_binding_body(
    binder: &SurfaceBinder,
    body: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<(SurfaceBinder, ClickProposition), String> {
    if !substitutions_reference_name(substitutions, binder) {
        return Ok((
            binder.clone(),
            substitute_click_proposition_in(body, substitutions)?,
        ));
    }
    let fresh = SurfaceBinder::fresh();
    let mut scoped = substitutions.clone();
    scoped.insert_value(binder.clone(), fresh.reference());
    Ok((fresh, substitute_click_proposition_in(body, &scoped)?))
}
fn prepare_contract_expression_binding_body(
    binder: &SurfaceBinder,
    body: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<(SurfaceBinder, ContractExpression), String> {
    if !substitutions_reference_name(substitutions, binder) {
        return Ok((
            binder.clone(),
            substitute_contract_expression_in(body, substitutions)?,
        ));
    }
    let fresh = SurfaceBinder::fresh();
    let mut scoped = substitutions.clone();
    scoped.insert_value(binder.clone(), fresh.reference());
    Ok((fresh, substitute_contract_expression_in(body, &scoped)?))
}
fn prepare_contract_range_fold_body(
    accumulator: &SurfaceBinder,
    item: &SurfaceBinder,
    body: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<(SurfaceBinder, SurfaceBinder, ContractExpression), String> {
    let mut scoped = substitutions.clone();
    let fresh_acc = if substitutions_reference_name(substitutions, accumulator) {
        let fresh = SurfaceBinder::fresh();
        scoped.insert_value(accumulator.clone(), fresh.reference());
        fresh
    } else {
        accumulator.clone()
    };
    let fresh_item = if item == accumulator {
        fresh_acc.clone()
    } else if substitutions_reference_name(substitutions, item) {
        let fresh = SurfaceBinder::fresh();
        scoped.insert_value(item.clone(), fresh.reference());
        fresh
    } else {
        item.clone()
    };
    Ok((
        fresh_acc,
        fresh_item,
        substitute_contract_expression_in(body, &scoped)?,
    ))
}

/// Only live replacements in this arm can capture its payload binders.
fn prepare_contract_match_arm(
    arm: &AlgebraicMatchArm,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<AlgebraicMatchArm, String> {
    let mut scoped = substitutions.clone();
    for name in &arm.bindings {
        scoped = scoped.without_binding(name);
    }
    let mut captures = BTreeSet::new();
    for name in contract_expression_referenced_bindings(&arm.body) {
        if let Some(references) = scoped.references.get(&name) {
            captures.extend(references.iter().cloned());
        }
    }
    let bindings = arm
        .bindings
        .iter()
        .map(|name| {
            if !captures.contains(&name.kernel_name()) {
                return name.clone();
            }
            let fresh = SurfaceBinder::fresh();
            scoped.insert_value(name.clone(), fresh.reference());
            fresh
        })
        .collect();
    Ok(AlgebraicMatchArm {
        bindings,
        body: substitute_contract_expression_in(&arm.body, &scoped)?,
        type_name: arm.type_name.clone(),
        variant: arm.variant.clone(),
    })
}

fn substitutions_reference_name(
    substitutions: &ContractSubstitutions<'_>,
    name: &SurfaceBinder,
) -> bool {
    substitutions
        .free_references
        .contains_key(&name.kernel_name())
}

pub(in crate::surface) fn rewrite_click_proposition_by_surface_equality(
    proposition: &ClickProposition,
    equality: &ClickProposition,
) -> Option<ClickProposition> {
    rewrite_surface_equality_candidate(proposition, equality, false)
}

// A current native value can differ from its historical reading even when
// both use the same variable spelling. Offer this bounded alternative when
// the ordinary candidate does not present the checked kernel rewrite.
pub(in crate::surface) fn rewrite_surface_equality_preserving_states(
    proposition: &ClickProposition,
    equality: &ClickProposition,
) -> Option<ClickProposition> {
    rewrite_surface_equality_candidate(proposition, equality, true)
}

fn rewrite_surface_equality_candidate(
    proposition: &ClickProposition,
    equality: &ClickProposition,
    preserve_states: bool,
) -> Option<ClickProposition> {
    let (left, right) = surface_equality_expression_sides(equality)?;
    let (rewritten, changed) =
        rewrite_click_proposition_expression(proposition, &left, &right, preserve_states);
    changed.then_some(rewritten)
}

/// Views an equality recorded at a program point as an equality between two
/// expressions at that point. This is the expression-level form needed by a
/// checked rewrite: `at(s, x == y)` permits replacing `at(s, x)` with
/// `at(s, y)`, but does not permit replacing an unqualified `x`.
fn surface_equality_expression_sides(
    equality: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    match equality {
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } => Some((left.clone(), right.clone())),
        ClickProposition::At {
            selector,
            proposition,
        } => {
            let (left, right) = surface_equality_expression_sides(proposition)?;
            Some((
                expression_at_program_point(selector, left),
                expression_at_program_point(selector, right),
            ))
        }
        _ => None,
    }
}

fn expression_at_program_point(
    selector: &ProgramPointSelector,
    expression: ContractExpression,
) -> ContractExpression {
    match expression {
        // `old` and an explicitly selected `at` are already absolute
        // states; an enclosing proposition state does not rebase them.
        ContractExpression::Old(_) | ContractExpression::At { .. } => expression,
        expression => ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression),
        },
    }
}

fn rewrite_click_proposition_expression(
    proposition: &ClickProposition,
    source: &ContractExpression,
    target: &ContractExpression,
    preserve_states: bool,
) -> (ClickProposition, bool) {
    let expression = |value: &ContractExpression| {
        rewrite_contract_expression_exact(value, source, target, preserve_states)
    };
    let rewrite_proposition = |value: &ClickProposition| {
        rewrite_click_proposition_expression(value, source, target, preserve_states)
    };
    match proposition {
        ClickProposition::Value(value) => {
            let (value, changed) = expression(value);
            (ClickProposition::Value(value), changed)
        }

        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let (left, left_changed) = expression(left);
            let (right, right_changed) = expression(right);
            (
                ClickProposition::Comparison {
                    left,
                    operator: *operator,
                    right,
                },
                left_changed || right_changed,
            )
        }
        ClickProposition::FloatClassification {
            expression: value,
            classification,
        } => {
            let (value, changed) = expression(value);
            (
                ClickProposition::FloatClassification {
                    expression: value,
                    classification: *classification,
                },
                changed,
            )
        }
        ClickProposition::Separate { left, right } => {
            let (left, left_changed) =
                rewrite_resource_subject_exact(left, source, target, preserve_states);
            let (right, right_changed) =
                rewrite_resource_subject_exact(right, source, target, preserve_states);
            (
                ClickProposition::Separate { left, right },
                left_changed || right_changed,
            )
        }
        ClickProposition::ResourceViewable { resource } => {
            let (resource, changed) =
                rewrite_resource_subject_exact(resource, source, target, preserve_states);
            (ClickProposition::ResourceViewable { resource }, changed)
        }
        ClickProposition::Contains { parent, child } => {
            let (parent, parent_changed) =
                rewrite_resource_subject_exact(parent, source, target, preserve_states);
            let (child, child_changed) =
                rewrite_resource_subject_exact(child, source, target, preserve_states);
            (
                ClickProposition::Contains { parent, child },
                parent_changed || child_changed,
            )
        }
        ClickProposition::Loadable { segment } => {
            let ContractSegmentSurface::Range { base, start, end } = &segment.surface else {
                return (proposition.clone(), false);
            };
            // Range bases retain a C fragment even when an equality names a
            // matched model binding. Propose the same fragment substitution;
            // the caller's kernel comparison still decides whether the names
            // denote the checked pointer, including under shadowing.
            let (base, changed) = if contract_expression_as_program_expression(source).as_ref()
                == Some(&segment.base)
            {
                (target.clone(), true)
            } else {
                expression(base)
            };
            if !changed {
                return (proposition.clone(), false);
            }
            let Some(lowered_base) = contract_expression_as_program_expression(&base) else {
                return (proposition.clone(), false);
            };
            // Keep the state and both spans exactly as written. This is
            // only a proposed presentation: finish_rewrite lowers it and asks
            // the kernel to match its checked successor before retaining it.
            let mut rewritten = segment.clone();
            rewritten.base = lowered_base;
            rewritten.surface = ContractSegmentSurface::Range {
                base,
                start: start.clone(),
                end: end.clone(),
            };
            (ClickProposition::Loadable { segment: rewritten }, true)
        }
        ClickProposition::Defined { expression: value } => {
            let (value, changed) = expression(value);
            (ClickProposition::Defined { expression: value }, changed)
        }
        ClickProposition::IsA { class, pointer } => {
            let (pointer, changed) = expression(pointer);
            (
                ClickProposition::IsA {
                    class: class.clone(),
                    pointer,
                },
                changed,
            )
        }
        ClickProposition::At {
            selector,
            proposition: body,
        } => {
            let (body, changed) = rewrite_proposition(body);
            (
                ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(body),
                },
                changed,
            )
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            let (left, left_changed) = rewrite_proposition(left);
            let (right, right_changed) = rewrite_proposition(right);
            let rewritten = match proposition {
                ClickProposition::And(_, _) => {
                    ClickProposition::And(Box::new(left), Box::new(right))
                }
                ClickProposition::Or(_, _) => ClickProposition::Or(Box::new(left), Box::new(right)),
                ClickProposition::Implies(_, _) => {
                    ClickProposition::Implies(Box::new(left), Box::new(right))
                }
                _ => unreachable!(),
            };
            (rewritten, left_changed || right_changed)
        }
        ClickProposition::Not(body) => {
            let (body, changed) = rewrite_proposition(body);
            (ClickProposition::Not(Box::new(body)), changed)
        }
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            body,
            ..
        }
        | ClickProposition::Exists {
            click_type: interface_type,
            name,
            body,
            ..
        } => {
            let (body, changed) = rewrite_proposition(body);
            let rewritten = match proposition {
                ClickProposition::ForAll { .. } => ClickProposition::ForAll {
                    click_type: interface_type.clone(),
                    name: name.clone(),
                    written_name: proposition.written_quantifier_name().map(str::to_string),
                    body: Box::new(body),
                },
                ClickProposition::Exists { .. } => ClickProposition::Exists {
                    click_type: interface_type.clone(),
                    name: name.clone(),
                    written_name: proposition.written_quantifier_name().map(str::to_string),
                    body: Box::new(body),
                },
                _ => unreachable!(),
            };
            (rewritten, changed)
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
            ..
        } => {
            let (start, start_changed) = expression(start);
            let (end, end_changed) = expression(end);
            let (body, body_changed) = rewrite_proposition(body);
            let rewritten = match proposition {
                ClickProposition::RangeAll { .. } => ClickProposition::RangeAll {
                    start,
                    end,
                    item: item.clone(),
                    written_item: proposition.written_quantifier_name().map(str::to_string),
                    body: Box::new(body),
                },
                ClickProposition::RangeAny { .. } => ClickProposition::RangeAny {
                    start,
                    end,
                    item: item.clone(),
                    written_item: proposition.written_quantifier_name().map(str::to_string),
                    body: Box::new(body),
                },
                _ => unreachable!(),
            };
            (rewritten, start_changed || end_changed || body_changed)
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let mut changed = false;
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, argument_changed) = expression(argument);
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ClickProposition::PredicateCall {
                    name: name.clone(),
                    arguments,
                },
                changed,
            )
        }
    }
}

fn rewrite_resource_subject_exact(
    subject: &ResourceSubject,
    source: &ContractExpression,
    target: &ContractExpression,
    preserve_states: bool,
) -> (ResourceSubject, bool) {
    match subject {
        ResourceSubject::At { selector, resource } => {
            let (source, target) = if preserve_states {
                let (
                    ContractExpression::At {
                        selector: from,
                        expression: source,
                    },
                    ContractExpression::At {
                        selector: to,
                        expression: target,
                    },
                ) = (source, target)
                else {
                    return (subject.clone(), false);
                };
                if from != selector || to != selector {
                    return (subject.clone(), false);
                }
                (source.as_ref(), target.as_ref())
            } else {
                (source, target)
            };
            let (resource, changed) =
                rewrite_resource_subject_exact(resource, source, target, preserve_states);
            (
                ResourceSubject::At {
                    selector: selector.clone(),
                    resource: Box::new(resource),
                },
                changed,
            )
        }
        ResourceSubject::Emp => (ResourceSubject::Emp, false),
        ResourceSubject::Star(left, right) => {
            let (a, x) = rewrite_resource_subject_exact(left, source, target, preserve_states);
            let (b, y) = rewrite_resource_subject_exact(right, source, target, preserve_states);
            (ResourceSubject::Star(Box::new(a), Box::new(b)), x || y)
        }
        ResourceSubject::Instance { .. }
        | ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Captured { .. } => (subject.clone(), false),
        ResourceSubject::Memory(segment) => (ResourceSubject::Memory(segment.clone()), false),
        ResourceSubject::SavedMemory { base, start, end } => {
            let mut changed = false;
            let mut rewrite = |expression| {
                let (expression, did_change) =
                    rewrite_contract_expression_exact(expression, source, target, preserve_states);
                changed |= did_change;
                expression
            };
            let resource = ResourceSubject::SavedMemory {
                base: rewrite(base),
                start: rewrite(start),
                end: end.as_ref().map(&mut rewrite),
            };
            (resource, changed)
        }
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            let mut changed = false;
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, argument_changed) = rewrite_contract_expression_exact(
                        argument,
                        source,
                        target,
                        preserve_states,
                    );
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ResourceSubject::Declared {
                    kind: *kind,
                    name: name.clone(),
                    arguments,
                    parameter_types: parameter_types.clone(),
                },
                changed,
            )
        }
    }
}

fn rewrite_resource_clause_exact(
    resource: &ResourceClause,
    source: &ContractExpression,
    target: &ContractExpression,
    preserve_states: bool,
) -> (ResourceClause, bool) {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => {
            let (condition, condition_changed) =
                rewrite_click_proposition_expression(condition, source, target, preserve_states);
            let (resource, resource_changed) =
                rewrite_resource_clause_exact(resource, source, target, preserve_states);
            (
                ResourceClause::Conditional {
                    condition,
                    resource: Box::new(resource),
                },
                condition_changed || resource_changed,
            )
        }
        ResourceClause::Named { binding, resource } => {
            let (resource, changed) =
                rewrite_resource_clause_exact(resource, source, target, preserve_states);
            (
                ResourceClause::Named {
                    binding: binding.clone(),
                    resource: Box::new(resource),
                },
                changed,
            )
        }
        ResourceClause::ViewMemory(segment) => (ResourceClause::ViewMemory(segment.clone()), false),
        ResourceClause::OwnMemory(segment) => (ResourceClause::OwnMemory(segment.clone()), false),
        ResourceClause::Iterated(clause) => (ResourceClause::Iterated(clause.clone()), false),
        ResourceClause::MemoryAggregate { access, segments } => (
            ResourceClause::MemoryAggregate {
                access: *access,
                segments: segments.clone(),
            },
            false,
        ),
        ResourceClause::Quantified { quantity, resource } => {
            let (quantity, quantity_changed) =
                rewrite_contract_expression_exact(quantity, source, target, preserve_states);
            let (resource, resource_changed) =
                rewrite_resource_clause_exact(resource, source, target, preserve_states);
            (
                ResourceClause::Quantified {
                    quantity,
                    resource: Box::new(resource),
                },
                quantity_changed || resource_changed,
            )
        }
        ResourceClause::Declared {
            type_schema,
            resource_type_arguments,
            resource_arguments,
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            let mut changed = false;
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, argument_changed) = rewrite_contract_expression_exact(
                        argument,
                        source,
                        target,
                        preserve_states,
                    );
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ResourceClause::Declared {
                    type_schema: type_schema.clone(),
                    resource_type_arguments: resource_type_arguments
                        .iter()
                        .map(|resource| {
                            let (resource, resource_changed) = rewrite_resource_clause_exact(
                                resource,
                                source,
                                target,
                                preserve_states,
                            );
                            changed |= resource_changed;
                            resource
                        })
                        .collect(),
                    resource_arguments: resource_arguments.clone(),
                    access: *access,
                    kind: *kind,
                    name: name.clone(),
                    arguments,
                    parameter_types: parameter_types.clone(),
                },
                changed,
            )
        }
    }
}

fn rewrite_contract_expression_exact(
    expression: &ContractExpression,
    source: &ContractExpression,
    target: &ContractExpression,
    preserve_states: bool,
) -> (ContractExpression, bool) {
    if expression == source {
        return (target.clone(), true);
    }
    let unary = |value: &ContractExpression| {
        rewrite_contract_expression_exact(value, source, target, preserve_states)
    };
    let binary = |left: &ContractExpression, right: &ContractExpression| {
        let (left, left_changed) = unary(left);
        let (right, right_changed) = unary(right);
        (left, right, left_changed || right_changed)
    };
    match expression {
        ContractExpression::IntegerContext(value) => {
            let (value, changed) = unary(value);
            (ContractExpression::IntegerContext(Box::new(value)), changed)
        }

        ContractExpression::Proposition(proposition) => {
            let (proposition, changed) =
                rewrite_click_proposition_expression(proposition, source, target, preserve_states);
            (
                ContractExpression::Proposition(Box::new(proposition)),
                changed,
            )
        }
        ContractExpression::Resource(_) => (expression.clone(), false),
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => (expression.clone(), false),
        // A rewrite does not cross a lambda binder: applying it first
        // exposes its body with the established capture-avoiding rules.
        ContractExpression::Lambda { .. } => (expression.clone(), false),
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            let (function, mut changed) = unary(function);
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, did_change) = unary(argument);
                    changed |= did_change;
                    argument
                })
                .collect();
            (
                ContractExpression::Apply {
                    function: Box::new(function),
                    arguments,
                },
                changed,
            )
        }

        ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::IntegerLiteral(_) => (expression.clone(), false),
        ContractExpression::CUnary { operand, lowered } => {
            let (operand, changed) = unary(operand);
            let fragment = match contract_expression_as_program_expression(&operand) {
                Some(fragment) => fragment,
                None if matches!(
                    lowered,
                    ProgramExpression::Cast { .. } | ProgramExpression::TypedLoad { .. }
                ) =>
                {
                    ProgramExpression::Value(int32(0))
                }
                None => return (expression.clone(), false),
            };
            (
                ContractExpression::CUnary {
                    lowered: c_unary_with_operand(lowered, fragment),
                    operand: Box::new(operand),
                },
                changed,
            )
        }
        ContractExpression::MemoryLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
        } => {
            let (pointer, changed) = unary(pointer);
            (
                ContractExpression::MemoryLoad {
                    pointer: Box::new(pointer),
                    value_type: *value_type,
                    volatile: *volatile,
                    pointee_constant: *pointee_constant,
                },
                changed,
            )
        }
        ContractExpression::Negate(inner) => {
            let (inner, changed) = unary(inner);
            (ContractExpression::Negate(Box::new(inner)), changed)
        }
        // An exact read is read in the surrounding state.
        ContractExpression::Exact(inner) => {
            let (inner, changed) = unary(inner);
            (ContractExpression::Exact(Box::new(inner)), changed)
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => {
            let mut changed = false;
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, argument_changed) = unary(argument);
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ContractExpression::AlgebraicConstructor {
                    algebraic_type: algebraic_type.clone(),
                    variant: variant.clone(),
                    arguments,
                },
                changed,
            )
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let (scrutinee, mut changed) = unary(scrutinee);
            let arms = arms
                .iter()
                .map(|arm| {
                    let (body, body_changed) = unary(&arm.body);
                    changed |= body_changed;
                    AlgebraicMatchArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        body,
                    }
                })
                .collect();
            (
                ContractExpression::AlgebraicMatch {
                    scrutinee: Box::new(scrutinee),
                    arms,
                },
                changed,
            )
        }
        ContractExpression::SequenceLiteral(elements) => {
            let mut changed = false;
            let elements = elements
                .iter()
                .map(|element| {
                    let (element, element_changed) = unary(element);
                    changed |= element_changed;
                    element
                })
                .collect();
            (ContractExpression::SequenceLiteral(elements), changed)
        }
        ContractExpression::SequenceConcat(left, right) => {
            let (left, right, changed) = binary(left, right);
            (
                ContractExpression::SequenceConcat(Box::new(left), Box::new(right)),
                changed,
            )
        }
        ContractExpression::ProgramExpression(
            lowered @ ProgramExpression::Cast {
                expression: operand,
                ..
            },
        ) => {
            let (operand, changed) =
                unary(&ContractExpression::ProgramExpression((**operand).clone()));
            if !changed {
                return (expression.clone(), false);
            }
            let Some(fragment) = contract_expression_as_program_expression(&operand) else {
                return (expression.clone(), false);
            };
            (
                ContractExpression::CUnary {
                    operand: Box::new(operand),
                    lowered: c_unary_with_operand(lowered, fragment),
                },
                changed,
            )
        }
        ContractExpression::QualifiedC { .. }
        | ContractExpression::ProgramExpression(_)
        | ContractExpression::Field { .. }
        | ContractExpression::ProgramBinding(_)
        | ContractExpression::ResourceWildcard => (expression.clone(), false),
        ContractExpression::ArrayIndex {
            base,
            indexes,
            dimensions,
            lowered,
        } => {
            let (base, base_changed) = unary(base);
            let mut indexes_changed = false;
            let indexes = indexes
                .iter()
                .map(|index| {
                    let (index, rewritten) = unary(index);
                    indexes_changed |= rewritten;
                    index
                })
                .collect::<Vec<_>>();
            let changed = base_changed || indexes_changed;
            if !changed {
                return (expression.clone(), false);
            }
            let Some(lowered_base) = contract_expression_as_program_expression(&base) else {
                return (expression.clone(), false);
            };
            let Some(lowered_indexes) = indexes
                .iter()
                .map(contract_expression_as_program_expression)
                .collect::<Option<Vec<_>>>()
            else {
                return (expression.clone(), false);
            };
            let offset = if indexes_changed {
                crate::surface::parser::flatten_array_indices(lowered_indexes, dimensions)
            } else {
                match lowered {
                    ProgramExpression::Index(_, offset) => (**offset).clone(),
                    ProgramExpression::Add(_, stride) => {
                        let ProgramExpression::Multiply(offset, _) = stride.as_ref() else {
                            return (expression.clone(), false);
                        };
                        (**offset).clone()
                    }
                    _ => return (expression.clone(), false),
                }
            };
            let lowered = match lowered {
                ProgramExpression::Index(_, _) => {
                    ProgramExpression::Index(Box::new(lowered_base), Box::new(offset))
                }
                ProgramExpression::Add(_, stride) => {
                    let ProgramExpression::Multiply(_, width) = stride.as_ref() else {
                        return (expression.clone(), false);
                    };
                    ProgramExpression::Add(
                        Box::new(lowered_base),
                        Box::new(ProgramExpression::Multiply(Box::new(offset), width.clone())),
                    )
                }
                _ => return (expression.clone(), false),
            };
            (
                ContractExpression::ArrayIndex {
                    base: Box::new(base),
                    indexes,
                    dimensions: dimensions.clone(),
                    lowered,
                },
                changed,
            )
        }
        ContractExpression::ResourceCount(resource) => {
            let (resource, changed) =
                rewrite_resource_clause_exact(resource, source, target, preserve_states);
            (
                ContractExpression::ResourceCount(Box::new(resource)),
                changed,
            )
        }
        // Historical reads are absolute. An equality about the current
        // variable cannot rewrite the same spelling inside another state.
        // Same-state operands may still rewrite within a compound read.
        ContractExpression::Old(value) => {
            if !preserve_states {
                let (value, changed) = unary(value);
                return (ContractExpression::Old(Box::new(value)), changed);
            }
            let (ContractExpression::Old(source), ContractExpression::Old(target)) =
                (source, target)
            else {
                return (expression.clone(), false);
            };
            let (value, changed) =
                rewrite_contract_expression_exact(value, source, target, preserve_states);
            (ContractExpression::Old(Box::new(value)), changed)
        }
        ContractExpression::At {
            selector,
            expression: value,
        } => {
            if !preserve_states {
                let (value, changed) = unary(value);
                return (
                    ContractExpression::At {
                        selector: selector.clone(),
                        expression: Box::new(value),
                    },
                    changed,
                );
            }
            let (
                ContractExpression::At {
                    selector: source_selector,
                    expression: source,
                },
                ContractExpression::At {
                    selector: target_selector,
                    expression: target,
                },
            ) = (source, target)
            else {
                return (expression.clone(), false);
            };
            if selector != source_selector || selector != target_selector {
                return (expression.clone(), false);
            }
            let (value, changed) =
                rewrite_contract_expression_exact(value, source, target, preserve_states);
            (
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(value),
                },
                changed,
            )
        }
        crate::surface::binary_contract_expression!(left, right) => {
            let (left, right, changed) = binary(left, right);
            let rewritten = match expression {
                ContractExpression::Add(_, _) => {
                    ContractExpression::Add(Box::new(left), Box::new(right))
                }
                ContractExpression::Subtract(_, _) => {
                    ContractExpression::Subtract(Box::new(left), Box::new(right))
                }
                ContractExpression::Multiply(_, _) => {
                    ContractExpression::Multiply(Box::new(left), Box::new(right))
                }
                ContractExpression::Divide(_, _) => {
                    ContractExpression::Divide(Box::new(left), Box::new(right))
                }
                ContractExpression::Remainder(_, _) => {
                    ContractExpression::Remainder(Box::new(left), Box::new(right))
                }
                ContractExpression::ShiftLeft(_, _) => {
                    ContractExpression::ShiftLeft(Box::new(left), Box::new(right))
                }
                ContractExpression::RustShiftLeft(_, _) => {
                    ContractExpression::RustShiftLeft(Box::new(left), Box::new(right))
                }
                ContractExpression::ShiftRight(_, _) => {
                    ContractExpression::ShiftRight(Box::new(left), Box::new(right))
                }
                ContractExpression::RustShiftRight(_, _) => {
                    ContractExpression::RustShiftRight(Box::new(left), Box::new(right))
                }
                ContractExpression::BitwiseAnd(_, _) => {
                    ContractExpression::BitwiseAnd(Box::new(left), Box::new(right))
                }
                ContractExpression::BitwiseOr(_, _) => {
                    ContractExpression::BitwiseOr(Box::new(left), Box::new(right))
                }
                ContractExpression::BitwiseXor(_, _) => {
                    ContractExpression::BitwiseXor(Box::new(left), Box::new(right))
                }
                ContractExpression::Index(_, _) => {
                    ContractExpression::Index(Box::new(left), Box::new(right))
                }
                _ => unreachable!(),
            };
            (rewritten, changed)
        }
        ContractExpression::BitwiseNot(value) => {
            let (value, changed) = unary(value);
            (ContractExpression::BitwiseNot(Box::new(value)), changed)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let (condition, condition_changed) =
                rewrite_click_proposition_expression(condition, source, target, preserve_states);
            let (then_branch, then_changed) = unary(then_branch);
            let (else_branch, else_changed) = unary(else_branch);
            (
                ContractExpression::If {
                    condition: Box::new(condition),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                },
                condition_changed || then_changed || else_changed,
            )
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let (start, start_changed) = unary(start);
            let (end, end_changed) = unary(end);
            let (initial, initial_changed) = unary(initial);
            let (body, body_changed) = unary(body);
            (
                ContractExpression::RangeFold {
                    start: Box::new(start),
                    end: Box::new(end),
                    initial: Box::new(initial),
                    accumulator: accumulator.clone(),
                    item: item.clone(),
                    body: Box::new(body),
                },
                start_changed || end_changed || initial_changed || body_changed,
            )
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let (value, value_changed) = unary(value);
            let (body, body_changed) = unary(body);
            (
                ContractExpression::Let {
                    name: name.clone(),
                    click_type: click_type.clone(),
                    value: Box::new(value),
                    body: Box::new(body),
                },
                value_changed || body_changed,
            )
        }
        ContractExpression::MethodCall {
            receiver,
            method,
            arguments,
        } => {
            let (receiver, mut changed) = unary(receiver);
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, argument_changed) = unary(argument);
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ContractExpression::MethodCall {
                    receiver: Box::new(receiver),
                    method: method.clone(),
                    arguments,
                },
                changed,
            )
        }
        ContractExpression::Call { name, arguments } => {
            let mut changed = false;
            let arguments = arguments
                .iter()
                .map(|argument| {
                    let (argument, argument_changed) = unary(argument);
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ContractExpression::Call {
                    name: name.clone(),
                    arguments,
                },
                changed,
            )
        }
    }
}

fn substitute_contract_segment(
    segment: &ContractSegment,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression_in(base, substitutions)?,
            start: substitute_contract_expression_in(start, substitutions)?,
            end: substitute_contract_expression_in(end, substitutions)?,
        },
        ContractSegmentSurface::StructRange {
            base,
            start,
            end,
            layout,
        } => ContractSegmentSurface::StructRange {
            base: substitute_contract_expression_in(base, substitutions)?,
            start: substitute_contract_expression_in(start, substitutions)?,
            end: substitute_contract_expression_in(end, substitutions)?,
            layout: layout.clone(),
        },
        ContractSegmentSurface::Field {
            base,
            name,
            element_width,
            element_type,
            value_bytes,
        } => ContractSegmentSurface::Field {
            base: base
                .as_ref()
                .map(|base| substitute_contract_expression_in(base, substitutions).map(Box::new))
                .transpose()?,
            name: name.clone(),
            element_width: *element_width,
            element_type: *element_type,
            value_bytes: *value_bytes,
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        uninitialized: segment.uninitialized,
        state: segment.state,
        base: substitute_program_expression_in(&segment.base, substitutions)?,
        start: substitute_program_expression_in(&segment.start, substitutions)?,
        end: substitute_program_expression_in(&segment.end, substitutions)?,
        surface,
    })
}

fn substitute_resource_subject(
    resource: &ResourceSubject,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ResourceSubject, String> {
    if substitutions.source.is_some() {
        let mut names = BTreeSet::<crate::kernel::BindingName>::new();
        collect_resource_subject_referenced_bindings(resource, &mut names);
        let selected = substitutions.selected(names);
        return substitute_resource_subject(resource, &selected);
    }

    match resource {
        ResourceSubject::At { selector, resource } => Ok(ResourceSubject::At {
            selector: selector.clone(),
            resource: Box::new(substitute_resource_subject(resource, substitutions)?),
        }),
        ResourceSubject::Emp => Ok(ResourceSubject::Emp),
        ResourceSubject::Star(left, right) => Ok(ResourceSubject::Star(
            Box::new(substitute_resource_subject(left, substitutions)?),
            Box::new(substitute_resource_subject(right, substitutions)?),
        )),
        ResourceSubject::Instance { .. } | ResourceSubject::Footprint(_) => Ok(resource.clone()),
        ResourceSubject::Parameter { name, .. } => match substitutions.values.get(name) {
            Some(ContractExpression::Resource(subject)) => Ok(subject.as_ref().clone()),
            Some(_) => Err(format!(
                "resource parameter `{name}` requires a Resource argument"
            )),
            None => Ok(resource.clone()),
        },
        ResourceSubject::Captured { .. } => Ok(resource.clone()),
        ResourceSubject::Memory(segment) => {
            if let Some((base, start, end)) = segment.surface_range() {
                let base = substitute_contract_expression_in(base, substitutions)?;
                let start = substitute_contract_expression_in(start, substitutions)?;
                let end = substitute_contract_expression_in(end, substitutions)?;
                if [&base, &start, &end]
                    .iter()
                    .any(|value| contract_expression_as_program_expression(value).is_none())
                {
                    // SymbolicMemory state-valued arguments are Surface expressions, not
                    // C fragments. Retain them in the same resource form used
                    // by written `memory(old(p)[lo..hi])` facts.
                    let at_state = |value| match segment.state {
                        ContractSegmentState::Current => value,
                        ContractSegmentState::Old => ContractExpression::Old(Box::new(value)),
                    };
                    return Ok(ResourceSubject::SavedMemory {
                        base: at_state(base),
                        start: at_state(start),
                        end: Some(at_state(end)),
                    });
                }
            }
            Ok(ResourceSubject::Memory(substitute_contract_segment(
                segment,
                substitutions,
            )?))
        }
        ResourceSubject::SavedMemory { base, start, end } => Ok(ResourceSubject::SavedMemory {
            base: substitute_contract_expression_in(base, substitutions)?,
            start: substitute_contract_expression_in(start, substitutions)?,
            end: end
                .as_ref()
                .map(|end| substitute_contract_expression_in(end, substitutions))
                .transpose()?,
        }),
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
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

pub(in crate::surface) fn apply_contract_lets_to_requirement(
    requirement: Requirement,
    bindings: &[ContractLetBinding],
) -> Result<Requirement, String> {
    match requirement {
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

pub(in crate::surface) fn apply_contract_lets_to_ensure_clause(
    clause: EnsureClause,
    bindings: &[ContractLetBinding],
) -> Result<EnsureClause, String> {
    let EnsureClause {
        proof_bindings: _,
        name,
        ensure,
        proof,
        borrowed,
        view_source,
        condition,
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
        proof_bindings: bindings
            .iter()
            .filter_map(|binding| {
                binding.value().map(|value| {
                    (
                        binding.name.clone(),
                        binding.click_type.clone(),
                        value.clone(),
                    )
                })
            })
            .collect(),
        name,
        ensure,
        proof,
        borrowed,
        view_source,
        condition: condition
            .map(|condition| apply_contract_lets_to_proposition(condition, bindings))
            .transpose()?,
    })
}

pub(in crate::surface) fn apply_contract_lets_to_resource_clause(
    resource: ResourceClause,
    bindings: &[ContractLetBinding],
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => Ok(ResourceClause::Conditional {
            condition: apply_contract_lets_to_proposition(condition, bindings)?,
            resource: Box::new(apply_contract_lets_to_resource_clause(*resource, bindings)?),
        }),
        ResourceClause::Named { binding, resource } => Ok(ResourceClause::Named {
            binding,
            resource: Box::new(apply_contract_lets_to_resource_clause(*resource, bindings)?),
        }),
        ResourceClause::Quantified { quantity, resource } => Ok(ResourceClause::Quantified {
            quantity: apply_contract_lets_to_expression(quantity, bindings)?,
            resource: Box::new(apply_contract_lets_to_resource_clause(*resource, bindings)?),
        }),
        ResourceClause::ViewMemory(segment) => Ok(ResourceClause::ViewMemory(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceClause::OwnMemory(segment) => Ok(ResourceClause::OwnMemory(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceClause::Iterated(clause) => Ok(ResourceClause::Iterated(clause)),
        ResourceClause::MemoryAggregate { access, segments } => {
            Ok(ResourceClause::MemoryAggregate {
                access,
                segments: segments
                    .into_iter()
                    .map(|segment| apply_contract_lets_to_segment(segment, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        ResourceClause::Declared {
            type_schema,
            resource_type_arguments,
            resource_arguments,
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            type_schema: type_schema.clone(),
            resource_type_arguments: resource_type_arguments
                .into_iter()
                .map(|resource| apply_contract_lets_to_resource_clause(resource, bindings))
                .collect::<Result<_, _>>()?,
            resource_arguments: resource_arguments.clone(),
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
        ResourceSubject::At { selector, resource } => Ok(ResourceSubject::At {
            selector,
            resource: Box::new(apply_contract_lets_to_resource_subject(
                *resource, bindings,
            )?),
        }),
        ResourceSubject::Emp => Ok(ResourceSubject::Emp),
        ResourceSubject::Star(left, right) => Ok(ResourceSubject::Star(
            Box::new(apply_contract_lets_to_resource_subject(*left, bindings)?),
            Box::new(apply_contract_lets_to_resource_subject(*right, bindings)?),
        )),
        ResourceSubject::Instance { .. }
        | ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Captured { .. } => Ok(resource),
        ResourceSubject::Memory(segment) => Ok(ResourceSubject::Memory(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceSubject::SavedMemory { base, start, end } => Ok(ResourceSubject::SavedMemory {
            base: apply_contract_lets_to_expression(base, bindings)?,
            start: apply_contract_lets_to_expression(start, bindings)?,
            end: end
                .map(|end| apply_contract_lets_to_expression(end, bindings))
                .transpose()?,
        }),
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

pub(in crate::surface) fn apply_contract_lets_to_segment(
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
        ContractSegmentSurface::StructRange {
            base,
            start,
            end,
            layout,
        } => ContractSegmentSurface::StructRange {
            base: substitute_contract_expression(&base, &substitutions)?,
            start: substitute_contract_expression(&start, &substitutions)?,
            end: substitute_contract_expression(&end, &substitutions)?,
            layout: layout.clone(),
        },
        ContractSegmentSurface::Field {
            base,
            name,
            element_width,
            element_type,
            value_bytes,
        } => ContractSegmentSurface::Field {
            base: base
                .map(|base| substitute_contract_expression(&base, &substitutions).map(Box::new))
                .transpose()?,
            name,
            element_width,
            element_type,
            value_bytes,
        },
        surface => surface,
    };
    let segment = ContractSegment {
        uninitialized: segment.uninitialized,
        state: segment.state,
        base: substitute_program_expression(&segment.base, &substitutions)?,
        start: substitute_program_expression(&segment.start, &substitutions)?,
        end: substitute_program_expression(&segment.end, &substitutions)?,
        surface,
    };
    reject_contract_where_let_references(
        &contract_segment_referenced_names(&segment),
        bindings,
        "memory segment expressions",
    )?;
    Ok(segment)
}

pub(in crate::surface) fn reject_contract_where_let_references(
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

pub(in crate::surface) fn apply_contract_lets_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    let proposition = apply_contract_let_expressions_to_proposition(proposition, bindings)?;
    wrap_contract_where_lets_proposition(proposition, bindings)
}

pub(in crate::surface) fn apply_contract_let_expressions_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    if bindings.is_empty() {
        return Ok(proposition);
    }
    let mut capture_names = BTreeSet::new();
    for binding in bindings {
        if let Some(value) = binding.value() {
            collect_contract_expression_referenced_bindings(value, &mut capture_names);
        }
    }
    apply_contract_let_expressions_inner(proposition, bindings, &capture_names)
}

fn apply_contract_let_expressions_inner(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
    capture_names: &BTreeSet<crate::kernel::BindingName>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Value(expression) => Ok(ClickProposition::Value(
            apply_contract_lets_to_expression(expression, bindings)?,
        )),

        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: apply_contract_lets_to_expression(left, bindings)?,
            operator,
            right: apply_contract_lets_to_expression(right, bindings)?,
        }),
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => Ok(ClickProposition::FloatClassification {
            expression: apply_contract_lets_to_expression(expression, bindings)?,
            classification,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: apply_contract_lets_to_resource_subject(left, bindings)?,
            right: apply_contract_lets_to_resource_subject(right, bindings)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: apply_contract_lets_to_resource_subject(parent, bindings)?,
            child: apply_contract_lets_to_resource_subject(child, bindings)?,
        }),
        ClickProposition::ResourceViewable { resource } => Ok(ClickProposition::ResourceViewable {
            resource: apply_contract_lets_to_resource_subject(resource, bindings)?,
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: apply_contract_lets_to_segment(segment, bindings)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: apply_contract_lets_to_expression(expression, bindings)?,
        }),
        ClickProposition::IsA { class, pointer } => Ok(ClickProposition::IsA {
            class,
            pointer: apply_contract_lets_to_expression(pointer, bindings)?,
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector,
            proposition: Box::new(apply_contract_let_expressions_inner(
                *proposition,
                bindings,
                capture_names,
            )?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(apply_contract_let_expressions_inner(
                *left,
                bindings,
                capture_names,
            )?),
            Box::new(apply_contract_let_expressions_inner(
                *right,
                bindings,
                capture_names,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(apply_contract_let_expressions_inner(
                *left,
                bindings,
                capture_names,
            )?),
            Box::new(apply_contract_let_expressions_inner(
                *right,
                bindings,
                capture_names,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            apply_contract_let_expressions_inner(*body, bindings, capture_names)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(apply_contract_let_expressions_inner(
                *left,
                bindings,
                capture_names,
            )?),
            Box::new(apply_contract_let_expressions_inner(
                *right,
                bindings,
                capture_names,
            )?),
        )),
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &name);
            let original_name = name.clone();
            let (name, body) = prepare_contract_let_binding_body(
                &name,
                *body,
                &scoped,
                capture_names,
                interface_type == ClickType::Integer,
            )?;
            let written_name = written_name.or_else(|| {
                (name != original_name)
                    .then(|| original_name.written().map(str::to_owned))
                    .flatten()
            });
            Ok(ClickProposition::ForAll {
                click_type: interface_type,
                name,
                written_name,
                body: Box::new(apply_contract_let_expressions_inner(
                    body,
                    &scoped,
                    capture_names,
                )?),
            })
        }
        ClickProposition::Exists {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &name);
            let original_name = name.clone();
            let (name, body) = prepare_contract_let_binding_body(
                &name,
                *body,
                &scoped,
                capture_names,
                interface_type == ClickType::Integer,
            )?;
            let written_name = written_name.or_else(|| {
                (name != original_name)
                    .then(|| original_name.written().map(str::to_owned))
                    .flatten()
            });
            Ok(ClickProposition::Exists {
                click_type: interface_type,
                name,
                written_name,
                body: Box::new(apply_contract_let_expressions_inner(
                    body,
                    &scoped,
                    capture_names,
                )?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            let original_item = item.clone();
            let (item, body) =
                prepare_contract_let_binding_body(&item, *body, &scoped, capture_names, false)?;
            let written_item = written_item.or_else(|| {
                (item != original_item)
                    .then(|| original_item.written().map(str::to_owned))
                    .flatten()
            });
            Ok(ClickProposition::RangeAll {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                written_item,
                body: Box::new(apply_contract_let_expressions_inner(
                    body,
                    &scoped,
                    capture_names,
                )?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            let original_item = item.clone();
            let (item, body) =
                prepare_contract_let_binding_body(&item, *body, &scoped, capture_names, false)?;
            let written_item = written_item.or_else(|| {
                (item != original_item)
                    .then(|| original_item.written().map(str::to_owned))
                    .flatten()
            });
            Ok(ClickProposition::RangeAny {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                written_item,
                body: Box::new(apply_contract_let_expressions_inner(
                    body,
                    &scoped,
                    capture_names,
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

/// Freshen a clause binder before alias expansion when an alias initializer
/// contains that name free. The initializer is inserted later, inside this
/// proposition, so performing the rename first preserves its declaration
/// meaning without expanding the initializer merely to detect capture.
fn prepare_contract_let_binding_body(
    binder: &SurfaceBinder,
    body: ClickProposition,
    bindings: &[ContractLetBinding],
    capture_names: &BTreeSet<crate::kernel::BindingName>,
    integer: bool,
) -> Result<(SurfaceBinder, ClickProposition), String> {
    if !capture_names.contains(&binder.kernel_name()) {
        return Ok((binder.clone(), body));
    }
    let mut referenced_names = BTreeSet::new();
    collect_click_proposition_referenced_names(&body, &mut referenced_names);
    let referenced_bindings = referenced_contract_let_bindings(bindings, referenced_names);
    let values = referenced_bindings
        .iter()
        .filter_map(|binding| {
            binding
                .value()
                .map(|value| (binding.name.clone(), value.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    let substitutions = ContractSubstitutions::indexed(
        values
            .iter()
            .map(|(name, value)| (SurfaceBinder::from(name), value.clone())),
    );
    if !substitutions_reference_name(&substitutions, binder) {
        return Ok((binder.clone(), body));
    }

    let fresh = SurfaceBinder::fresh();
    let _ = integer;
    let renaming = BTreeMap::from([(binder.clone(), fresh.reference())]);
    Ok((fresh, substitute_click_proposition(&body, &renaming)?))
}

pub(in crate::surface) fn wrap_contract_where_lets_proposition(
    mut proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    for (index, binding) in bindings.iter().enumerate().rev() {
        let Some(condition) = binding.where_condition() else {
            continue;
        };
        let condition =
            apply_contract_let_expressions_to_proposition(condition.clone(), &bindings[..index])?;
        let Some(click_type) = &binding.click_type else {
            return Err(format!(
                "`let ... where` `{}` requires an explicit type annotation",
                binding.name
            ));
        };
        let ClickType::Program(interface_type) = click_type else {
            return Err(format!(
                "`let ... where` `{}` requires a C type annotation",
                binding.name
            ));
        };
        proposition = ClickProposition::Exists {
            click_type: ClickType::Program(*interface_type),
            name: binding.name.clone().into(),
            written_name: None,
            body: Box::new(ClickProposition::And(
                Box::new(condition),
                Box::new(proposition),
            )),
        };
    }
    Ok(proposition)
}

pub(in crate::surface) fn apply_contract_lets_to_expression(
    expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> Result<ContractExpression, String> {
    // Integer lets are deliberately retained as lexical aliases until the
    // mathematical lowering pass. Resolve the transitive dependency closure
    // with an indexed worklist: the old fixed-point loop rescanned every
    // binding once per dependency depth, which made a linear alias chain
    // quadratic before lowering even had a chance to preserve sharing.
    let referenced_names = contract_expression_referenced_lexical_names(&expression);
    let referenced_bindings = referenced_contract_let_bindings(bindings, referenced_names);
    let substitutions = contract_let_substitutions(bindings);
    let expression = substitute_contract_expression(&expression, &substitutions)?;
    Ok(wrap_contract_lets_expression(
        expression,
        &referenced_bindings,
    ))
}

fn referenced_contract_let_bindings(
    bindings: &[ContractLetBinding],
    mut referenced_names: BTreeSet<String>,
) -> Vec<ContractLetBinding> {
    let binding_indices = bindings
        .iter()
        .enumerate()
        .filter_map(|(index, binding)| binding.value().map(|_| (binding.name.as_str(), index)))
        .collect::<BTreeMap<_, _>>();
    let mut pending = referenced_names.iter().cloned().collect::<Vec<_>>();
    let mut referenced_indices = BTreeSet::new();
    while let Some(name) = pending.pop() {
        let Some(&index) = binding_indices.get(name.as_str()) else {
            continue;
        };
        if !referenced_indices.insert(index) {
            continue;
        }
        let Some(value) = bindings[index].value() else {
            continue;
        };
        for dependency in contract_expression_referenced_lexical_names(value) {
            if referenced_names.insert(dependency.clone()) {
                pending.push(dependency);
            }
        }
    }
    referenced_indices
        .into_iter()
        .map(|index| bindings[index].clone())
        .collect()
}

pub(in crate::surface) fn wrap_contract_lets_expression(
    mut expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> ContractExpression {
    for binding in bindings.iter().rev() {
        let Some(value) = binding.value() else {
            continue;
        };
        expression = ContractExpression::Let {
            name: binding.name.clone().into(),
            click_type: binding.click_type.clone(),
            value: Box::new(value.clone()),
            body: Box::new(expression),
        };
    }
    expression
}

pub(in crate::surface) fn contract_lets_without_name(
    bindings: &[ContractLetBinding],
    name: &SurfaceBinder,
) -> Vec<ContractLetBinding> {
    bindings
        .iter()
        .filter(|binding| name != &binding.name)
        .cloned()
        .collect()
}

fn contract_expression_referenced_lexical_names(
    expression: &ContractExpression,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_contract_expression_referenced_bindings(expression, &mut names);
    names
}

pub(in crate::surface) fn contract_expression_referenced_names(
    expression: &ContractExpression,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_contract_expression_referenced_names(expression, &mut names);
    names
}

pub(in crate::surface) fn collect_contract_expression_referenced_binders(
    expression: &ContractExpression,
    names: &mut BinderSet,
) {
    names.extend(
        contract_expression_referenced_bindings(expression)
            .into_iter()
            .filter_map(|name| match name {
                crate::kernel::BindingName::Named(name) => Some(SurfaceBinder::from(name)),
                crate::kernel::BindingName::Generated(id) => Some(SurfaceBinder::from(id)),
                _ => None,
            }),
    );
}
pub(in crate::surface) fn collect_click_proposition_referenced_binders(
    proposition: &ClickProposition,
    names: &mut BinderSet,
) {
    let mut bindings = BTreeSet::<crate::kernel::BindingName>::new();
    collect_click_proposition_referenced_bindings(proposition, &mut bindings);
    names.extend(bindings.into_iter().filter_map(|name| match name {
        crate::kernel::BindingName::Named(name) => Some(SurfaceBinder::from(name)),
        crate::kernel::BindingName::Generated(id) => Some(SurfaceBinder::from(id)),
        _ => None,
    }));
}
pub(in crate::surface) fn collect_contract_expression_referenced_names(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    let bindings = contract_expression_referenced_bindings(expression);
    names.extend(
        bindings
            .iter()
            .filter_map(|binding| binding.metadata_name().map(str::to_owned)),
    );
}

pub(in crate::surface) fn collect_click_proposition_referenced_names(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    let mut bindings = BTreeSet::<crate::kernel::BindingName>::new();
    collect_click_proposition_referenced_bindings(proposition, &mut bindings);
    names.extend(
        bindings
            .iter()
            .filter_map(|binding| binding.metadata_name().map(str::to_owned)),
    );
}

/// Select lexical dependencies or exact program bindings with the same walk.
/// Lexical binders remove only named dependencies, never physical declarations.
pub(in crate::surface) trait ReferencedBinding: Ord + From<String> {
    fn program(binding: &crate::kernel::BindingName) -> Option<Self>;
    fn captured_value(_value: &ProgramValue, _names: &mut BTreeSet<Self>)
    where
        Self: Sized,
    {
    }
    fn leave_scope(names: &mut BTreeSet<Self>, binder: &Self) -> bool
    where
        Self: Sized,
    {
        names.remove(binder)
    }
    fn binder(binding: &SurfaceBinder) -> Option<Self> {
        Self::program(&binding.kernel_name())
    }
}
impl ReferencedBinding for String {
    fn program(binding: &crate::kernel::BindingName) -> Option<Self> {
        binding.named().map(str::to_owned)
    }
}
impl ReferencedBinding for crate::kernel::BindingName {
    fn program(binding: &crate::kernel::BindingName) -> Option<Self> {
        Some(binding.clone())
    }
}

/// All referenced lexical identities, including references under their binder.
/// Used to choose deterministic capture-free local slots for beta elaboration.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::surface) struct LexicalBinding(pub crate::kernel::BindingName);
impl From<String> for LexicalBinding {
    fn from(name: String) -> Self {
        Self(name.into())
    }
}
impl ReferencedBinding for LexicalBinding {
    fn program(binding: &crate::kernel::BindingName) -> Option<Self> {
        Some(Self(binding.clone()))
    }
    fn leave_scope(names: &mut BTreeSet<Self>, binder: &Self) -> bool {
        // Unused declarations can capture inserted references too. Retain
        // every binder, so deterministic slots never trigger fresh renaming.
        crate::instrumentation::record_deterministic_work(1);
        names.insert(binder.clone());
        false
    }
}

pub(in crate::surface) fn contract_expression_referenced_bindings(
    expression: &ContractExpression,
) -> BTreeSet<crate::kernel::BindingName> {
    let mut bindings = BTreeSet::new();
    collect_contract_expression_referenced_bindings(expression, &mut bindings);
    bindings
}

pub(in crate::surface) fn collect_contract_expression_referenced_bindings<N: ReferencedBinding>(
    expression: &ContractExpression,
    names: &mut BTreeSet<N>,
) {
    // A lexical let chain is a sequence of scopes, not recursive syntax work.
    // Save each entry dependency so shadowing restores exactly its former set.
    if matches!(expression, ContractExpression::Let { .. }) {
        let mut current = expression;
        let mut scopes = Vec::new();
        while let ContractExpression::Let {
            name, value, body, ..
        } = current
        {
            collect_contract_expression_referenced_bindings(value, names);
            let previous = N::binder(name).is_some_and(|name| N::leave_scope(names, &name));
            scopes.push((name, previous));
            current = body;
        }
        collect_contract_expression_referenced_bindings(current, names);
        for (name, previous) in scopes.into_iter().rev() {
            if let Some(name) = N::binder(name) {
                N::leave_scope(names, &name);
                if previous {
                    names.insert(name);
                }
            }
        }
        return;
    }
    let mut depth = 0;
    let mut current = expression;
    while let ContractExpression::Add(left, _) = current {
        depth += 1;
        current = left;
    }
    if depth > 128 {
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            match expression {
                crate::surface::binary_contract_expression!(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                ContractExpression::CUnary { operand: inner, .. }
                | ContractExpression::MemoryLoad { pointer: inner, .. }
                | ContractExpression::Negate(inner)
                | ContractExpression::Old(inner)
                | ContractExpression::Exact(inner)
                | ContractExpression::BitwiseNot(inner)
                | ContractExpression::At {
                    expression: inner, ..
                } => pending.push(inner),
                expression => {
                    collect_contract_expression_referenced_bindings_one(expression, names)
                }
            }
        }
        return;
    }
    collect_contract_expression_referenced_bindings_one(expression, names);
}

fn collect_contract_expression_referenced_bindings_one<N: ReferencedBinding>(
    expression: &ContractExpression,
    names: &mut BTreeSet<N>,
) {
    match expression {
        ContractExpression::IntegerContext(value) => {
            collect_contract_expression_referenced_bindings(value, names)
        }

        ContractExpression::Proposition(proposition) => {
            collect_click_proposition_referenced_bindings(proposition, names)
        }
        ContractExpression::Resource(subject) => {
            collect_resource_subject_referenced_bindings(subject, names)
        }
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => {}
        ContractExpression::Lambda {
            parameters, body, ..
        } => {
            let mut captures = BTreeSet::new();
            collect_contract_expression_referenced_bindings(body, &mut captures);
            for (name, _) in parameters {
                let _ = N::binder(name).is_some_and(|name| N::leave_scope(&mut captures, &name));
            }
            names.extend(captures);
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            collect_contract_expression_referenced_bindings(function, names);
            for argument in arguments {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }

        ContractExpression::ResourceField(_) | ContractExpression::IntegerLiteral(_) => {}
        ContractExpression::Negate(inner) | ContractExpression::Exact(inner) => {
            collect_contract_expression_referenced_bindings(inner, names);
        }
        ContractExpression::AlgebraicVariable { name, .. } => {
            if let Some(name) = N::binder(name) {
                names.insert(name);
            }
        }
        ContractExpression::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_contract_expression_referenced_bindings(scrutinee, names);
            for arm in arms {
                let mut arm_names = BTreeSet::new();
                collect_contract_expression_referenced_bindings(&arm.body, &mut arm_names);
                for binding in &arm.bindings {
                    let _ = N::binder(binding)
                        .is_some_and(|name| N::leave_scope(&mut arm_names, &name));
                }
                names.extend(arm_names);
            }
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                collect_contract_expression_referenced_bindings(element, names);
            }
        }
        ContractExpression::SequenceConcat(left, right) => {
            collect_contract_expression_referenced_bindings(left, names);
            collect_contract_expression_referenced_bindings(right, names);
        }
        // A qualified C object is referenced under its qualified spelling as
        // well as through whatever its lowering names, so a body that reads
        // one is seen to mention it (`reject_pure_bodies_reading_c_objects`).
        ContractExpression::QualifiedC { name, lowered } => {
            names.insert(name.clone().into());
            collect_program_expression_referenced_bindings(lowered, names);
        }
        ContractExpression::CUnary { operand, .. }
        | ContractExpression::MemoryLoad {
            pointer: operand, ..
        } => {
            collect_contract_expression_referenced_bindings(operand, names);
        }
        ContractExpression::ProgramExpression(expression) => {
            collect_program_expression_referenced_bindings(expression, names);
        }
        ContractExpression::Field { base, .. } => {
            collect_contract_expression_referenced_bindings(base, names);
        }
        ContractExpression::ArrayIndex { base, indexes, .. } => {
            collect_contract_expression_referenced_bindings(base, names);
            for index in indexes {
                collect_contract_expression_referenced_bindings(index, names);
            }
        }
        ContractExpression::Binding(name) | ContractExpression::ProgramBinding(name) => {
            names.insert(name.clone().into());
        }
        ContractExpression::ResourceCount(resource) => {
            if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                for argument in arguments {
                    collect_contract_expression_referenced_bindings(argument, names);
                }
            }
        }
        ContractExpression::ResourceWildcard => {}
        ContractExpression::Old(expression) | ContractExpression::BitwiseNot(expression) => {
            collect_contract_expression_referenced_bindings(expression, names);
        }
        ContractExpression::At { expression, .. } => {
            collect_contract_expression_referenced_bindings(expression, names);
        }
        crate::surface::binary_contract_expression!(left, right) => {
            collect_contract_expression_referenced_bindings(left, names);
            collect_contract_expression_referenced_bindings(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_proposition_referenced_bindings(condition, names);
            collect_contract_expression_referenced_bindings(then_branch, names);
            collect_contract_expression_referenced_bindings(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_contract_expression_referenced_bindings(start, names);
            collect_contract_expression_referenced_bindings(end, names);
            collect_contract_expression_referenced_bindings(initial, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_bindings(body, &mut body_names);
            let _ =
                N::binder(accumulator).is_some_and(|name| N::leave_scope(&mut body_names, &name));
            let _ = N::binder(item).is_some_and(|name| N::leave_scope(&mut body_names, &name));
            names.extend(body_names);
        }
        ContractExpression::Let {
            name, value, body, ..
        } => {
            collect_contract_expression_referenced_bindings(value, names);
            let previous = N::binder(name).is_some_and(|name| N::leave_scope(names, &name));
            collect_contract_expression_referenced_bindings(body, names);
            let _ = N::binder(name).is_some_and(|name| N::leave_scope(names, &name));
            if previous && let Some(name) = N::binder(name) {
                names.insert(name);
            }
        }
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            collect_contract_expression_referenced_bindings(receiver, names);
            for argument in arguments {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }
    }
}

fn collect_resource_subject_referenced_bindings<N: ReferencedBinding>(
    subject: &ResourceSubject,
    names: &mut BTreeSet<N>,
) {
    match subject {
        ResourceSubject::At { resource, .. } => {
            collect_resource_subject_referenced_bindings(resource, names)
        }
        ResourceSubject::Emp => (),
        ResourceSubject::Star(left, right) => {
            collect_resource_subject_referenced_bindings(left, names);
            collect_resource_subject_referenced_bindings(right, names);
        }
        ResourceSubject::Parameter { name, .. } => {
            names.insert(N::from(name.clone()));
        }
        ResourceSubject::Instance { .. }
        | ResourceSubject::Footprint(_)
        | ResourceSubject::Captured { .. } => {}
        ResourceSubject::SavedMemory { base, start, end } => {
            for argument in [base, start].into_iter().chain(end.iter()) {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }
        ResourceSubject::Memory(segment) => {
            collect_program_expression_referenced_bindings(&segment.base, names);
            collect_program_expression_referenced_bindings(&segment.start, names);
            collect_program_expression_referenced_bindings(&segment.end, names);
            match &segment.surface {
                ContractSegmentSurface::Range { base, start, end }
                | ContractSegmentSurface::StructRange {
                    base, start, end, ..
                } => {
                    for expression in [base, start, end] {
                        collect_contract_expression_referenced_bindings(expression, names);
                    }
                }
                ContractSegmentSurface::Field {
                    base: Some(base), ..
                } => {
                    collect_contract_expression_referenced_bindings(base, names);
                }
                _ => {}
            }
        }
    }
}

pub(in crate::surface) fn collect_click_proposition_referenced_bindings<N: ReferencedBinding>(
    proposition: &ClickProposition,
    names: &mut BTreeSet<N>,
) {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            proposition => collect_click_proposition_referenced_bindings_one(proposition, names),
        }
    }
}

fn collect_click_proposition_referenced_bindings_one<N: ReferencedBinding>(
    proposition: &ClickProposition,
    names: &mut BTreeSet<N>,
) {
    match proposition {
        ClickProposition::Value(expression) => {
            collect_contract_expression_referenced_bindings(expression, names)
        }

        ClickProposition::Comparison { left, right, .. } => {
            collect_contract_expression_referenced_bindings(left, names);
            collect_contract_expression_referenced_bindings(right, names);
        }
        ClickProposition::FloatClassification { expression, .. } => {
            collect_contract_expression_referenced_bindings(expression, names);
        }
        ClickProposition::Separate { left, right } => {
            collect_resource_subject_referenced_bindings(left, names);
            collect_resource_subject_referenced_bindings(right, names);
        }
        ClickProposition::Contains { parent, child } => {
            collect_resource_subject_referenced_bindings(parent, names);
            collect_resource_subject_referenced_bindings(child, names);
        }
        ClickProposition::ResourceViewable { resource } => {
            collect_resource_subject_referenced_bindings(resource, names);
        }
        ClickProposition::Loadable { segment } => {
            for expression in [&segment.base, &segment.start, &segment.end] {
                collect_program_expression_referenced_bindings(expression, names);
            }
        }
        ClickProposition::Defined { expression }
        | ClickProposition::IsA {
            pointer: expression,
            ..
        } => {
            collect_contract_expression_referenced_bindings(expression, names);
        }
        ClickProposition::At { proposition, .. } => {
            collect_click_proposition_referenced_bindings(proposition, names);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_proposition_referenced_bindings(left, names);
            collect_click_proposition_referenced_bindings(right, names);
        }
        ClickProposition::Not(body) => collect_click_proposition_referenced_bindings(body, names),
        ClickProposition::ForAll { name, body, .. }
        | ClickProposition::Exists { name, body, .. } => {
            let previous = N::binder(name).is_some_and(|name| N::leave_scope(names, &name));
            collect_click_proposition_referenced_bindings(body, names);
            let _ = N::binder(name).is_some_and(|name| N::leave_scope(names, &name));
            if previous && let Some(name) = N::binder(name) {
                names.insert(name);
            }
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
            ..
        } => {
            collect_contract_expression_referenced_bindings(start, names);
            collect_contract_expression_referenced_bindings(end, names);
            let previous = N::binder(item).is_some_and(|name| N::leave_scope(names, &name));
            collect_click_proposition_referenced_bindings(body, names);
            let _ = N::binder(item).is_some_and(|name| N::leave_scope(names, &name));
            if previous && let Some(name) = N::binder(item) {
                names.insert(name);
            }
        }
        ClickProposition::PredicateCall { name, .. }
            if crate::kernel::TerminationAtomKind::from_spelling(name).is_some() => {}
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_bindings(argument, names);
            }
        }
    }
}

pub(in crate::surface) fn contract_let_substitutions(
    bindings: &[ContractLetBinding],
) -> BTreeMap<String, ContractExpression> {
    bindings
        .iter()
        .filter_map(|binding| {
            // Mathematical lets remain abbreviations until Integer lowering.
            // Substituting them here duplicates every referenced tree and
            // makes repeated binary let chains exponential in source size.
            // A machine `let` at an 8- or 16-bit type whose value does
            // arithmetic stays a binding too: its value's operators are that
            // type's (G2), which only the typed binding records.
            (binding.click_type != Some(ClickType::Integer)
                && !narrow_typed_arithmetic_let(binding))
            .then(|| {
                binding
                    .value()
                    .map(|value| (binding.name.clone(), value.clone()))
            })
            .flatten()
        })
        .collect()
}

/// Whether `binding` is `let name: T = value;` at an 8- or 16-bit `T` with
/// arithmetic at the root of its value.
fn narrow_typed_arithmetic_let(binding: &ContractLetBinding) -> bool {
    binding
        .value()
        .is_some_and(|value| narrow_typed_arithmetic(binding.click_type.as_ref(), value))
}

/// Whether `value` at type `click_type` is arithmetic at an 8- or 16-bit
/// type: its operators are that type's (G2), which spelling the value
/// alone, outside its typed binding, would lose to C's promotion.
pub(in crate::surface) fn narrow_typed_arithmetic(
    click_type: Option<&ClickType>,
    value: &ContractExpression,
) -> bool {
    matches!(
        click_type,
        Some(ClickType::Program(
            InterfaceType::Int8
                | InterfaceType::UInt8
                | InterfaceType::Int16
                | InterfaceType::UInt16
        ))
    ) && matches!(
        value,
        ContractExpression::Add(..)
            | ContractExpression::Subtract(..)
            | ContractExpression::Multiply(..)
            | ContractExpression::BitwiseAnd(..)
            | ContractExpression::BitwiseOr(..)
            | ContractExpression::BitwiseXor(..)
            | ContractExpression::BitwiseNot(..)
    )
}

/// The new surface name an execution theorem's `as` map gives one resource
/// instance of the target contract. The identity is the semantic key: an
/// unrelated instance that happens to share the declared spelling keeps its
/// own name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct InstanceRename {
    pub(in crate::surface) name: String,
    pub(in crate::surface) identity: crate::kernel::InstanceRef,
    /// The identity the renamed reads take, when the new name denotes a
    /// different instance: a caller's instance bound to a callee's binder.
    /// `None` keeps the identity.
    pub(in crate::surface) target_identity: Option<InstanceId>,
}

/// Nothing is renamed. A values-only pass borrows this instead of allocating
/// an empty map.
static NO_INSTANCE_RENAMES: BTreeMap<String, InstanceRename> = BTreeMap::new();

/// Borrow ambient maps until the selected term tells us which replacements
/// it actually reads. Preparing a substitution never enumerates unrelated keys.
pub(in crate::surface) trait SubstitutionSourceMap: std::fmt::Debug {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression>;
}
impl SubstitutionSourceMap for BTreeMap<crate::kernel::BindingName, ContractExpression> {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        self.get(name)
    }
}
impl SubstitutionSourceMap for BTreeMap<String, ContractExpression> {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        name.named().and_then(|name| self.get(name))
    }
}
impl SubstitutionSourceMap for BTreeMap<SurfaceBinder, ContractExpression> {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        match name {
            crate::kernel::BindingName::Named(name) => {
                self.get(&SurfaceBinder::Written(name.clone()))
            }
            crate::kernel::BindingName::Generated(id) => self.get(&SurfaceBinder::Generated(*id)),
            _ => None,
        }
    }
}
impl SubstitutionSourceMap for BinderMap<ContractExpression> {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        self.get(name)
    }
}
impl SubstitutionSourceMap for PersistentBinderMap<ContractExpression> {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        self.get(name)
    }
}
impl SubstitutionSourceMap for BTreeMap<&str, ContractExpression> {
    fn replacement(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        name.named().and_then(|name| self.get(name))
    }
}

/// What one substitution pass replaces: values keyed by the name they replace,
/// and instance renames keyed by the declared instance name.
///
/// The two are separate maps because they replace different things. A value
/// substitution rewrites a whole expression wherever that name is read; a
/// rename only respells a resource instance, in the owner of a resource field
/// and in the binder of a named clause, and only where the instance identity
/// matches. Encoding a rename as a value would need a sentinel expression
/// shape, which every other reader of the map would then have to know about.
#[derive(Clone, Debug)]
pub(in crate::surface) struct ContractSubstitutions<'a> {
    source: Option<&'a dyn SubstitutionSourceMap>,
    values: PersistentBinderMap<ContractExpression>,
    program_values: PersistentMap<
        crate::kernel::BindingName,
        (ContractExpression, Arc<[crate::kernel::BindingName]>),
    >,
    references: PersistentBinderMap<Arc<[crate::kernel::BindingName]>>,
    free_references: PersistentMap<crate::kernel::BindingName, usize>,
    instance_renames: Cow<'a, BTreeMap<String, InstanceRename>>,
    body_instance: Option<(String, InstanceId)>,
    /// Whether a scalar field of the resource body being defined is replaced
    /// by the C name the kernel binds it to (see `resource_body_program_expression`).
    body_fields_as_program_names: bool,
    body_field_values: Option<&'a BTreeMap<String, ContractExpression>>,
    contract_result_only: bool,
    current_program_values: bool,
    call_captures: Option<&'a crate::surface::RecordedStates>,
    /// When set, a C declaration is written by its source name wherever that
    /// name resolves to it in these locals and no binder here shadows it, as
    /// the parser reads a proof that writes the name.
    source_names: Option<(
        &'a crate::kernel::LocalEnvironment,
        Cow<'a, BTreeSet<String>>,
    )>,
}

impl<'a> ContractSubstitutions<'a> {
    /// Value substitutions with no instance renamed.
    pub(in crate::surface) fn new<M: SubstitutionSourceMap>(values: &'a M) -> Self {
        let mut result = Self::indexed(std::iter::empty());
        result.source = Some(values);
        result
    }
    fn selected(&self, names: impl IntoIterator<Item = crate::kernel::BindingName>) -> Self {
        let Some(source) = self.source else {
            return self.clone();
        };
        let mut selected = self.clone();
        selected.source = None;
        for name in names {
            if let Some(value) = source.replacement(&name) {
                if matches!(
                    name,
                    crate::kernel::BindingName::Named(_) | crate::kernel::BindingName::Generated(_)
                ) {
                    selected.insert_value(name.clone().into(), value.clone());
                } else {
                    selected.insert_program_value(name.clone(), value.clone());
                }
            }
            if name.named().is_none()
                && let Some(spelling) = name.source_spelling()
            {
                let spelling = crate::kernel::BindingName::from(spelling);
                if let Some(value) = source.replacement(&spelling) {
                    selected.insert_value(spelling.into(), value.clone());
                }
            }
        }
        if self.contract_result_only {
            let name = crate::kernel::BindingName::from("result");
            if let Some(value) = source.replacement(&name) {
                selected.insert_value(name.into(), value.clone());
            }
        }
        selected
    }
    fn indexed(values: impl Iterator<Item = (SurfaceBinder, ContractExpression)>) -> Self {
        let mut result = Self {
            source: None,
            values: PersistentBinderMap::default(),
            program_values: PersistentMap::default(),
            references: PersistentBinderMap::default(),
            free_references: PersistentMap::default(),
            instance_renames: Cow::Borrowed(&NO_INSTANCE_RENAMES),
            body_instance: None,
            body_fields_as_program_names: false,
            body_field_values: None,
            contract_result_only: false,
            current_program_values: false,
            source_names: None,
            call_captures: None,
        };
        for (name, value) in values {
            result.insert_value(name, value);
        }
        result
    }
    fn insert_program_value(
        &mut self,
        name: crate::kernel::BindingName,
        value: ContractExpression,
    ) {
        if let Some((_, references)) = self.program_values.get(&name) {
            for binding in references.iter() {
                let count = *self
                    .free_references
                    .get(binding)
                    .expect("indexed program replacement");
                if count == 1 {
                    self.free_references.remove(binding);
                } else {
                    self.free_references.insert(binding.clone(), count - 1);
                }
            }
        }
        let references: Arc<[_]> = contract_expression_referenced_bindings(&value)
            .into_iter()
            .collect();
        for binding in references.iter() {
            let count = self.free_references.get(binding).copied().unwrap_or(0);
            self.free_references.insert(binding.clone(), count + 1);
        }
        self.program_values.insert(name, (value, references));
    }

    fn program_value(&self, name: &crate::kernel::BindingName) -> Option<&ContractExpression> {
        self.program_values
            .get(name)
            .map(|(value, _)| value)
            .or_else(|| self.value(name))
    }

    fn remove_value(&mut self, name: &SurfaceBinder) {
        if let Some(references) = self.references.get(name) {
            for binding in references.iter() {
                let count = *self
                    .free_references
                    .get(binding)
                    .expect("indexed replacement reference");
                if count == 1 {
                    self.free_references.remove(binding);
                } else {
                    self.free_references.insert(binding.clone(), count - 1);
                }
            }
        }
        self.values.remove(name);
        self.references.remove(name);
    }
    fn insert_value(&mut self, name: SurfaceBinder, value: ContractExpression) {
        self.remove_value(&name);
        let references: Arc<[_]> = contract_expression_referenced_bindings(&value)
            .into_iter()
            .collect();
        for binding in references.iter() {
            let count = self.free_references.get(binding).copied().unwrap_or(0);
            self.free_references.insert(binding.clone(), count + 1);
        }
        self.references.insert(name.clone(), references);
        self.values.insert(name, value);
    }

    /// Write each C declaration by its source name where it resolves in
    /// `locals`, and exact call captures by their recorded call result.
    pub(in crate::surface) fn with_source_names(
        values: &'a BTreeMap<String, ContractExpression>,
        locals: &'a crate::kernel::LocalEnvironment,
        call_captures: Option<&'a crate::surface::RecordedStates>,
    ) -> Self {
        Self {
            call_captures,
            source_names: Some((locals, Cow::Owned(BTreeSet::new()))),
            ..Self::new(values)
        }
    }

    fn call_capture(&self, name: &crate::kernel::BindingName) -> Option<ContractExpression> {
        let points = self.call_captures?;
        let (locals, _) = self.source_names.as_ref()?;
        if !name
            .local_id()
            .is_some_and(crate::kernel::LocalBindingId::is_temporary)
        {
            return None;
        }
        points.call_capture_expression(name, locals.get(name)?, None)
    }

    /// The source name `name` is written as here, if any.
    fn source_name(&self, name: &crate::kernel::BindingName) -> Option<String> {
        let (locals, bound) = self.source_names.as_ref()?;
        let source = locals.active_source_name(name)?;
        (!bound.contains(source)).then(|| source.to_owned())
    }

    /// Bind the postcondition return value without changing source C bindings
    /// or expressions read in historical states.
    pub(in crate::surface) fn for_contract_result(
        values: &'a BTreeMap<String, ContractExpression>,
    ) -> Self {
        Self {
            contract_result_only: true,
            ..Self::new(values)
        }
    }

    pub(in crate::surface) fn is_contract_result_binding(&self) -> bool {
        self.contract_result_only
    }

    /// Capture current C values without replacing the storage named by `&x`
    /// or changing a value explicitly read from a historical state.
    pub(in crate::surface) fn for_current_program_values(
        values: &'a BTreeMap<String, ContractExpression>,
    ) -> Self {
        Self {
            current_program_values: true,
            ..Self::new(values)
        }
    }

    /// Value substitutions that also spell each scalar field of the resource
    /// body being defined as the C name the kernel binds it to while folding
    /// or unfolding. Definition validation reads a field-bearing body this
    /// way, so a field and a matched constructor payload are checked alike.
    pub(in crate::surface) fn with_body_fields_as_program_names(
        values: &'a BTreeMap<String, ContractExpression>,
    ) -> Self {
        Self {
            body_fields_as_program_names: true,
            ..Self::new(values)
        }
    }

    /// Value substitutions together with the renames an execution theorem's
    /// `as` map states for the target contract's proof parameters.
    pub(in crate::surface) fn with_instance_renames<M: SubstitutionSourceMap>(
        values: &'a M,
        instance_renames: &'a BTreeMap<String, InstanceRename>,
    ) -> Self {
        Self {
            instance_renames: Cow::Borrowed(instance_renames),
            ..Self::new(values)
        }
    }

    /// Instantiate a resource body's own field reads as reads of the opened instance.
    pub(in crate::surface) fn with_body_instance<M: SubstitutionSourceMap>(
        values: &'a M,
        name: String,
        identity: InstanceId,
    ) -> Self {
        Self {
            body_instance: Some((name, identity)),
            ..Self::new(values)
        }
    }

    /// Instantiate the body of an explicit fold with its written field
    /// initializers. These are definition-bound fields, not reads of a
    /// newly constructed (and not yet owned) instance.
    pub(in crate::surface) fn for_fold_body(
        values: &'a BTreeMap<String, ContractExpression>,
        instance_renames: &'a BTreeMap<String, InstanceRename>,
    ) -> Self {
        Self {
            body_field_values: Some(values),
            ..Self::with_instance_renames(values, instance_renames)
        }
    }

    fn value<Q: binders::BinderKey + ?Sized>(&self, name: &Q) -> Option<&ContractExpression> {
        self.values.get(name)
    }

    /// The new surface name for the instance `owner`, when a rename was
    /// recorded for exactly that instance identity.
    pub(in crate::surface) fn instance_rename(
        &self,
        owner: &str,
        identity: impl Into<crate::kernel::InstanceRef>,
    ) -> Option<String> {
        let identity = identity.into();
        self.instance_renames
            .get(owner)
            .filter(|rename| rename.identity == identity)
            .map(|rename| rename.name.clone())
    }

    /// The new name and identity of the instance `owner`, when a rename was
    /// recorded for exactly that instance identity.
    fn instance_rename_target(
        &self,
        owner: &str,
        identity: crate::kernel::InstanceRef,
    ) -> Option<(String, crate::kernel::InstanceRef)> {
        if identity == crate::kernel::InstanceRef::Body
            && let Some((name, target)) = &self.body_instance
        {
            return Some((name.clone(), (*target).into()));
        }
        self.instance_renames
            .get(owner)
            .filter(|rename| rename.identity == identity)
            .map(|rename| {
                (
                    rename.name.clone(),
                    rename.target_identity.map_or(identity, Into::into),
                )
            })
    }

    /// The same pass under a binder that shadows `name`: inside that body the
    /// name is a binding, not something this pass replaces.
    fn without_binding(&self, name: &SurfaceBinder) -> Self {
        let mut result = self.clone();
        result.remove_value(name);
        if let Some(name) = name.written() {
            if result.instance_renames.contains_key(name) {
                result.instance_renames.to_mut().remove(name);
            }
            if let Some((_, bound)) = &mut result.source_names {
                bound.to_mut().insert(name.to_owned());
            }
        }
        result
    }
}

impl<'a> From<&'a BinderMap<ContractExpression>> for ContractSubstitutions<'a> {
    fn from(values: &'a BinderMap<ContractExpression>) -> Self {
        Self::new(values)
    }
}
impl<'a, N> From<&'a BTreeMap<N, ContractExpression>> for ContractSubstitutions<'a>
where
    BTreeMap<N, ContractExpression>: SubstitutionSourceMap,
{
    fn from(values: &'a BTreeMap<N, ContractExpression>) -> Self {
        Self::new(values)
    }
}

pub(in crate::surface) fn substitute_contract_expression<'a>(
    expression: &ContractExpression,
    substitutions: impl Into<ContractSubstitutions<'a>>,
) -> Result<ContractExpression, String> {
    substitute_contract_expression_in(expression, &substitutions.into())
}

pub(in crate::surface) fn contract_expression_has_explicit_program_result_reference(
    expression: &ContractExpression,
) -> bool {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            ContractExpression::ProgramBinding(name) if name == "result" => return true,
            ContractExpression::CUnary { operand, .. }
            | ContractExpression::MemoryLoad {
                pointer: operand, ..
            }
            | ContractExpression::Field { base: operand, .. }
            | ContractExpression::Negate(operand)
            | ContractExpression::Exact(operand)
            | ContractExpression::BitwiseNot(operand) => pending.push(operand),
            ContractExpression::ArrayIndex { base, indexes, .. } => {
                pending.push(base);
                pending.extend(indexes.iter());
            }
            crate::surface::binary_contract_expression!(left, right) => {
                pending.extend([left.as_ref(), right.as_ref()])
            }
            _ => {}
        }
    }
    false
}

// Pure functions have declared machine parameter types just as C functions do.
// Keep the conversion in both the application and its unfolded body: otherwise
// f(0) and f(word) after word == 0 name different typed applications, and a
// narrowing call can unfold the unconverted argument.
pub(in crate::surface) fn pure_function_parameter_scalar_type(
    parameter: &FunctionParameter,
) -> Option<ProgramType> {
    pure_function_scalar_type(parameter.click_type())
}

fn pure_function_scalar_type(click_type: &ClickType) -> Option<ProgramType> {
    let interface_type = click_type.interface_type()?;
    let target_type = interface_type.to_kernel_type();
    if !matches!(
        target_type,
        ProgramType::Bool
            | ProgramType::Int8
            | ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::UInt64
            | ProgramType::Int128
            | ProgramType::UInt128
            | ProgramType::Float32
            | ProgramType::Float64
    ) {
        return None;
    }
    Some(target_type)
}

pub(in crate::surface) fn pure_function_result_scalar_type(
    definition: &ClickFunctionDefinition,
) -> Option<ProgramType> {
    pure_function_scalar_type(definition.return_type()).filter(|ty| *ty != ProgramType::Bool)
}

/// The defining equality uses the same numeric return conversion as the
/// registered body. Pointer results retain their existing selected views.
pub(in crate::surface) fn pure_function_result_value(
    definition: &ClickFunctionDefinition,
    value: ContractExpression,
) -> ContractExpression {
    if definition.return_type() == &ClickType::Integer {
        // The declaration supplies the carrier even when the body consists
        // only of contextual numerals (for example, `if P { 1 } else { 0 }`).
        // Keep that context in the defining equation used by `unfold`.
        return ContractExpression::IntegerContext(Box::new(value));
    }
    let Some(target_type) = pure_function_result_scalar_type(definition) else {
        return value;
    };
    let lowered = ProgramExpression::Cast {
        expression: Box::new(
            contract_expression_as_program_expression(&value)
                .unwrap_or(ProgramExpression::Value(int32(0))),
        ),
        target_type,
        // At an 8- or 16-bit result the body's arithmetic is at that type
        // (G2); any other result keeps C's conversion as before.
        integer_mode: if matches!(
            target_type,
            ProgramType::Int8 | ProgramType::UInt8 | ProgramType::Int16 | ProgramType::UInt16
        ) {
            crate::kernel::IntegerCastMode::ResultConversion
        } else {
            crate::kernel::IntegerCastMode::CConversion
        },
        pointee_struct: None,
        pointee_struct_size: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    ContractExpression::CUnary {
        operand: Box::new(value),
        lowered,
    }
}

/// [`pure_function_parameter_argument`] for an argument whose type is
/// known: an argument already of the parameter's type needs no conversion,
/// so the instantiated body reads it as written, `cd(n - 1)` rather than
/// `cd(n as int32 - 1)`. The conversion is a no-op there, so the lowered body
/// is the same either way; only its spelling differs.
pub(in crate::surface) fn pure_function_parameter_argument_of_type(
    parameter: &FunctionParameter,
    argument: &ContractExpression,
    argument_type: Option<&crate::surface::ClickType>,
) -> ContractExpression {
    if argument_type.is_some_and(|argument_type| argument_type == parameter.click_type()) {
        return argument.clone();
    }
    // A `uint8` byte parameter reads unsigned bytes through a signed
    // character pointer, as a predicate's does ([`character_byte_view`]):
    // a string literal passed for `s: uint8[]` is read as `uint8`.
    if let Some(crate::surface::ClickType::Program(actual)) = argument_type
        && let Some(expected) = parameter.click_type().interface_type()
        && needs_character_byte_view(*actual, expected.to_kernel_type())
        && let Some(pointer) = contract_expression_as_program_expression(argument)
    {
        return ContractExpression::CUnary {
            operand: Box::new(argument.clone()),
            lowered: ProgramExpression::Cast {
                expression: Box::new(pointer),
                target_type: crate::kernel::ProgramType::UInt8Pointer,
                integer_mode: crate::kernel::IntegerCastMode::PointerCoercion,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        };
    }
    pure_function_parameter_argument(parameter, argument)
}

pub(in crate::surface) fn pure_function_parameter_argument(
    parameter: &FunctionParameter,
    argument: &ContractExpression,
) -> ContractExpression {
    let mut literal = argument;
    while let ContractExpression::Old(inner) = literal {
        literal = inner;
    }
    if let Some(ty) = parameter.click_type().interface_type()
        && argument_is_null_pointer_constant(literal, ty)
    {
        return ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::typed_pointer(Address::null(), ty.to_kernel_type()),
        ));
    }
    let Some((target_type, integer_mode)) = pure_function_parameter_conversion(parameter) else {
        return argument.clone();
    };
    ContractExpression::CUnary {
        operand: Box::new(argument.clone()),
        // CUnary's operand is authoritative during lowering. Retain an exact
        // C spelling when one exists for printing and C-fragment substitution.
        lowered: ProgramExpression::Cast {
            expression: Box::new(
                contract_expression_as_program_expression(argument)
                    .unwrap_or(ProgramExpression::Value(int32(0))),
            ),
            target_type,
            integer_mode,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    }
}

/// Implicit argument conversions also apply when a helper's body is unfolded.
/// Unlike an authored void-pointer cast, the object-pointer coercion retains
/// the caller's provenance and selected bounds.
pub(in crate::surface) fn pure_function_parameter_conversion(
    parameter: &FunctionParameter,
) -> Option<(ProgramType, crate::kernel::IntegerCastMode)> {
    let kernel_type = parameter.click_type().interface_type()?.to_kernel_type();
    if matches!(kernel_type, ProgramType::VoidPointer | ProgramType::Pointer) {
        Some((kernel_type, crate::kernel::IntegerCastMode::PointerCoercion))
    } else {
        pure_function_parameter_scalar_type(parameter)
            .map(|target| (target, crate::kernel::IntegerCastMode::CConversion))
    }
}

/// The compiler-inserted byte view of a C character pointer named `name`.
/// A `uint8` predicate parameter reads unsigned bytes even when the source
/// target's plain `char` is signed. The conversion changes that read type
/// while retaining the source pointer's selected bounds. An authored byte
/// cast uses the separate explicit-cast rule and can widen to the root.
pub(in crate::surface) fn character_byte_view(
    name: impl Into<crate::kernel::BindingName>,
) -> ContractExpression {
    let name = name.into();
    ContractExpression::CUnary {
        operand: Box::new(ContractExpression::ProgramExpression(
            ProgramExpression::Variable(name.clone()),
        )),
        lowered: ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Variable(name.clone())),
            target_type: crate::kernel::ProgramType::UInt8Pointer,
            integer_mode: crate::kernel::IntegerCastMode::PointerCoercion,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    }
}

/// The pointer a [`character_byte_view`] views, if `expression` is one.
pub(in crate::surface) fn character_byte_view_name(
    expression: &ContractExpression,
) -> Option<&str> {
    let ContractExpression::CUnary { operand, lowered } = expression else {
        return None;
    };
    let (
        ContractExpression::ProgramExpression(ProgramExpression::Variable(name)),
        ProgramExpression::Cast {
            expression,
            target_type: crate::kernel::ProgramType::UInt8Pointer,
            pointee_struct: None,
            pointee_volatile: false,
            ..
        },
    ) = (operand.as_ref(), lowered)
    else {
        return None;
    };
    matches!(expression.as_ref(), ProgramExpression::Variable(inner) if inner == name)
        .then(|| name.named())
        .flatten()
}

/// Whether a value of C type `actual` passed where kernel type `expected`
/// is read needs the explicit [`character_byte_view`]: `expected` is
/// `uint8` bytes and `actual` is a signed character pointer or array.
pub(in crate::surface) fn needs_character_byte_view(
    actual: InterfaceType,
    expected: crate::kernel::ProgramType,
) -> bool {
    use crate::languages::c::syntax::PlainChar;
    matches!(
        expected,
        crate::kernel::ProgramType::UInt8Pointer | crate::kernel::ProgramType::UInt8Array(_)
    ) && matches!(
        actual,
        InterfaceType::CharPointer(PlainChar::Signed)
            | InterfaceType::CharArray(PlainChar::Signed, _)
            | InterfaceType::Int8Pointer
            | InterfaceType::Int8Array(_)
    )
}

/// Elaborates the C-string bridge in the top-level predicate calls of a
/// proposition: an argument that directly names a C value of signed
/// character pointer type, passed to a parameter of `uint8` bytes, becomes the
/// explicit [`character_byte_view`] of that value. `type_of` gives the C type
/// of a name in scope. Calls under a binder are left alone, since a binder may
/// shadow the name; their arguments still lower through the same view.
pub(in crate::surface) fn elaborate_character_byte_views(
    proposition: &ClickProposition,
    predicates: &PredicateEnvironment,
    type_of: &dyn Fn(&str) -> Option<InterfaceType>,
) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::PredicateCall { name, arguments } => {
            let definition = predicates.get(name)?;
            let mut changed = false;
            let arguments = arguments
                .iter()
                .zip(definition.parameters())
                .map(|(argument, parameter)| {
                    let named = match argument {
                        ContractExpression::ProgramExpression(ProgramExpression::Variable(
                            crate::kernel::BindingName::Named(name),
                        ))
                        | ContractExpression::Binding(name)
                        | ContractExpression::ProgramBinding(name) => Some(name),
                        _ => None,
                    };
                    match (named, parameter.click_type()) {
                        (Some(named), ClickType::Program(expected))
                            if type_of(named).is_some_and(|actual| {
                                needs_character_byte_view(actual, expected.to_kernel_type())
                            }) =>
                        {
                            changed = true;
                            character_byte_view(named)
                        }
                        _ => argument.clone(),
                    }
                })
                .collect::<Vec<_>>();
            changed.then(|| ClickProposition::PredicateCall {
                name: name.clone(),
                arguments,
            })
        }
        _ => None,
    }
}

pub(in crate::surface) fn contract_c_unary(
    operand: ContractExpression,
    lowered: ProgramExpression,
) -> ContractExpression {
    // Keep member syntax through casts so later instantiation can substitute
    // a state value such as old(p) into the authoritative Surface base.
    // A flattened C fragment cannot represent that substitution.
    if contract_expression_has_explicit_program_result_reference(&operand)
        || matches!(
            &operand,
            ContractExpression::Field { .. } | ContractExpression::CUnary { .. }
        )
    {
        ContractExpression::CUnary {
            operand: Box::new(operand),
            lowered,
        }
    } else {
        ContractExpression::ProgramExpression(lowered)
    }
}

pub(in crate::surface) fn c_unary_with_operand(
    lowered: &ProgramExpression,
    operand: ProgramExpression,
) -> ProgramExpression {
    let mut lowered = lowered.clone();
    match &mut lowered {
        ProgramExpression::AddressOf(expression) => {
            let mut operand = operand;
            // A member address selects the field's own bounds. Rebuilding
            // its source operand must keep that selection around the new
            // field pointer, including after a binding substitution.
            if let (
                ProgramExpression::TypedLoad {
                    pointer: original, ..
                },
                ProgramExpression::TypedLoad {
                    pointer: replacement,
                    ..
                },
            ) = (expression.as_ref(), &mut operand)
                && let ProgramExpression::Subobject { width, .. } = original.as_ref()
                && !matches!(replacement.as_ref(), ProgramExpression::Subobject { .. })
            {
                **replacement = ProgramExpression::Subobject {
                    pointer: Box::new((**replacement).clone()),
                    width: *width,
                };
            }
            **expression = operand;
        }
        ProgramExpression::Cast { expression, .. }
        | ProgramExpression::CheckedObjectAddress(expression)
        | ProgramExpression::Load(expression) => **expression = operand,
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. }
        | ProgramExpression::TypedLoad { pointer, .. } => **pointer = operand,
        _ => unreachable!("CUnary stores a unary C operation"),
    }
    lowered
}

/// A projection rooted at an explicit C binding keeps that namespace even
/// though its lowered C fragment no longer carries the surface wrapper.
pub(in crate::surface) fn contract_expression_has_explicit_program_result_base(
    mut expression: &ContractExpression,
) -> bool {
    loop {
        match expression {
            ContractExpression::ProgramBinding(name) => return name == "result",
            ContractExpression::CUnary { operand: base, .. }
            | ContractExpression::MemoryLoad { pointer: base, .. }
            | ContractExpression::Field { base, .. }
            | ContractExpression::ArrayIndex { base, .. }
            | ContractExpression::Index(base, _) => expression = base,
            _ => return false,
        }
    }
}

pub(in crate::surface) fn substitute_contract_expression_in(
    expression: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractExpression, String> {
    if substitutions.source.is_some() {
        let mut names = BTreeSet::<crate::kernel::BindingName>::new();
        collect_contract_expression_referenced_bindings(expression, &mut names);
        let selected = substitutions.selected(names);
        return substitute_contract_expression_in(expression, &selected);
    }

    if matches!(expression, ContractExpression::Let { .. }) {
        return substitute_contract_let_chain(expression, substitutions);
    }
    substitute_contract_expression_node(expression, substitutions)
}

/// Retain scope snapshots and rebuild from the tail, preserving the original
/// order of capture renaming and initializer substitution without recursive
/// frames for every declaration. Persistent binding maps share each prefix.
fn substitute_contract_let_chain(
    expression: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractExpression, String> {
    let mut current = expression;
    let mut scoped = substitutions.clone();
    let mut frames = Vec::new();
    while let ContractExpression::Let {
        name,
        click_type,
        value,
        body,
    } = current
    {
        let mut inside = scoped.without_binding(name);
        let renamed = if substitutions_reference_name(&inside, name) {
            let fresh = SurfaceBinder::fresh();
            inside.insert_value(name.clone(), fresh.reference());
            fresh
        } else {
            name.clone()
        };
        frames.push((renamed, click_type.clone(), value.as_ref(), scoped));
        scoped = inside;
        current = body;
    }
    let mut result = substitute_contract_expression_in(current, &scoped)?;
    for (name, click_type, value, before) in frames.into_iter().rev() {
        let value = substitute_contract_expression_in(value, &before)?;
        result = ContractExpression::Let {
            name,
            click_type,
            value: Box::new(value),
            body: Box::new(result),
        };
    }
    Ok(result)
}

// Keep the large ordinary expression match out of the frame of each fold.
fn substitute_contract_expression_node(
    expression: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractExpression, String> {
    if let ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) = expression
        && let Some(value) = substitutions.program_value(name)
    {
        return Ok(value.clone());
    }
    match expression {
        ContractExpression::IntegerContext(value) => Ok(ContractExpression::IntegerContext(
            Box::new(substitute_contract_expression_in(value, substitutions)?),
        )),

        ContractExpression::Proposition(proposition) => Ok(ContractExpression::Proposition(
            Box::new(substitute_click_proposition_in(proposition, substitutions)?),
        )),
        ContractExpression::Resource(subject) => Ok(ContractExpression::Resource(Box::new(
            substitute_resource_subject(subject, substitutions)?,
        ))),
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => Ok(expression.clone()),
        ContractExpression::Lambda {
            parameters,
            result,
            body,
        } => {
            let mut scoped = substitutions.clone();
            for (name, _) in parameters {
                scoped = scoped.without_binding(name);
            }
            let parameters = parameters
                .iter()
                .map(|(name, ty)| {
                    if !substitutions_reference_name(&scoped, name) {
                        return (name.clone(), ty.clone());
                    }
                    let fresh = SurfaceBinder::fresh();
                    scoped.insert_value(name.clone(), fresh.reference());
                    (fresh, ty.clone())
                })
                .collect();
            let body = substitute_contract_expression_in(body, &scoped)?;
            Ok(ContractExpression::Lambda {
                parameters,
                result: result.clone(),
                body: Box::new(body),
            })
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => Ok(ContractExpression::Apply {
            function: Box::new(substitute_contract_expression_in(function, substitutions)?),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),

        ContractExpression::Old(_) | ContractExpression::At { .. }
            if substitutions.current_program_values =>
        {
            Ok(expression.clone())
        }
        ContractExpression::CUnary { operand, lowered }
            if substitutions.current_program_values
                && matches!(
                    lowered,
                    ProgramExpression::AddressOf(_) | ProgramExpression::CheckedObjectAddress(_)
                )
                && matches!(
                    contract_expression_as_program_expression(operand),
                    Some(ProgramExpression::Variable(_))
                ) =>
        {
            Ok(expression.clone())
        }
        ContractExpression::CUnary { operand, lowered } => {
            let operand = substitute_contract_expression_in(operand, substitutions)?;
            let fragment = match contract_expression_as_program_expression(&operand) {
                Some(fragment) => fragment,
                None if matches!(
                    lowered,
                    ProgramExpression::Cast { .. } | ProgramExpression::TypedLoad { .. }
                ) =>
                {
                    ProgramExpression::Value(int32(0))
                }
                None => return Err("C unary operand is not a C expression".to_string()),
            };
            Ok(ContractExpression::CUnary {
                lowered: c_unary_with_operand(lowered, fragment),
                operand: Box::new(operand),
            })
        }
        ContractExpression::MemoryLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
        } => Ok(ContractExpression::MemoryLoad {
            pointer: Box::new(substitute_contract_expression_in(pointer, substitutions)?),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
        }),

        ContractExpression::IntegerLiteral(_) => Ok(expression.clone()),
        ContractExpression::ResourceField(access)
            if let Some(fields) = substitutions.body_field_values
                && access.identity == crate::kernel::InstanceRef::Body
                && access.children.is_empty() =>
        {
            fields.get(&access.field).cloned().ok_or_else(|| {
                format!(
                    "fold body field `{}` has no written initializer",
                    access.field
                )
            })
        }
        ContractExpression::ResourceField(_)
            if substitutions.body_fields_as_program_names
                && let Some(name) = resource_body_program_expression(expression) =>
        {
            Ok(ContractExpression::ProgramExpression(name))
        }
        ContractExpression::ResourceField(access) => Ok(ContractExpression::ResourceField(
            match substitutions.instance_rename_target(&access.owner, access.identity) {
                Some((owner, identity)) => ResourceFieldAccess {
                    owner,
                    identity,
                    ..access.clone()
                },
                None => access.clone(),
            },
        )),
        ContractExpression::Negate(inner) => Ok(ContractExpression::Negate(Box::new(
            substitute_contract_expression_in(inner, substitutions)?,
        ))),
        ContractExpression::Exact(inner) => Ok(ContractExpression::Exact(Box::new(
            substitute_contract_expression_in(inner, substitutions)?,
        ))),
        ContractExpression::AlgebraicVariable { name, .. } => Ok(substitutions
            .value(name)
            .cloned()
            .unwrap_or_else(|| expression.clone())),
        ContractExpression::Binding(name) => Ok(substitutions
            .value(name)
            .cloned()
            .unwrap_or_else(|| expression.clone())),
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => Ok(ContractExpression::AlgebraicConstructor {
            algebraic_type: algebraic_type.clone(),
            variant: variant.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            Ok(ContractExpression::AlgebraicMatch {
                scrutinee: Box::new(substitute_contract_expression_in(scrutinee, substitutions)?),
                arms: arms
                    .iter()
                    .map(|arm| prepare_contract_match_arm(arm, substitutions))
                    .collect::<Result<Vec<_>, String>>()?,
            })
        }
        ContractExpression::SequenceLiteral(elements) => Ok(ContractExpression::SequenceLiteral(
            elements
                .iter()
                .map(|element| substitute_contract_expression_in(element, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        ContractExpression::SequenceConcat(left, right) => Ok(ContractExpression::SequenceConcat(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::QualifiedC { .. } | ContractExpression::ProgramBinding(_) => {
            Ok(expression.clone())
        }
        ContractExpression::ArrayIndex {
            base,
            indexes,
            dimensions,
            lowered,
        } => Ok(ContractExpression::ArrayIndex {
            base: Box::new(substitute_contract_expression_in(base, substitutions)?),
            indexes: indexes
                .iter()
                .map(|index| substitute_contract_expression_in(index, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            dimensions: dimensions.clone(),
            lowered: if substitutions.is_contract_result_binding()
                && (contract_expression_has_explicit_program_result_reference(base)
                    || indexes
                        .iter()
                        .any(contract_expression_has_explicit_program_result_reference))
            {
                lowered.clone()
            } else {
                substitute_program_expression_in(lowered, substitutions)?
            },
        }),
        ContractExpression::ResourceWildcard => Ok(expression.clone()),
        ContractExpression::ResourceCount(resource) => {
            let ResourceClause::Declared {
                type_schema,
                resource_type_arguments,
                resource_arguments,
                access,
                kind,
                name,
                arguments,
                parameter_types,
            } = resource.as_ref()
            else {
                return Err("`count(...)` expects a declared resource".to_string());
            };
            Ok(ContractExpression::ResourceCount(Box::new(
                ResourceClause::Declared {
                    type_schema: type_schema.clone(),
                    resource_type_arguments: resource_type_arguments
                        .iter()
                        .map(|resource| {
                            crate::surface::verification::substitute_resource_clause_for_summary_in(
                                resource,
                                substitutions,
                            )
                        })
                        .collect::<Result<_, _>>()?,
                    resource_arguments: resource_arguments.clone(),
                    access: *access,
                    kind: *kind,
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| match argument {
                            ContractExpression::ResourceWildcard => Ok(argument.clone()),
                            argument => substitute_contract_expression_in(argument, substitutions),
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    parameter_types: parameter_types.clone(),
                },
            )))
        }
        ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) => {
            Ok(substitutions
                .value(name)
                .cloned()
                .unwrap_or_else(|| expression.clone()))
        }
        ContractExpression::ProgramExpression(expression) => {
            substitute_program_expression_as_contract_in(expression, substitutions)
        }
        ContractExpression::Field {
            base,
            field,
            lowered,
            offset_bytes,
            pointee_struct,
        } => {
            let substituted_base = substitute_contract_expression_in(base, substitutions)?;
            // SymbolicMemory state field lowering uses the Surface base and only the
            // operation/type shape of `lowered`. An `old(...)` base cannot
            // be embedded in the cached C fragment.
            // A call's parameter object is read at that call's parameter
            // point, from its own layout, when the read is lowered.
            let state_base = matches!(
                &substituted_base,
                ContractExpression::Old(_)
                    | ContractExpression::At { .. }
                    | ContractExpression::Exact(_)
                    | ContractExpression::RegionParameter { .. }
            ) || super::annotations::region_parameter_read(&substituted_base)
                .is_some();
            Ok(ContractExpression::Field {
                pointee_struct: pointee_struct.clone(),
                base: Box::new(substituted_base),
                field: field.clone(),
                lowered: if state_base
                    || (substitutions.is_contract_result_binding()
                        && contract_expression_has_explicit_program_result_base(base))
                {
                    lowered.clone()
                } else {
                    substitute_program_expression_in(lowered, substitutions)?
                },
                offset_bytes: *offset_bytes,
            })
        }
        ContractExpression::Old(_) | ContractExpression::At { .. }
            if substitutions.contract_result_only =>
        {
            Ok(expression.clone())
        }
        ContractExpression::Old(expression) => Ok(ContractExpression::Old(Box::new(
            substitute_contract_expression_in(expression, substitutions)?,
        ))),
        ContractExpression::At {
            selector,
            expression,
        } => Ok(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(substitute_contract_expression_in(
                expression,
                substitutions,
            )?),
        }),
        ContractExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::RustShiftLeft(left, right) => Ok(ContractExpression::RustShiftLeft(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::RustShiftRight(left, right) => Ok(ContractExpression::RustShiftRight(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_contract_expression_in(left, substitutions)?),
            Box::new(substitute_contract_expression_in(right, substitutions)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_contract_expression_in(expression, substitutions)?,
        ))),
        ContractExpression::Index(base, index) => Ok(substituted_index(
            substitute_contract_expression_in(base, substitutions)?,
            substitute_contract_expression_in(index, substitutions)?,
            substitutions,
            !array_reference_selects_state(base),
        )),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => Ok(ContractExpression::If {
            condition: Box::new(substitute_click_proposition_in(condition, substitutions)?),
            then_branch: Box::new(substitute_contract_expression_in(
                then_branch,
                substitutions,
            )?),
            else_branch: Box::new(substitute_contract_expression_in(
                else_branch,
                substitutions,
            )?),
        }),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let scoped = substitutions
                .without_binding(accumulator)
                .without_binding(item);
            let (accumulator, item, body) =
                prepare_contract_range_fold_body(accumulator, item, body, &scoped)?;
            Ok(ContractExpression::RangeFold {
                start: Box::new(substitute_contract_expression_in(start, substitutions)?),
                end: Box::new(substitute_contract_expression_in(end, substitutions)?),
                initial: Box::new(substitute_contract_expression_in(initial, substitutions)?),
                accumulator,
                item,
                body: Box::new(body),
            })
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let scoped = substitutions.without_binding(name);
            let (name, body) = prepare_contract_expression_binding_body(name, body, &scoped)?;
            Ok(ContractExpression::Let {
                name,
                click_type: click_type.clone(),
                value: Box::new(substitute_contract_expression_in(value, substitutions)?),
                body: Box::new(body),
            })
        }
        ContractExpression::MethodCall {
            receiver,
            method,
            arguments,
        } => Ok(ContractExpression::MethodCall {
            receiver: Box::new(substitute_contract_expression_in(receiver, substitutions)?),
            method: method.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ContractExpression::Call { name, arguments } => Ok(ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

fn substitute_program_expression_as_contract_in(
    expression: &ProgramExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractExpression, String> {
    substitute_program_expression_as_contract_with_numerals_in(expression, substitutions, false)
}

pub(in crate::surface) fn substitute_program_expression_as_contract_with_numerals<'a>(
    expression: &ProgramExpression,
    substitutions: impl Into<ContractSubstitutions<'a>>,
    contextual_numerals: bool,
) -> Result<ContractExpression, String> {
    substitute_program_expression_as_contract_with_numerals_in(
        expression,
        &substitutions.into(),
        contextual_numerals,
    )
}

fn substitute_program_expression_as_contract_with_numerals_in(
    expression: &ProgramExpression,
    substitutions: &ContractSubstitutions<'_>,
    contextual_numerals: bool,
) -> Result<ContractExpression, String> {
    if substitutions.source.is_some() {
        let mut names = BTreeSet::<crate::kernel::BindingName>::new();
        collect_program_expression_referenced_bindings(expression, &mut names);
        let selected = substitutions.selected(names);
        return substitute_program_expression_as_contract_with_numerals_in(
            expression,
            &selected,
            contextual_numerals,
        );
    }

    match expression {
        ProgramExpression::Value(ProgramValue::Int32(bits32_constant!(value)))
            if contextual_numerals =>
        {
            let signed = constant_u32(*value) as i32;
            let literal =
                ContractExpression::IntegerLiteral(i64::from(signed).unsigned_abs().to_string());
            Ok(if signed < 0 {
                ContractExpression::Negate(Box::new(literal))
            } else {
                literal
            })
        }
        ProgramExpression::Cast {
            expression: operand,
            ..
        } => {
            let operand = substitute_program_expression_as_contract_with_numerals_in(
                operand,
                substitutions,
                false,
            )?;
            Ok(match contract_expression_as_program_expression(&operand) {
                Some(fragment) => ContractExpression::ProgramExpression(c_unary_with_operand(
                    expression, fragment,
                )),
                None => ContractExpression::CUnary {
                    operand: Box::new(operand),
                    // The authoritative operand carries the state. The
                    // cached C operation supplies only its cast metadata.
                    lowered: expression.clone(),
                },
            })
        }
        ProgramExpression::Value(_) => {
            Ok(ContractExpression::ProgramExpression(expression.clone()))
        }
        // A step's result is spelled by its step.
        ProgramExpression::StepResult { step, origin, .. } => {
            crate::surface::diagnostics::step_result_expression(*step).ok_or_else(|| match origin {
                crate::kernel::StepOrigin::Call(function) => {
                    format!("the result of the call to `{function}` has no source spelling")
                }
                crate::kernel::StepOrigin::Prior(local) => {
                    format!("the value `{local}` held before its update has no source spelling")
                }
                crate::kernel::StepOrigin::Value(what) => {
                    format!("the value of {what} has no source spelling")
                }
                crate::kernel::StepOrigin::Operator(kind) => format!(
                    "the value of {} has no source spelling",
                    crate::surface::diagnostics::describe_operator_kind(*kind)
                ),
            })
        }
        ProgramExpression::Variable(name) => Ok(substitutions
            .program_value(name)
            .cloned()
            .or_else(|| substitutions.call_capture(name))
            .or_else(|| {
                substitutions.source_name(name).map(|source| {
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        source.into(),
                    ))
                })
            })
            .unwrap_or_else(|| ContractExpression::ProgramExpression(expression.clone()))),
        ProgramExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::RustShiftLeft(left, right) => Ok(ContractExpression::RustShiftLeft(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::RustShiftRight(left, right) => Ok(ContractExpression::RustShiftRight(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_program_expression_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        ProgramExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_program_expression_as_contract_with_numerals_in(
                expression,
                substitutions,
                contextual_numerals,
            )?,
        ))),
        ProgramExpression::Index(base, index) => Ok(substituted_index(
            substitute_program_expression_as_contract_with_numerals_in(
                base,
                substitutions,
                contextual_numerals,
            )?,
            substitute_program_expression_as_contract_with_numerals_in(
                index,
                substitutions,
                contextual_numerals,
            )?,
            substitutions,
            true,
        )),
        _ => Ok(ContractExpression::ProgramExpression(
            substitute_program_expression_in(expression, substitutions)?,
        )),
    }
}

fn array_reference_selects_state(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Old(_) | ContractExpression::At { .. } => true,
        ContractExpression::Add(left, right) => {
            array_reference_selects_state(left) || array_reference_selects_state(right)
        }
        ContractExpression::Subtract(left, _) => array_reference_selects_state(left),
        _ => false,
    }
}

// A fold parameter supplies a pointer value, not an array state. For
// example, substituting old(p) in the body's p[k] must read current memory
// through that value; Index(Old(p), k) would instead read the old array.
// An ordinary let expression keeps that distinction writable and replayable.
fn substituted_index(
    base: ContractExpression,
    index: ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
    current_read: bool,
) -> ContractExpression {
    let base = if current_read && substitutions.body_field_values.is_some() {
        let binder = SurfaceBinder::fresh();
        ContractExpression::Let {
            name: binder.clone(),
            click_type: None,
            value: Box::new(base),
            body: Box::new(binder.reference()),
        }
    } else {
        base
    };
    ContractExpression::Index(Box::new(base), Box::new(index))
}

pub(in crate::surface) fn substitute_program_expression<'a>(
    expression: &ProgramExpression,
    substitutions: impl Into<ContractSubstitutions<'a>>,
) -> Result<ProgramExpression, String> {
    substitute_program_expression_in(expression, &substitutions.into())
}

pub(in crate::surface) fn substitute_program_expression_in(
    expression: &ProgramExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ProgramExpression, String> {
    if substitutions.source.is_some() {
        let mut names = BTreeSet::<crate::kernel::BindingName>::new();
        collect_program_expression_referenced_bindings(expression, &mut names);
        let selected = substitutions.selected(names);
        return substitute_program_expression_in(expression, &selected);
    }

    match expression {
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => Ok(expression.clone()),
        ProgramExpression::Variable(name) => {
            let Some(substitution) = substitutions.program_value(name) else {
                return Ok(substitutions.source_name(name).map_or_else(
                    || expression.clone(),
                    |source| ProgramExpression::Variable(source.into()),
                ));
            };
            contract_expression_as_program_expression(substitution).ok_or_else(|| {
                format!(
                    "cannot substitute non-C-fragment expression for `{name}` inside C fragment `{}`",
                    crate::surface::diagnostics::describe_program_expression(expression)
                )
            })
        }
        ProgramExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct,
            pointee_struct_size,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => Ok(ProgramExpression::Cast {
            expression: Box::new(substitute_program_expression_in(expression, substitutions)?),
            target_type: *target_type,
            integer_mode: *integer_mode,
            pointee_struct: pointee_struct.clone(),
            pointee_struct_size: *pointee_struct_size,
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: *explicit_qualification,
        }),
        ProgramExpression::Negate(expression) => Ok(ProgramExpression::Negate(Box::new(
            substitute_program_expression_in(expression, substitutions)?,
        ))),
        ProgramExpression::FloatNegate(expression) => Ok(ProgramExpression::FloatNegate(Box::new(
            substitute_program_expression_in(expression, substitutions)?,
        ))),
        ProgramExpression::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => Ok(ProgramExpression::EnumConstruct {
            enum_type: *enum_type,
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| substitute_program_expression_in(field, substitutions))
                .collect::<Result<_, _>>()?,
        }),
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => Ok(ProgramExpression::EnumField {
            value: Box::new(substitute_program_expression_in(value, substitutions)?),
            variant: variant.clone(),
            index: *index,
        }),
        ProgramExpression::EnumIs { value, variant } => Ok(ProgramExpression::EnumIs {
            value: Box::new(substitute_program_expression_in(value, substitutions)?),
            variant: variant.clone(),
        }),
        ProgramExpression::FloatClassification {
            expression,
            classification,
        } => Ok(ProgramExpression::FloatClassification {
            expression: Box::new(substitute_program_expression_in(expression, substitutions)?),
            classification: *classification,
        }),
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => Ok(ProgramExpression::Ternary {
            condition: Box::new(substitute_program_expression_in(condition, substitutions)?),
            then_branch: Box::new(substitute_program_expression_in(
                then_branch,
                substitutions,
            )?),
            else_branch: Box::new(substitute_program_expression_in(
                else_branch,
                substitutions,
            )?),
        }),
        ProgramExpression::AddressOf(body) | ProgramExpression::CheckedObjectAddress(body)
            if substitutions.current_program_values
                && matches!(body.as_ref(), ProgramExpression::Variable(_)) =>
        {
            Ok(expression.clone())
        }
        ProgramExpression::AddressOf(body) => Ok(ProgramExpression::AddressOf(Box::new(
            substitute_program_expression_in(body, substitutions)?,
        ))),
        ProgramExpression::CheckedObjectAddress(body) => {
            Ok(ProgramExpression::CheckedObjectAddress(Box::new(
                substitute_program_expression_in(body, substitutions)?,
            )))
        }
        ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
            Ok(ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(substitute_program_expression_in(pointer, substitutions)?),
                bytes: *bytes,
            })
        }
        ProgramExpression::Subobject { pointer, width } => Ok(ProgramExpression::Subobject {
            pointer: Box::new(substitute_program_expression_in(pointer, substitutions)?),
            width: *width,
        }),
        ProgramExpression::LessThan(left, right) => Ok(ProgramExpression::LessThan(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::LessEqual(left, right) => Ok(ProgramExpression::LessEqual(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::GreaterThan(left, right) => Ok(ProgramExpression::GreaterThan(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::GreaterEqual(left, right) => Ok(ProgramExpression::GreaterEqual(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Equal(left, right) => Ok(ProgramExpression::Equal(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::NotEqual(left, right) => Ok(ProgramExpression::NotEqual(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Not(body) => Ok(ProgramExpression::Not(Box::new(
            substitute_program_expression_in(body, substitutions)?,
        ))),
        ProgramExpression::And(left, right) => Ok(ProgramExpression::And(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Or(left, right) => Ok(ProgramExpression::Or(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Add(left, right) => Ok(ProgramExpression::Add(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Subtract(left, right) => Ok(ProgramExpression::Subtract(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Multiply(left, right) => Ok(ProgramExpression::Multiply(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Divide(left, right) => Ok(ProgramExpression::Divide(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::Remainder(left, right) => Ok(ProgramExpression::Remainder(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::ShiftLeft(left, right) => Ok(ProgramExpression::ShiftLeft(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::RustShiftLeft(left, right) => Ok(ProgramExpression::RustShiftLeft(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::ShiftRight(left, right) => Ok(ProgramExpression::ShiftRight(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::RustShiftRight(left, right) => Ok(ProgramExpression::RustShiftRight(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::BitwiseAnd(left, right) => Ok(ProgramExpression::BitwiseAnd(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::BitwiseOr(left, right) => Ok(ProgramExpression::BitwiseOr(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::BitwiseXor(left, right) => Ok(ProgramExpression::BitwiseXor(
            Box::new(substitute_program_expression_in(left, substitutions)?),
            Box::new(substitute_program_expression_in(right, substitutions)?),
        )),
        ProgramExpression::BitwiseNot(expression) => Ok(ProgramExpression::BitwiseNot(Box::new(
            substitute_program_expression_in(expression, substitutions)?,
        ))),
        ProgramExpression::Load(body) => Ok(ProgramExpression::Load(Box::new(
            substitute_program_expression_in(body, substitutions)?,
        ))),
        ProgramExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            access_class,
            source,
        } => Ok(ProgramExpression::TypedLoad {
            pointer: Box::new(substitute_program_expression_in(pointer, substitutions)?),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            access_class: access_class.clone(),
            source: source.clone(),
        }),
        ProgramExpression::Index(base, index) => Ok(ProgramExpression::Index(
            Box::new(substitute_program_expression_in(base, substitutions)?),
            Box::new(substitute_program_expression_in(index, substitutions)?),
        )),
    }
}

fn typed_memory_load_fragment(
    pointer: ProgramExpression,
    value_type: ProgramType,
    volatile: bool,
    pointee_constant: bool,
) -> ProgramExpression {
    ProgramExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile,
        pointee_constant,
        access_class: None,
        source: Default::default(),
    }
}

pub(in crate::surface) fn contract_expression_as_program_expression(
    expression: &ContractExpression,
) -> Option<ProgramExpression> {
    contract_expression_as_program_expression_resolving_fields(expression, &|_| None)
}

/// Converts a contract expression to a C fragment, letting `field` supply
/// the C spelling of a resource field access. Inside a resource body a scalar
/// field of the instance being defined is stable model data, which the kernel
/// binds by name exactly as it binds a matched constructor payload; every
/// other field access has no C spelling.
pub(in crate::surface) fn contract_expression_as_program_expression_resolving_fields(
    expression: &ContractExpression,
    field: &dyn Fn(&ResourceFieldAccess) -> Option<ProgramExpression>,
) -> Option<ProgramExpression> {
    let contract_expression_as_program_expression = |expression: &ContractExpression| {
        contract_expression_as_program_expression_resolving_fields(expression, field)
    };
    match expression {
        ContractExpression::IntegerContext(_) => None,

        ContractExpression::Proposition(_) => None,
        ContractExpression::Resource(_) => None,
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => None,
        ContractExpression::Lambda { .. } | ContractExpression::Apply { .. } => None,

        ContractExpression::ResourceField(access) => field(access),
        ContractExpression::IntegerLiteral(value) => {
            let value = value.parse::<u64>().ok()?;
            Some(ProgramExpression::Value(if value <= i32::MAX as u64 {
                int32(value as u32)
            } else if value <= i64::MAX as u64 {
                ProgramValue::Int64(MachineTerm::int64_constant(value as i64))
            } else {
                ProgramValue::UInt64(MachineTerm::uint64_constant(value))
            }))
        }
        ContractExpression::Negate(inner) => {
            if let ContractExpression::IntegerLiteral(value) = inner.as_ref()
                && let Ok(value) = value.parse::<u64>()
                && value <= (i32::MAX as u64) + 1
            {
                return Some(ProgramExpression::Value(int32(
                    0u32.wrapping_sub(value as u32),
                )));
            }
            Some(ProgramExpression::Subtract(
                Box::new(ProgramExpression::Value(int32(0))),
                Box::new(contract_expression_as_program_expression(inner)?),
            ))
        }
        ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicMatch { .. } => None,
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => None,
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::ProgramExpression(expression) => Some(expression.clone()),
        ContractExpression::CUnary { operand, lowered } => Some(c_unary_with_operand(
            lowered,
            contract_expression_as_program_expression(operand)?,
        )),
        ContractExpression::MemoryLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
        } => Some(typed_memory_load_fragment(
            contract_expression_as_program_expression(pointer)?,
            *value_type,
            *volatile,
            *pointee_constant,
        )),
        // Reads rooted at a copied argument need the recorded parameter
        // point, which the cached C fragment cannot represent.
        ContractExpression::Field { lowered, .. }
        | ContractExpression::ArrayIndex { lowered, .. } => {
            super::annotations::region_parameter_read(expression)
                .is_none()
                .then(|| lowered.clone())
        }
        ContractExpression::Binding(name) | ContractExpression::ProgramBinding(name) => {
            Some(ProgramExpression::Variable((name.clone()).into()))
        }
        ContractExpression::ResourceCount(_) => None,
        ContractExpression::ResourceWildcard => None,
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        // An exact read names a state; it has no C spelling.
        ContractExpression::Exact(_) => None,
        ContractExpression::Add(left, right) => Some(ProgramExpression::Add(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(ProgramExpression::Subtract(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(ProgramExpression::Multiply(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(ProgramExpression::Divide(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(ProgramExpression::Remainder(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(ProgramExpression::ShiftLeft(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::RustShiftLeft(left, right) => Some(ProgramExpression::RustShiftLeft(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(ProgramExpression::ShiftRight(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::RustShiftRight(left, right) => Some(ProgramExpression::RustShiftRight(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(ProgramExpression::BitwiseAnd(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(ProgramExpression::BitwiseOr(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(ProgramExpression::BitwiseXor(
            Box::new(contract_expression_as_program_expression(left)?),
            Box::new(contract_expression_as_program_expression(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(ProgramExpression::BitwiseNot(
            Box::new(contract_expression_as_program_expression(expression)?),
        )),
        ContractExpression::Index(base, index) => Some(ProgramExpression::Index(
            Box::new(contract_expression_as_program_expression(base)?),
            Box::new(contract_expression_as_program_expression(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::MethodCall { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

/// The C spelling of an expression inside a resource body, where a scalar
/// field of the resource being defined is stable model data. The kernel binds
/// each C-typed field of an instance by name while it folds or unfolds the
/// body, just as it binds a matched constructor payload, so the field may
/// select a memory-range endpoint or supply a child argument. A field outside
/// a resource body, or of a non-C type, has no C spelling.
pub(in crate::surface) fn resource_body_program_expression(
    expression: &ContractExpression,
) -> Option<ProgramExpression> {
    contract_expression_as_program_expression_resolving_fields(expression, &|access| {
        (access.identity == crate::kernel::InstanceRef::Body
            && access.children.is_empty()
            && access
                .click_type
                .as_ref()
                .is_some_and(|click_type| click_type.interface_type().is_some()))
        .then(|| ProgramExpression::Variable((access.field.clone()).into()))
    })
}

pub(in crate::surface) fn c_comparison_operator(
    operator: ComparisonOperator,
) -> KernelComparisonOperator {
    match operator {
        ComparisonOperator::Equal => KernelComparisonOperator::Equal,
        ComparisonOperator::NotEqual => KernelComparisonOperator::NotEqual,
        ComparisonOperator::In => unreachable!("membership is lowered before C comparisons"),
        ComparisonOperator::LessThan => KernelComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => KernelComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => KernelComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => KernelComparisonOperator::GreaterEqual,
    }
}

pub(in crate::surface) fn contract_expression_to_program_expression(
    expression: &ContractExpression,
) -> Option<ProgramExpression> {
    match expression {
        ContractExpression::IntegerContext(_) => None,

        ContractExpression::Proposition(_) => None,
        ContractExpression::Resource(_) => None,
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => None,
        ContractExpression::Lambda { .. } | ContractExpression::Apply { .. } => None,

        ContractExpression::ResourceField(_) => None,
        ContractExpression::IntegerLiteral(_) | ContractExpression::Negate(_) => {
            resource_argument_to_program_expression(expression).ok()
        }
        ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicMatch { .. } => None,
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => None,
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::ProgramExpression(expression) => Some(expression.clone()),
        ContractExpression::CUnary { operand, lowered } => Some(c_unary_with_operand(
            lowered,
            contract_expression_to_program_expression(operand)?,
        )),
        ContractExpression::MemoryLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
        } => Some(typed_memory_load_fragment(
            contract_expression_to_program_expression(pointer)?,
            *value_type,
            *volatile,
            *pointee_constant,
        )),
        // Reads rooted at a copied argument need the recorded parameter
        // point, which the cached C fragment cannot represent.
        ContractExpression::Field { lowered, .. }
        | ContractExpression::ArrayIndex { lowered, .. } => {
            super::annotations::region_parameter_read(expression)
                .is_none()
                .then(|| lowered.clone())
        }
        ContractExpression::Binding(name) | ContractExpression::ProgramBinding(name) => {
            Some(ProgramExpression::Variable((name.clone()).into()))
        }
        ContractExpression::ResourceCount(_) => None,
        ContractExpression::ResourceWildcard => None,
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        // An exact read names a state; it has no C spelling.
        ContractExpression::Exact(_) => None,
        ContractExpression::Add(left, right) => Some(ProgramExpression::Add(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(ProgramExpression::Subtract(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(ProgramExpression::Multiply(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(ProgramExpression::Divide(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(ProgramExpression::Remainder(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(ProgramExpression::ShiftLeft(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::RustShiftLeft(left, right) => Some(ProgramExpression::RustShiftLeft(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(ProgramExpression::ShiftRight(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::RustShiftRight(left, right) => Some(ProgramExpression::RustShiftRight(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(ProgramExpression::BitwiseAnd(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(ProgramExpression::BitwiseOr(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(ProgramExpression::BitwiseXor(
            Box::new(contract_expression_to_program_expression(left)?),
            Box::new(contract_expression_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(ProgramExpression::BitwiseNot(
            Box::new(contract_expression_to_program_expression(expression)?),
        )),
        ContractExpression::Index(base, index) => Some(ProgramExpression::Index(
            Box::new(contract_expression_to_program_expression(base)?),
            Box::new(contract_expression_to_program_expression(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::MethodCall { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn integer_result_context_does_not_create_a_binding() {
        let source = "function constant() -> Integer { 4294967296 } function choose(x: Integer) -> Integer { if x == 0 { 1 } else { 2 } } theorem check() { ensures constant() == 4294967296 by { unfold(constant()); close(); } ensures choose(0) == 1 by { unfold(choose(0)); close(); } }";
        crate::surface::verify_c_sources(source, &[]).unwrap();
        let annotated = "theorem check(__click_integer_result: Integer) { ensures ((__click_integer_result + 1) : Integer) == __click_integer_result + 1 by close(); }";
        crate::surface::verify_c_sources(annotated, &[]).unwrap();
    }

    #[test]
    fn integer_context_preserves_unbounded_arithmetic_and_rejects_machine_claims() {
        for source in [
            "theorem check() { ensures (4294967296 + 4294967296 : Integer) == 8589934592 by close(); }",
            "theorem check() { ensures (1 : Integer) == 1 by close(); }",
        ] {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        }
        assert!(
            crate::surface::verify_c_sources(
                "theorem bad() { ensures (1 : Integer) == 2 by close(); }",
                &[]
            )
            .is_err()
        );
    }

    use super::*;

    #[test]
    fn reference_dependencies_survive_same_named_lexical_binders() {
        let carrier = crate::kernel::BindingName::reference_carrier("x");
        let expression = ContractExpression::Let {
            name: "x".into(),
            click_type: None,
            value: Box::new(ContractExpression::IntegerLiteral("0".into())),
            body: Box::new(ContractExpression::ProgramExpression(
                ProgramExpression::Variable(carrier.clone()),
            )),
        };
        assert_eq!(
            contract_expression_referenced_bindings(&expression),
            BTreeSet::from([carrier]),
        );
        assert_eq!(
            contract_expression_referenced_names(&expression),
            BTreeSet::from(["x".to_owned()]),
        );
        assert!(contract_expression_referenced_lexical_names(&expression).is_empty());
        let substituted = substitute_contract_expression(
            &expression,
            &BTreeMap::from([(
                "x".to_owned(),
                ContractExpression::IntegerLiteral("7".into()),
            )]),
        )
        .unwrap();
        assert_eq!(substituted, expression);
    }

    #[test]
    fn call_substitution_replaces_exact_reference_carriers_without_lexical_capture() {
        let carrier = crate::kernel::BindingName::reference_carrier("x");
        let variable =
            |name| ContractExpression::ProgramExpression(ProgramExpression::Variable(name));
        let expression = ContractExpression::Let {
            name: "y".into(),
            click_type: None,
            value: Box::new(ContractExpression::IntegerLiteral("0".into())),
            body: Box::new(ContractExpression::Add(
                Box::new(variable(carrier.clone())),
                Box::new(ContractExpression::Binding("y".into())),
            )),
        };
        let replacements = BTreeMap::from([
            (carrier, variable("y".into())),
            (
                crate::kernel::BindingName::from("&x"),
                ContractExpression::IntegerLiteral("9".into()),
            ),
        ]);
        let actual = substitute_contract_expression(&expression, &replacements).unwrap();
        assert_eq!(
            contract_expression_referenced_bindings(&actual),
            BTreeSet::from(["y".into()])
        );
        let ContractExpression::Let { name, body, .. } = actual else {
            panic!("expected let")
        };
        assert!(matches!(name, SurfaceBinder::Generated(_)));
        let ContractExpression::Add(left, right) = *body else {
            panic!("expected sum")
        };
        assert_eq!(*left, variable("y".into()));
        assert_eq!(*right, name.reference());
    }

    #[test]
    fn logical_substitution_preserves_operators_points_and_bound_names() {
        let variable = |name: &str| {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(name.into()))
        };
        let atom = |left: ContractExpression| ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
        };
        let build = |free: ContractExpression| {
            ClickProposition::And(
                Box::new(atom(free.clone())),
                Box::new(ClickProposition::Or(
                    Box::new(ClickProposition::Not(Box::new(atom(variable("y"))))),
                    Box::new(ClickProposition::Implies(
                        Box::new(atom(free.clone())),
                        Box::new(ClickProposition::At {
                            selector: ProgramPointSelector::Mark("entry".into()),
                            proposition: Box::new(ClickProposition::And(
                                Box::new(atom(free)),
                                Box::new(ClickProposition::ForAll {
                                    click_type: ClickType::Program(InterfaceType::Int32),
                                    name: "x".into(),
                                    written_name: None,
                                    body: Box::new(atom(variable("x"))),
                                }),
                            )),
                        }),
                    )),
                )),
            )
        };
        let replacement = ContractExpression::ProgramExpression(ProgramExpression::Value(int32(7)));
        let actual = substitute_click_proposition(
            &build(variable("x")),
            &BTreeMap::from([("x".to_owned(), replacement.clone())]),
        )
        .unwrap();
        assert_eq!(actual, build(replacement));
    }

    #[test]
    fn expression_rewrite_respects_absolute_state_boundaries() {
        let x = ContractExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
        let y = ContractExpression::ProgramExpression(ProgramExpression::Variable("y".into()));
        let old = |value| ContractExpression::Old(Box::new(value));
        let at = |label: &str, value| ContractExpression::At {
            selector: ProgramPointSelector::Mark(label.into()),
            expression: Box::new(value),
        };
        let pair = |left, right| ContractExpression::Add(Box::new(left), Box::new(right));
        for historical in [old(x.clone()), at("entry", x.clone())] {
            assert_eq!(
                rewrite_contract_expression_exact(
                    &pair(x.clone(), historical.clone()),
                    &x,
                    &y,
                    true
                ),
                (pair(y.clone(), historical), true),
            );
        }
        assert_eq!(
            rewrite_contract_expression_exact(
                &old(pair(x.clone(), x.clone())),
                &old(x.clone()),
                &old(y.clone()),
                true
            ),
            (old(pair(y.clone(), y.clone())), true),
        );
        assert_eq!(
            rewrite_contract_expression_exact(
                &at("entry", pair(x.clone(), x.clone())),
                &at("entry", x.clone()),
                &at("entry", y.clone()),
                true
            ),
            (at("entry", pair(y.clone(), y.clone())), true),
        );
        let historical = at("other", pair(x.clone(), x.clone()));
        assert_eq!(
            rewrite_contract_expression_exact(&historical, &at("entry", x), &at("entry", y), true),
            (historical, false),
        );
    }

    #[test]
    fn multidimensional_array_rewrite_updates_its_lowered_base() {
        let source_base =
            ContractExpression::ProgramExpression(ProgramExpression::Variable("old".into()));
        let target_base =
            ContractExpression::ProgramExpression(ProgramExpression::Variable("new".into()));
        let expression = ContractExpression::ArrayIndex {
            base: Box::new(source_base.clone()),
            indexes: vec![
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            ],
            dimensions: vec![2, 2],
            lowered: ProgramExpression::Index(
                Box::new(ProgramExpression::Variable("old".into())),
                Box::new(ProgramExpression::Value(int32(1))),
            ),
        };
        let (rewritten, changed) =
            rewrite_contract_expression_exact(&expression, &source_base, &target_base, false);
        assert!(changed);
        let ContractExpression::ArrayIndex { lowered, .. } = rewritten else {
            panic!("array rewrite must retain its presentation node");
        };
        assert_eq!(
            lowered,
            ProgramExpression::Index(
                Box::new(ProgramExpression::Variable("new".into())),
                Box::new(ProgramExpression::Value(int32(1))),
            )
        );
    }

    #[test]
    fn multidimensional_array_rewrite_fails_closed_for_non_c_bases() {
        let source_base =
            ContractExpression::ProgramExpression(ProgramExpression::Variable("old".into()));
        let expression = ContractExpression::ArrayIndex {
            base: Box::new(source_base.clone()),
            indexes: vec![
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            ],
            dimensions: vec![2, 2],
            lowered: ProgramExpression::Index(
                Box::new(ProgramExpression::Variable("old".into())),
                Box::new(ProgramExpression::Value(int32(1))),
            ),
        };
        let target = ContractExpression::Call {
            name: "not_a_c_fragment".into(),
            arguments: vec![],
        };
        let (rewritten, changed) =
            rewrite_contract_expression_exact(&expression, &source_base, &target, false);
        assert!(!changed);
        assert_eq!(rewritten, expression);
    }
}
