use super::*;
use std::borrow::Cow;

pub(in crate::surface) fn unfold_structural_invariant_proposition(
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

pub(in crate::surface) fn unfold_click_predicates_in_proposition_with_active(
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
        ClickProposition::ForAll {
            click_type: c_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::ForAll {
            click_type: c_type.clone(),
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::Exists {
            click_type: c_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::Exists {
            click_type: c_type.clone(),
            name: name.clone(),
            written_name: written_name.clone(),
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
            written_item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            written_item: written_item.clone(),
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
            written_item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            written_item: written_item.clone(),
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
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
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
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(substitute_click_proposition_in(proposition, substitutions)?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(substitute_click_proposition_in(left, substitutions)?),
            Box::new(substitute_click_proposition_in(right, substitutions)?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(substitute_click_proposition_in(left, substitutions)?),
            Box::new(substitute_click_proposition_in(right, substitutions)?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            substitute_click_proposition_in(body, substitutions)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(substitute_click_proposition_in(left, substitutions)?),
            Box::new(substitute_click_proposition_in(right, substitutions)?),
        )),
        _ => unreachable!("non-logical proposition dispatched to logical substitution"),
    }
}

fn substitute_click_proposition_nonlogical(
    proposition: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ClickProposition, String> {
    match proposition {
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
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: substitute_contract_segment(segment, substitutions)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: substitute_contract_expression_in(expression, substitutions)?,
        }),
        ClickProposition::ForAll {
            click_type: c_type,
            name,
            written_name,
            body,
        } => {
            let scoped = substitutions.without_binding(name);
            let original_name = name.clone();
            let (name, body) = prepare_click_proposition_binding_body(name, body, &scoped)?;
            Ok(ClickProposition::ForAll {
                click_type: c_type.clone(),
                written_name: written_name
                    .clone()
                    .or_else(|| (name != original_name).then_some(original_name)),
                name,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists {
            click_type: c_type,
            name,
            written_name,
            body,
        } => {
            let scoped = substitutions.without_binding(name);
            let original_name = name.clone();
            let (name, body) = prepare_click_proposition_binding_body(name, body, &scoped)?;
            Ok(ClickProposition::Exists {
                click_type: c_type.clone(),
                written_name: written_name
                    .clone()
                    .or_else(|| (name != original_name).then_some(original_name)),
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
            let written_item = written_item
                .clone()
                .or_else(|| (item != original_item).then_some(original_item));
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
            let written_item = written_item
                .clone()
                .or_else(|| (item != original_item).then_some(original_item));
            Ok(ClickProposition::RangeAny {
                start: substitute_contract_expression_in(start, substitutions)?,
                end: substitute_contract_expression_in(end, substitutions)?,
                item,
                written_item,
                body: Box::new(body),
            })
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
    binder: &str,
    body: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<(String, ClickProposition), String> {
    if !substitutions_reference_name(substitutions, binder) {
        return Ok((
            binder.to_string(),
            substitute_click_proposition_in(body, substitutions)?,
        ));
    }

    let fresh = fresh_click_binding_name_for_proposition(binder, body, substitutions);
    let renaming = BTreeMap::from([(
        binder.to_string(),
        ContractExpression::CBinding(fresh.clone()),
    )]);
    let renamed = substitute_click_proposition(body, &renaming)?;
    Ok((
        fresh,
        substitute_click_proposition_in(&renamed, substitutions)?,
    ))
}

fn prepare_contract_expression_binding_body(
    binder: &str,
    body: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<(String, ContractExpression), String> {
    if !substitutions_reference_name(substitutions, binder) {
        return Ok((
            binder.to_string(),
            substitute_contract_expression_in(body, substitutions)?,
        ));
    }

    let fresh = fresh_click_binding_name_for_expression(binder, body, substitutions);
    let renaming = BTreeMap::from([(
        binder.to_string(),
        ContractExpression::CBinding(fresh.clone()),
    )]);
    let renamed = substitute_contract_expression(body, &renaming)?;
    Ok((
        fresh,
        substitute_contract_expression_in(&renamed, substitutions)?,
    ))
}

fn prepare_contract_range_fold_body(
    accumulator: &str,
    item: &str,
    body: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<(String, String, ContractExpression), String> {
    let mut used = substitutions
        .replaced_names()
        .cloned()
        .collect::<BTreeSet<_>>();
    collect_contract_expression_referenced_names(body, &mut used);
    collect_contract_expression_binding_names(body, &mut used);
    for expression in substitutions.substituted_expressions() {
        collect_contract_expression_referenced_names(expression, &mut used);
        collect_contract_expression_binding_names(expression, &mut used);
    }
    used.insert(accumulator.to_string());
    used.insert(item.to_string());

    let original_accumulator = accumulator.to_string();
    let original_item = item.to_string();
    let mut accumulator = original_accumulator.clone();
    let mut item = original_item.clone();
    let mut renamed_body = body.clone();

    if substitutions_reference_name(substitutions, &original_accumulator) {
        let fresh = fresh_click_binding_name(used.clone());
        used.insert(fresh.clone());
        let renaming = BTreeMap::from([(
            original_accumulator.clone(),
            ContractExpression::CBinding(fresh.clone()),
        )]);
        renamed_body = substitute_contract_expression(&renamed_body, &renaming)?;
        accumulator = fresh;
    }
    if original_item != original_accumulator
        && substitutions_reference_name(substitutions, &original_item)
    {
        let fresh = fresh_click_binding_name(used);
        let renaming = BTreeMap::from([(
            original_item.clone(),
            ContractExpression::CBinding(fresh.clone()),
        )]);
        renamed_body = substitute_contract_expression(&renamed_body, &renaming)?;
        item = fresh;
    } else if original_item == original_accumulator {
        item = accumulator.clone();
    }

    Ok((
        accumulator,
        item,
        substitute_contract_expression_in(&renamed_body, substitutions)?,
    ))
}

/// A `match` arm binds its payload names inside its body, so a replacement that
/// still applies there must not itself mention one of them: substituting it
/// under the binder would silently rebind the caller's name to this arm's
/// payload and make the instantiated body say something other than the
/// definition. Quantifier and range-fold binders avoid that by renaming
/// themselves out of the way first; a match arm now follows the same rule, and
/// a binding a live replacement mentions is renamed before the substitution
/// reaches the body. Renaming a binding also un-shadows a replacement keyed by
/// its old name, so the surviving arm bindings decide the final substitutions,
/// and anything a rename could not separate is refused rather than captured.
fn prepare_contract_match_arm(
    arm: &AlgebraicMatchArm,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<AlgebraicMatchArm, String> {
    let mut shadowed = substitutions.clone();
    for binding in &arm.bindings {
        shadowed = shadowed.without_binding(binding);
    }

    let mut bindings = arm.bindings.clone();
    let mut body = arm.body.clone();
    for binding in &mut bindings {
        if !match_arm_replacements_reference_name(&body, &shadowed, binding) {
            continue;
        }
        let fresh = fresh_click_binding_name_for_expression(binding, &body, &shadowed);
        let renaming =
            BTreeMap::from([(binding.clone(), ContractExpression::Binding(fresh.clone()))]);
        body = substitute_contract_expression(&body, &renaming)?;
        *binding = fresh;
    }

    let mut arm_substitutions = substitutions.clone();
    for binding in &bindings {
        arm_substitutions = arm_substitutions.without_binding(binding);
    }
    let renamed = AlgebraicMatchArm {
        type_name: arm.type_name.clone(),
        variant: arm.variant.clone(),
        bindings,
        body,
    };
    refuse_captured_match_arm_substitution(&renamed, &arm_substitutions)?;
    Ok(AlgebraicMatchArm {
        body: substitute_contract_expression_in(&renamed.body, &arm_substitutions)?,
        ..renamed
    })
}

/// Whether a replacement that actually reaches `body` mentions `name`. Only a
/// replacement keyed by a name the arm body still refers to can be substituted
/// under this arm's binders, so a replacement that lands elsewhere — the match
/// scrutinee, say, which is outside them — is not a reason to rename anything.
/// Renaming a binding no substitution reaches would change the instantiated
/// body for nothing and lose the spelling a later exact check compares against.
fn match_arm_replacements_reference_name(
    body: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
    name: &str,
) -> bool {
    let mut body_names = BTreeSet::new();
    collect_contract_expression_referenced_names(body, &mut body_names);
    substitutions
        .values
        .iter()
        .filter(|(key, _)| body_names.contains(*key))
        .any(|(_, replacement)| {
            let mut names = BTreeSet::new();
            collect_contract_expression_referenced_names(replacement, &mut names);
            names.contains(name)
        })
}

/// The residual check for [`prepare_contract_match_arm`]: after renaming, no
/// replacement that still reaches this arm's body may mention a name the arm
/// binds. The scan is bounded by the arm's own free names and the replacements
/// that actually reach it.
fn refuse_captured_match_arm_substitution(
    arm: &AlgebraicMatchArm,
    arm_substitutions: &ContractSubstitutions<'_>,
) -> Result<(), String> {
    if arm.bindings.is_empty() {
        return Ok(());
    }
    let mut body_names = BTreeSet::new();
    collect_contract_expression_referenced_names(&arm.body, &mut body_names);
    for (name, replacement) in arm_substitutions.values.iter() {
        if !body_names.contains(name) {
            continue;
        }
        let mut replacement_names = BTreeSet::new();
        collect_contract_expression_referenced_names(replacement, &mut replacement_names);
        for binding in &arm.bindings {
            if replacement_names.contains(binding) {
                return Err(format!(
                    "substituting `{name}` into the `{}::{}` arm would capture `{binding}`, \
                     which that arm binds; rename the arm binding or the substituted name",
                    arm.type_name, arm.variant
                ));
            }
        }
    }
    Ok(())
}

fn substitutions_reference_name(substitutions: &ContractSubstitutions<'_>, name: &str) -> bool {
    substitutions.substituted_expressions().any(|expression| {
        let mut names = BTreeSet::new();
        collect_contract_expression_referenced_names(expression, &mut names);
        names.contains(name)
    })
}

fn fresh_click_binding_name_for_proposition(
    binder: &str,
    body: &ClickProposition,
    substitutions: &ContractSubstitutions<'_>,
) -> String {
    let mut used = substitutions
        .replaced_names()
        .cloned()
        .collect::<BTreeSet<_>>();
    collect_click_proposition_referenced_names(body, &mut used);
    collect_click_proposition_binding_names(body, &mut used);
    for expression in substitutions.substituted_expressions() {
        collect_contract_expression_referenced_names(expression, &mut used);
        collect_contract_expression_binding_names(expression, &mut used);
    }
    used.insert(binder.to_string());
    fresh_click_binding_name(used)
}

fn fresh_click_binding_name_for_expression(
    binder: &str,
    body: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> String {
    let mut used = substitutions
        .replaced_names()
        .cloned()
        .collect::<BTreeSet<_>>();
    collect_contract_expression_referenced_names(body, &mut used);
    collect_contract_expression_binding_names(body, &mut used);
    for expression in substitutions.substituted_expressions() {
        collect_contract_expression_referenced_names(expression, &mut used);
        collect_contract_expression_binding_names(expression, &mut used);
    }
    used.insert(binder.to_string());
    fresh_click_binding_name(used)
}

fn fresh_click_binding_name(used: BTreeSet<String>) -> String {
    let mut index = 0usize;
    loop {
        let candidate = format!("__click_binder_{index}");
        if !used.contains(&candidate) {
            return candidate;
        }
        index += 1;
    }
}

fn collect_click_proposition_binding_names(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_contract_expression_binding_names(left, names);
            collect_contract_expression_binding_names(right, names);
        }
        ClickProposition::FloatClassification { expression, .. } => {
            collect_contract_expression_binding_names(expression, names);
        }
        ClickProposition::Separate { left, right } => {
            collect_resource_subject_binding_names(left, names);
            collect_resource_subject_binding_names(right, names);
        }
        ClickProposition::Contains { parent, child } => {
            collect_resource_subject_binding_names(parent, names);
            collect_resource_subject_binding_names(child, names);
        }
        ClickProposition::Loadable { segment } => {
            collect_contract_segment_binding_names(segment, names);
        }
        ClickProposition::Defined { expression } => {
            collect_contract_expression_binding_names(expression, names);
        }
        ClickProposition::At { proposition, .. } | ClickProposition::Not(proposition) => {
            collect_click_proposition_binding_names(proposition, names);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_proposition_binding_names(left, names);
            collect_click_proposition_binding_names(right, names);
        }
        ClickProposition::ForAll { name, body, .. }
        | ClickProposition::Exists { name, body, .. } => {
            names.insert(name.clone());
            collect_click_proposition_binding_names(body, names);
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
            collect_contract_expression_binding_names(start, names);
            collect_contract_expression_binding_names(end, names);
            names.insert(item.clone());
            collect_click_proposition_binding_names(body, names);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_binding_names(argument, names);
            }
        }
    }
}

fn collect_contract_expression_binding_names(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::IntegerLiteral(_) => {}
        ContractExpression::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_binding_names(argument, names);
            }
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_contract_expression_binding_names(scrutinee, names);
            for arm in arms {
                names.extend(arm.bindings.iter().cloned());
                collect_contract_expression_binding_names(&arm.body, names);
            }
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                collect_contract_expression_binding_names(element, names);
            }
        }
        ContractExpression::SequenceConcat(left, right) => {
            collect_contract_expression_binding_names(left, names);
            collect_contract_expression_binding_names(right, names);
        }
        ContractExpression::QualifiedC { .. }
        | ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => {}
        ContractExpression::ArrayIndex { .. } => {}
        ContractExpression::Field { base, .. }
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::Negate(base)
        | ContractExpression::BitwiseNot(base) => {
            collect_contract_expression_binding_names(base, names);
        }
        ContractExpression::ResourceCount(resource) => {
            collect_resource_clause_binding_names(resource, names);
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
            collect_contract_expression_binding_names(left, names);
            collect_contract_expression_binding_names(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_proposition_binding_names(condition, names);
            collect_contract_expression_binding_names(then_branch, names);
            collect_contract_expression_binding_names(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_contract_expression_binding_names(start, names);
            collect_contract_expression_binding_names(end, names);
            collect_contract_expression_binding_names(initial, names);
            names.insert(accumulator.clone());
            names.insert(item.clone());
            collect_contract_expression_binding_names(body, names);
        }
        ContractExpression::Let {
            name, value, body, ..
        } => {
            names.insert(name.clone());
            collect_contract_expression_binding_names(value, names);
            collect_contract_expression_binding_names(body, names);
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_binding_names(argument, names);
            }
        }
    }
}

fn collect_resource_subject_binding_names(
    resource: &ResourceSubject,
    names: &mut BTreeSet<String>,
) {
    match resource {
        ResourceSubject::Memory(segment) => collect_contract_segment_binding_names(segment, names),
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_binding_names(argument, names);
            }
        }
    }
}

fn collect_resource_clause_binding_names(resource: &ResourceClause, names: &mut BTreeSet<String>) {
    match resource {
        ResourceClause::Named { binding, resource } => {
            names.insert(binding.name.clone());
            collect_resource_clause_binding_names(resource, names);
        }
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            collect_contract_segment_binding_names(segment, names)
        }
        ResourceClause::MemoryAggregate { segments, .. } => {
            for segment in segments {
                collect_contract_segment_binding_names(segment, names);
            }
        }
        ResourceClause::Quantified { quantity, resource } => {
            collect_contract_expression_binding_names(quantity, names);
            collect_resource_clause_binding_names(resource, names);
        }
        ResourceClause::Declared { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_binding_names(argument, names);
            }
        }
    }
}

fn collect_contract_segment_binding_names(segment: &ContractSegment, names: &mut BTreeSet<String>) {
    if let ContractSegmentSurface::Range { base, start, end } = &segment.surface {
        collect_contract_expression_binding_names(base, names);
        collect_contract_expression_binding_names(start, names);
        collect_contract_expression_binding_names(end, names);
    }
}

/// Applies one exact Surface equality as an untrusted form transform.
///
/// The checked kernel rewrite remains authoritative. Callers must lower the
/// returned candidate and compare it with the kernel successor before
/// retaining it as a goal view. This helper only preserves source structure
/// for later certificate search; it never establishes a proposition.
pub(in crate::surface) fn rewrite_click_proposition_by_surface_equality(
    proposition: &ClickProposition,
    equality: &ClickProposition,
) -> Option<ClickProposition> {
    let (left, right) = surface_equality_expression_sides(equality)?;
    let (rewritten, changed) = rewrite_click_proposition_expression(proposition, &left, &right);
    changed.then_some(rewritten)
}

/// Reduce the constructor arms exposed by an explicit surface rewrite.
///
/// The checked kernel lowering performs constructor iota while it rebuilds a
/// goal.  Keep the retained source view at the same reduction frontier so a
/// later explicit unfold can see calls that were inside selected arms.  This
/// is only a presentation transform: callers still lower the returned
/// proposition and use that checked kernel result as the authority.
pub(in crate::surface) fn reduce_constructor_iota_in_proposition(
    proposition: &ClickProposition,
) -> Result<ClickProposition, String> {
    let expression = |value: &ContractExpression| reduce_constructor_iota_in_expression(value);
    let proposition = match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ClickProposition::Comparison {
            left: expression(left)?,
            operator: *operator,
            right: expression(right)?,
        },
        ClickProposition::FloatClassification {
            expression: value,
            classification,
        } => ClickProposition::FloatClassification {
            expression: expression(value)?,
            classification: *classification,
        },
        ClickProposition::Defined { expression: value } => ClickProposition::Defined {
            expression: expression(value)?,
        },
        ClickProposition::At {
            selector,
            proposition,
        } => ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(reduce_constructor_iota_in_proposition(proposition)?),
        },
        ClickProposition::And(left, right) => ClickProposition::And(
            Box::new(reduce_constructor_iota_in_proposition(left)?),
            Box::new(reduce_constructor_iota_in_proposition(right)?),
        ),
        ClickProposition::Or(left, right) => ClickProposition::Or(
            Box::new(reduce_constructor_iota_in_proposition(left)?),
            Box::new(reduce_constructor_iota_in_proposition(right)?),
        ),
        ClickProposition::Not(body) => {
            ClickProposition::Not(Box::new(reduce_constructor_iota_in_proposition(body)?))
        }
        ClickProposition::Implies(left, right) => ClickProposition::Implies(
            Box::new(reduce_constructor_iota_in_proposition(left)?),
            Box::new(reduce_constructor_iota_in_proposition(right)?),
        ),
        ClickProposition::ForAll {
            click_type,
            name,
            written_name,
            body,
        } => ClickProposition::ForAll {
            click_type: click_type.clone(),
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(reduce_constructor_iota_in_proposition(body)?),
        },
        ClickProposition::Exists {
            click_type,
            name,
            written_name,
            body,
        } => ClickProposition::Exists {
            click_type: click_type.clone(),
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(reduce_constructor_iota_in_proposition(body)?),
        },
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => ClickProposition::RangeAll {
            start: expression(start)?,
            end: expression(end)?,
            item: item.clone(),
            written_item: written_item.clone(),
            body: Box::new(reduce_constructor_iota_in_proposition(body)?),
        },
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => ClickProposition::RangeAny {
            start: expression(start)?,
            end: expression(end)?,
            item: item.clone(),
            written_item: written_item.clone(),
            body: Box::new(reduce_constructor_iota_in_proposition(body)?),
        },
        ClickProposition::PredicateCall { name, arguments } => ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(expression)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ClickProposition::Separate { left, right } => ClickProposition::Separate {
            left: left.clone(),
            right: right.clone(),
        },
        ClickProposition::Contains { parent, child } => ClickProposition::Contains {
            parent: parent.clone(),
            child: child.clone(),
        },
        ClickProposition::Loadable { segment } => ClickProposition::Loadable {
            segment: segment.clone(),
        },
    };
    Ok(proposition)
}

fn reduce_constructor_iota_in_expression(
    expression: &ContractExpression,
) -> Result<ContractExpression, String> {
    let recurse = |value: &ContractExpression| reduce_constructor_iota_in_expression(value);
    match expression {
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let scrutinee = recurse(scrutinee)?;
            if let ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            } = &scrutinee
                && let Some(arm) = arms.iter().find(|arm| {
                    arm.type_name == algebraic_type.name
                        && arm.variant == *variant
                        && arm.bindings.len() == arguments.len()
                })
            {
                let substitutions = arm
                    .bindings
                    .iter()
                    .cloned()
                    .zip(arguments.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                let selected = substitute_contract_expression(&arm.body, &substitutions)?;
                return recurse(&selected);
            }
            Ok(ContractExpression::AlgebraicMatch {
                scrutinee: Box::new(scrutinee),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(AlgebraicMatchArm {
                            type_name: arm.type_name.clone(),
                            variant: arm.variant.clone(),
                            bindings: arm.bindings.clone(),
                            body: recurse(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            })
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => Ok(ContractExpression::AlgebraicConstructor {
            algebraic_type: algebraic_type.clone(),
            variant: variant.clone(),
            arguments: arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ContractExpression::SequenceLiteral(elements) => Ok(ContractExpression::SequenceLiteral(
            elements
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        )),
        ContractExpression::SequenceConcat(left, right) => Ok(ContractExpression::SequenceConcat(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::Old(inner) => Ok(ContractExpression::Old(Box::new(recurse(inner)?))),
        ContractExpression::At {
            selector,
            expression,
        } => Ok(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(recurse(expression)?),
        }),
        ContractExpression::Negate(inner) => {
            Ok(ContractExpression::Negate(Box::new(recurse(inner)?)))
        }
        ContractExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::BitwiseNot(inner) => {
            Ok(ContractExpression::BitwiseNot(Box::new(recurse(inner)?)))
        }
        ContractExpression::Index(left, right) => Ok(ContractExpression::Index(
            Box::new(recurse(left)?),
            Box::new(recurse(right)?),
        )),
        ContractExpression::ArrayIndex {
            base,
            indexes,
            lowered,
        } => Ok(ContractExpression::ArrayIndex {
            base: Box::new(recurse(base)?),
            indexes: indexes.clone(),
            lowered: lowered.clone(),
        }),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => Ok(ContractExpression::If {
            condition: Box::new(reduce_constructor_iota_in_proposition(condition)?),
            then_branch: Box::new(recurse(then_branch)?),
            else_branch: Box::new(recurse(else_branch)?),
        }),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Ok(ContractExpression::RangeFold {
            start: Box::new(recurse(start)?),
            end: Box::new(recurse(end)?),
            initial: Box::new(recurse(initial)?),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(recurse(body)?),
        }),
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => Ok(ContractExpression::Let {
            name: name.clone(),
            click_type: click_type.clone(),
            value: Box::new(recurse(value)?),
            body: Box::new(recurse(body)?),
        }),
        ContractExpression::Call { name, arguments } => Ok(ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ContractExpression::Field {
            base,
            field,
            lowered,
        } => Ok(ContractExpression::Field {
            base: Box::new(recurse(base)?),
            field: field.clone(),
            lowered: lowered.clone(),
        }),
        ContractExpression::IntegerLiteral(_)
        | ContractExpression::QualifiedC { .. }
        | ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard => Ok(expression.clone()),
    }
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
                expression_at_snapshot(selector, left),
                expression_at_snapshot(selector, right),
            ))
        }
        _ => None,
    }
}

fn expression_at_snapshot(
    selector: &SnapshotSelector,
    expression: ContractExpression,
) -> ContractExpression {
    match expression {
        // `old` and an explicitly selected `at` are already absolute
        // snapshots; an enclosing proposition snapshot does not rebase them.
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
) -> (ClickProposition, bool) {
    let expression =
        |value: &ContractExpression| rewrite_contract_expression_exact(value, source, target);
    let rewrite_proposition =
        |value: &ClickProposition| rewrite_click_proposition_expression(value, source, target);
    match proposition {
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
            let (left, left_changed) = rewrite_resource_subject_exact(left, source, target);
            let (right, right_changed) = rewrite_resource_subject_exact(right, source, target);
            (
                ClickProposition::Separate { left, right },
                left_changed || right_changed,
            )
        }
        ClickProposition::Contains { parent, child } => {
            let (parent, parent_changed) = rewrite_resource_subject_exact(parent, source, target);
            let (child, child_changed) = rewrite_resource_subject_exact(child, source, target);
            (
                ClickProposition::Contains { parent, child },
                parent_changed || child_changed,
            )
        }
        ClickProposition::Loadable { segment } => (
            ClickProposition::Loadable {
                segment: segment.clone(),
            },
            false,
        ),
        ClickProposition::Defined { expression: value } => {
            let (value, changed) = expression(value);
            (ClickProposition::Defined { expression: value }, changed)
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
            click_type: c_type,
            name,
            body,
            ..
        }
        | ClickProposition::Exists {
            click_type: c_type,
            name,
            body,
            ..
        } => {
            let (body, changed) = rewrite_proposition(body);
            let rewritten = match proposition {
                ClickProposition::ForAll { .. } => ClickProposition::ForAll {
                    click_type: c_type.clone(),
                    name: name.clone(),
                    written_name: proposition.written_quantifier_name().map(str::to_string),
                    body: Box::new(body),
                },
                ClickProposition::Exists { .. } => ClickProposition::Exists {
                    click_type: c_type.clone(),
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
) -> (ResourceSubject, bool) {
    match subject {
        ResourceSubject::Memory(segment) => (ResourceSubject::Memory(segment.clone()), false),
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
                    let (argument, argument_changed) =
                        rewrite_contract_expression_exact(argument, source, target);
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
) -> (ResourceClause, bool) {
    match resource {
        ResourceClause::Named { binding, resource } => {
            let (resource, changed) = rewrite_resource_clause_exact(resource, source, target);
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
        ResourceClause::MemoryAggregate { access, segments } => (
            ResourceClause::MemoryAggregate {
                access: *access,
                segments: segments.clone(),
            },
            false,
        ),
        ResourceClause::Quantified { quantity, resource } => {
            let (quantity, quantity_changed) =
                rewrite_contract_expression_exact(quantity, source, target);
            let (resource, resource_changed) =
                rewrite_resource_clause_exact(resource, source, target);
            (
                ResourceClause::Quantified {
                    quantity,
                    resource: Box::new(resource),
                },
                quantity_changed || resource_changed,
            )
        }
        ResourceClause::Declared {
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
                    let (argument, argument_changed) =
                        rewrite_contract_expression_exact(argument, source, target);
                    changed |= argument_changed;
                    argument
                })
                .collect();
            (
                ResourceClause::Declared {
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
) -> (ContractExpression, bool) {
    if expression == source {
        return (target.clone(), true);
    }
    let unary =
        |value: &ContractExpression| rewrite_contract_expression_exact(value, source, target);
    let binary = |left: &ContractExpression, right: &ContractExpression| {
        let (left, left_changed) = unary(left);
        let (right, right_changed) = unary(right);
        (left, right, left_changed || right_changed)
    };
    match expression {
        ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::IntegerLiteral(_) => (expression.clone(), false),
        ContractExpression::Negate(inner) => {
            let (inner, changed) = unary(inner);
            (ContractExpression::Negate(Box::new(inner)), changed)
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
        ContractExpression::QualifiedC { .. }
        | ContractExpression::CFragment(_)
        | ContractExpression::Field { .. }
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceWildcard => (expression.clone(), false),
        ContractExpression::ArrayIndex {
            base,
            indexes,
            lowered,
        } => {
            let (base, changed) = unary(base);
            if !changed {
                return (expression.clone(), false);
            }
            let Some(lowered_base) = contract_expression_as_c_fragment(&base) else {
                return (expression.clone(), false);
            };
            let CExpression::Index(_, offset) = lowered else {
                return (expression.clone(), false);
            };
            (
                ContractExpression::ArrayIndex {
                    base: Box::new(base),
                    indexes: indexes.clone(),
                    lowered: CExpression::Index(Box::new(lowered_base), offset.clone()),
                },
                changed,
            )
        }
        ContractExpression::ResourceCount(resource) => {
            let (resource, changed) = rewrite_resource_clause_exact(resource, source, target);
            (
                ContractExpression::ResourceCount(Box::new(resource)),
                changed,
            )
        }
        ContractExpression::Old(value) => {
            let (value, changed) = unary(value);
            (ContractExpression::Old(Box::new(value)), changed)
        }
        ContractExpression::At {
            selector,
            expression,
        } => {
            let (expression, changed) = unary(expression);
            (
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(expression),
                },
                changed,
            )
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
                ContractExpression::ShiftRight(_, _) => {
                    ContractExpression::ShiftRight(Box::new(left), Box::new(right))
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
                rewrite_click_proposition_expression(condition, source, target);
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
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment_in(&segment.base, substitutions)?,
        start: substitute_c_fragment_in(&segment.start, substitutions)?,
        end: substitute_c_fragment_in(&segment.end, substitutions)?,
        surface,
    })
}

fn substitute_resource_subject(
    resource: &ResourceSubject,
    substitutions: &ContractSubstitutions<'_>,
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

pub(in crate::surface) fn apply_contract_lets_to_ensure_clause(
    clause: EnsureClause,
    bindings: &[ContractLetBinding],
) -> Result<EnsureClause, String> {
    let EnsureClause {
        name,
        ensure,
        proof,
        borrowed,
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
        borrowed,
    })
}

pub(in crate::surface) fn apply_contract_lets_to_resource_clause(
    resource: ResourceClause,
    bindings: &[ContractLetBinding],
) -> Result<ResourceClause, String> {
    match resource {
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
    let mut capture_names = BTreeSet::new();
    for binding in bindings {
        if let Some(value) = binding.value() {
            collect_contract_expression_referenced_names(value, &mut capture_names);
        }
    }
    apply_contract_let_expressions_inner(proposition, bindings, &capture_names)
}

fn apply_contract_let_expressions_inner(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
    capture_names: &BTreeSet<String>,
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
            click_type: c_type,
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
                c_type == ClickType::Integer,
            )?;
            let written_name =
                written_name.or_else(|| (name != original_name).then_some(original_name));
            Ok(ClickProposition::ForAll {
                click_type: c_type,
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
            click_type: c_type,
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
                c_type == ClickType::Integer,
            )?;
            let written_name =
                written_name.or_else(|| (name != original_name).then_some(original_name));
            Ok(ClickProposition::Exists {
                click_type: c_type,
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
            let written_item =
                written_item.or_else(|| (item != original_item).then_some(original_item));
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
            let written_item =
                written_item.or_else(|| (item != original_item).then_some(original_item));
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
    binder: &str,
    body: ClickProposition,
    bindings: &[ContractLetBinding],
    capture_names: &BTreeSet<String>,
    integer: bool,
) -> Result<(String, ClickProposition), String> {
    if !capture_names.contains(binder) {
        return Ok((binder.to_string(), body));
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
    let substitutions = ContractSubstitutions::new(&values);
    if !substitutions_reference_name(&substitutions, binder) {
        return Ok((binder.to_string(), body));
    }

    let fresh = fresh_click_binding_name_for_proposition(binder, &body, &substitutions);
    let replacement = if integer {
        ContractExpression::Binding(fresh.clone())
    } else {
        ContractExpression::CBinding(fresh.clone())
    };
    let renaming = BTreeMap::from([(binder.to_string(), replacement)]);
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
        let ClickType::C(c_type) = click_type else {
            return Err(format!(
                "`let ... where` `{}` requires a C type annotation",
                binding.name
            ));
        };
        proposition = ClickProposition::Exists {
            click_type: ClickType::C(*c_type),
            name: binding.name.clone(),
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
    let referenced_names = contract_expression_referenced_names(&expression);
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
        for dependency in contract_expression_referenced_names(value) {
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
            name: binding.name.clone(),
            click_type: binding.click_type.clone(),
            value: Box::new(value.clone()),
            body: Box::new(expression),
        };
    }
    expression
}

pub(in crate::surface) fn contract_lets_without_name(
    bindings: &[ContractLetBinding],
    name: &str,
) -> Vec<ContractLetBinding> {
    bindings
        .iter()
        .filter(|binding| binding.name != name)
        .cloned()
        .collect()
}

pub(in crate::surface) fn contract_expression_referenced_names(
    expression: &ContractExpression,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_contract_expression_referenced_names(expression, &mut names);
    names
}

pub(in crate::surface) fn collect_contract_expression_referenced_names(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::ResourceField(_) | ContractExpression::IntegerLiteral(_) => {}
        ContractExpression::Negate(inner) => {
            collect_contract_expression_referenced_names(inner, names);
        }
        ContractExpression::AlgebraicVariable { name, .. } => {
            names.insert(name.clone());
        }
        ContractExpression::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_contract_expression_referenced_names(scrutinee, names);
            for arm in arms {
                let mut arm_names = BTreeSet::new();
                collect_contract_expression_referenced_names(&arm.body, &mut arm_names);
                for binding in &arm.bindings {
                    arm_names.remove(binding);
                }
                names.extend(arm_names);
            }
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                collect_contract_expression_referenced_names(element, names);
            }
        }
        ContractExpression::SequenceConcat(left, right) => {
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::CFragment(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        ContractExpression::Field { base, .. } => {
            collect_contract_expression_referenced_names(base, names);
        }
        ContractExpression::ArrayIndex { base, indexes, .. } => {
            collect_contract_expression_referenced_names(base, names);
            for index in indexes {
                collect_c_expression_referenced_names(index, names);
            }
        }
        ContractExpression::Binding(name) | ContractExpression::CBinding(name) => {
            names.insert(name.clone());
        }
        ContractExpression::ResourceCount(resource) => {
            if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                for argument in arguments {
                    collect_contract_expression_referenced_names(argument, names);
                }
            }
        }
        ContractExpression::ResourceWildcard => {}
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
            let previous = names.remove(name);
            collect_contract_expression_referenced_names(body, names);
            names.remove(name);
            if previous {
                names.insert(name.clone());
            }
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(in crate::surface) fn collect_click_proposition_referenced_names(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ClickProposition::FloatClassification { expression, .. } => {
            collect_contract_expression_referenced_names(expression, names);
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
            let previous = names.remove(name);
            collect_click_proposition_referenced_names(body, names);
            names.remove(name);
            if previous {
                names.insert(name.clone());
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
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            let previous = names.remove(item);
            collect_click_proposition_referenced_names(body, names);
            names.remove(item);
            if previous {
                names.insert(item.clone());
            }
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
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
            (binding.click_type != Some(ClickType::Integer))
                .then(|| {
                    binding
                        .value()
                        .map(|value| (binding.name.clone(), value.clone()))
                })
                .flatten()
        })
        .collect()
}

/// The new surface name an execution theorem's `as` map gives one resource
/// instance of the target contract. The identity is the semantic key: an
/// unrelated instance that happens to share the declared spelling keeps its
/// own name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct InstanceRename {
    pub(in crate::surface) name: String,
    pub(in crate::surface) identity: Variable,
}

/// Nothing is renamed. A values-only pass borrows this instead of allocating
/// an empty map.
static NO_INSTANCE_RENAMES: BTreeMap<String, InstanceRename> = BTreeMap::new();

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
    values: Cow<'a, BTreeMap<String, ContractExpression>>,
    instance_renames: Cow<'a, BTreeMap<String, InstanceRename>>,
}

impl<'a> ContractSubstitutions<'a> {
    /// Value substitutions with no instance renamed.
    pub(in crate::surface) fn new(values: &'a BTreeMap<String, ContractExpression>) -> Self {
        Self {
            values: Cow::Borrowed(values),
            instance_renames: Cow::Borrowed(&NO_INSTANCE_RENAMES),
        }
    }

    /// Value substitutions together with the renames an execution theorem's
    /// `as` map states for the target contract's proof parameters.
    pub(in crate::surface) fn with_instance_renames(
        values: &'a BTreeMap<String, ContractExpression>,
        instance_renames: &'a BTreeMap<String, InstanceRename>,
    ) -> Self {
        Self {
            values: Cow::Borrowed(values),
            instance_renames: Cow::Borrowed(instance_renames),
        }
    }

    fn value(&self, name: &str) -> Option<&ContractExpression> {
        self.values.get(name)
    }

    /// The expressions this pass substitutes in. A rename carries no
    /// expression, so it contributes nothing here.
    fn substituted_expressions(&self) -> impl Iterator<Item = &ContractExpression> {
        self.values.values()
    }

    /// The new surface name for the instance `owner`, when a rename was
    /// recorded for exactly that instance identity.
    pub(in crate::surface) fn instance_rename(
        &self,
        owner: &str,
        identity: Variable,
    ) -> Option<String> {
        self.instance_renames
            .get(owner)
            .filter(|rename| rename.identity == identity)
            .map(|rename| rename.name.clone())
    }

    /// Every name this pass replaces, values and renames alike. A fresh
    /// binding name has to avoid all of them.
    fn replaced_names(&self) -> impl Iterator<Item = &String> {
        self.values.keys().chain(self.instance_renames.keys())
    }

    /// The same pass under a binder that shadows `name`: inside that body the
    /// name is a binding, not something this pass replaces.
    fn without_binding(&self, name: &str) -> ContractSubstitutions<'a> {
        let mut values = self.values.as_ref().clone();
        values.remove(name);
        let mut instance_renames = self.instance_renames.clone();
        if instance_renames.contains_key(name) {
            instance_renames.to_mut().remove(name);
        }
        ContractSubstitutions {
            values: Cow::Owned(values),
            instance_renames,
        }
    }
}

impl<'a> From<&'a BTreeMap<String, ContractExpression>> for ContractSubstitutions<'a> {
    fn from(values: &'a BTreeMap<String, ContractExpression>) -> Self {
        ContractSubstitutions::new(values)
    }
}

pub(in crate::surface) fn substitute_contract_expression<'a>(
    expression: &ContractExpression,
    substitutions: impl Into<ContractSubstitutions<'a>>,
) -> Result<ContractExpression, String> {
    substitute_contract_expression_in(expression, &substitutions.into())
}

pub(in crate::surface) fn substitute_contract_expression_in(
    expression: &ContractExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractExpression, String> {
    match expression {
        ContractExpression::IntegerLiteral(_) => Ok(expression.clone()),
        ContractExpression::ResourceField(access) => Ok(ContractExpression::ResourceField(
            match substitutions.instance_rename(&access.owner, access.identity) {
                Some(owner) => ResourceFieldAccess {
                    owner,
                    ..access.clone()
                },
                None => access.clone(),
            },
        )),
        ContractExpression::Negate(inner) => Ok(ContractExpression::Negate(Box::new(
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
        ContractExpression::QualifiedC { .. } | ContractExpression::CBinding(_) => {
            Ok(expression.clone())
        }
        ContractExpression::ArrayIndex {
            base,
            indexes,
            lowered,
        } => Ok(ContractExpression::ArrayIndex {
            base: Box::new(substitute_contract_expression_in(base, substitutions)?),
            indexes: indexes
                .iter()
                .map(|index| substitute_c_fragment_in(index, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            lowered: substitute_c_fragment_in(lowered, substitutions)?,
        }),
        ContractExpression::ResourceWildcard => Ok(expression.clone()),
        ContractExpression::ResourceCount(resource) => {
            let ResourceClause::Declared {
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
        ContractExpression::CFragment(CExpression::Variable(name)) => Ok(substitutions
            .value(name)
            .cloned()
            .unwrap_or_else(|| expression.clone())),
        ContractExpression::CFragment(expression) => {
            substitute_c_fragment_as_contract_in(expression, substitutions)
        }
        ContractExpression::Field {
            base,
            field,
            lowered,
        } => Ok(ContractExpression::Field {
            base: Box::new(substitute_contract_expression_in(base, substitutions)?),
            field: field.clone(),
            lowered: substitute_c_fragment_in(lowered, substitutions)?,
        }),
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
        ContractExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
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
        ContractExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_contract_expression_in(base, substitutions)?),
            Box::new(substitute_contract_expression_in(index, substitutions)?),
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
        ContractExpression::Call { name, arguments } => Ok(ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

fn substitute_c_fragment_as_contract_in(
    expression: &CExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractExpression, String> {
    substitute_c_fragment_as_contract_with_numerals_in(expression, substitutions, false)
}

pub(in crate::surface) fn substitute_c_fragment_as_contract_with_numerals<'a>(
    expression: &CExpression,
    substitutions: impl Into<ContractSubstitutions<'a>>,
    contextual_numerals: bool,
) -> Result<ContractExpression, String> {
    substitute_c_fragment_as_contract_with_numerals_in(
        expression,
        &substitutions.into(),
        contextual_numerals,
    )
}

fn substitute_c_fragment_as_contract_with_numerals_in(
    expression: &CExpression,
    substitutions: &ContractSubstitutions<'_>,
    contextual_numerals: bool,
) -> Result<ContractExpression, String> {
    match expression {
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value)))
            if contextual_numerals =>
        {
            let signed = *value as i32;
            let literal =
                ContractExpression::IntegerLiteral(i64::from(signed).unsigned_abs().to_string());
            Ok(if signed < 0 {
                ContractExpression::Negate(Box::new(literal))
            } else {
                literal
            })
        }
        CExpression::Value(_) => Ok(ContractExpression::CFragment(expression.clone())),
        CExpression::Variable(name) => Ok(substitutions
            .value(name)
            .cloned()
            .unwrap_or_else(|| ContractExpression::CFragment(expression.clone()))),
        CExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                left,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                right,
                substitutions,
                contextual_numerals,
            )?),
        )),
        CExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_c_fragment_as_contract_with_numerals_in(
                expression,
                substitutions,
                contextual_numerals,
            )?,
        ))),
        CExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                base,
                substitutions,
                contextual_numerals,
            )?),
            Box::new(substitute_c_fragment_as_contract_with_numerals_in(
                index,
                substitutions,
                contextual_numerals,
            )?),
        )),
        _ => Ok(ContractExpression::CFragment(substitute_c_fragment_in(
            expression,
            substitutions,
        )?)),
    }
}

pub(in crate::surface) fn substitute_c_fragment<'a>(
    expression: &CExpression,
    substitutions: impl Into<ContractSubstitutions<'a>>,
) -> Result<CExpression, String> {
    substitute_c_fragment_in(expression, &substitutions.into())
}

pub(in crate::surface) fn substitute_c_fragment_in(
    expression: &CExpression,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<CExpression, String> {
    match expression {
        CExpression::Value(_) | CExpression::FunctionAddress(_) => Ok(expression.clone()),
        CExpression::Variable(name) => {
            let Some(substitution) = substitutions.value(name) else {
                return Ok(expression.clone());
            };
            contract_expression_as_c_fragment(substitution).ok_or_else(|| {
                format!(
                    "cannot substitute non-C-fragment expression for `{name}` inside C fragment `{expression:?}`"
                )
            })
        }
        CExpression::Cast {
            expression,
            target_type,
            pointee_volatile,
            pointee_constant,
        } => Ok(CExpression::Cast {
            expression: Box::new(substitute_c_fragment_in(expression, substitutions)?),
            target_type: *target_type,
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
        }),
        CExpression::FloatNegate(expression) => Ok(CExpression::FloatNegate(Box::new(
            substitute_c_fragment_in(expression, substitutions)?,
        ))),
        CExpression::FloatClassification {
            expression,
            classification,
        } => Ok(CExpression::FloatClassification {
            expression: Box::new(substitute_c_fragment_in(expression, substitutions)?),
            classification: *classification,
        }),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => Ok(CExpression::Conditional {
            condition: Box::new(substitute_c_fragment_in(condition, substitutions)?),
            then_branch: Box::new(substitute_c_fragment_in(then_branch, substitutions)?),
            else_branch: Box::new(substitute_c_fragment_in(else_branch, substitutions)?),
        }),
        CExpression::AddressOf(body) => Ok(CExpression::AddressOf(Box::new(
            substitute_c_fragment_in(body, substitutions)?,
        ))),
        CExpression::PointerOffsetBytes { pointer, bytes } => Ok(CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_c_fragment_in(pointer, substitutions)?),
            bytes: *bytes,
        }),
        CExpression::LessThan(left, right) => Ok(CExpression::LessThan(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::LessEqual(left, right) => Ok(CExpression::LessEqual(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::GreaterThan(left, right) => Ok(CExpression::GreaterThan(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::GreaterEqual(left, right) => Ok(CExpression::GreaterEqual(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Equal(left, right) => Ok(CExpression::Equal(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::NotEqual(left, right) => Ok(CExpression::NotEqual(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Not(body) => Ok(CExpression::Not(Box::new(substitute_c_fragment_in(
            body,
            substitutions,
        )?))),
        CExpression::And(left, right) => Ok(CExpression::And(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Or(left, right) => Ok(CExpression::Or(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(substitute_c_fragment_in(left, substitutions)?),
            Box::new(substitute_c_fragment_in(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            substitute_c_fragment_in(expression, substitutions)?,
        ))),
        CExpression::Load(body) => Ok(CExpression::Load(Box::new(substitute_c_fragment_in(
            body,
            substitutions,
        )?))),
        CExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
        } => Ok(CExpression::TypedLoad {
            pointer: Box::new(substitute_c_fragment_in(pointer, substitutions)?),
            value_type: *value_type,
            volatile: *volatile,
        }),
        CExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(substitute_c_fragment_in(base, substitutions)?),
            Box::new(substitute_c_fragment_in(index, substitutions)?),
        )),
    }
}

pub(in crate::surface) fn contract_expression_as_c_fragment(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::ResourceField(_) => None,
        ContractExpression::IntegerLiteral(value) => {
            let value = value.parse::<u64>().ok()?;
            Some(CExpression::Value(if value <= i32::MAX as u64 {
                int32(value as u32)
            } else if value <= i64::MAX as u64 {
                CValue::Int64(Bitvector32Term::Int64Constant(value as i64))
            } else {
                CValue::UInt64(Bitvector32Term::UInt64Constant(value))
            }))
        }
        ContractExpression::Negate(inner) => {
            if let ContractExpression::IntegerLiteral(value) = inner.as_ref()
                && let Ok(value) = value.parse::<u64>()
                && value <= (i32::MAX as u64) + 1
            {
                return Some(CExpression::Value(int32(0u32.wrapping_sub(value as u32))));
            }
            Some(CExpression::Subtract(
                Box::new(CExpression::Value(int32(0))),
                Box::new(contract_expression_as_c_fragment(inner)?),
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
        | ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Field { lowered, .. } => Some(lowered.clone()),
        ContractExpression::Binding(name) | ContractExpression::CBinding(name) => {
            Some(CExpression::Variable(name.clone()))
        }
        ContractExpression::ResourceCount(_) => None,
        ContractExpression::ResourceWildcard => None,
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
        ContractExpression::ArrayIndex { lowered, .. } => Some(lowered.clone()),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

pub(in crate::surface) fn c_comparison_operator(
    operator: ComparisonOperator,
) -> CComparisonOperator {
    match operator {
        ComparisonOperator::Equal => CComparisonOperator::Equal,
        ComparisonOperator::NotEqual => CComparisonOperator::NotEqual,
        ComparisonOperator::In => unreachable!("membership is lowered before C comparisons"),
        ComparisonOperator::LessThan => CComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => CComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => CComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => CComparisonOperator::GreaterEqual,
    }
}

pub(in crate::surface) fn contract_expression_to_c_fragment(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::ResourceField(_) => None,
        ContractExpression::IntegerLiteral(_) | ContractExpression::Negate(_) => {
            resource_argument_to_c_expression(expression).ok()
        }
        ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicMatch { .. } => None,
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => None,
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Field { lowered, .. } => Some(lowered.clone()),
        ContractExpression::Binding(name) | ContractExpression::CBinding(name) => {
            Some(CExpression::Variable(name.clone()))
        }
        ContractExpression::ResourceCount(_) => None,
        ContractExpression::ResourceWildcard => None,
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
        ContractExpression::ArrayIndex { lowered, .. } => Some(lowered.clone()),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multidimensional_array_rewrite_updates_its_lowered_base() {
        let source_base = ContractExpression::CFragment(CExpression::Variable("old".into()));
        let target_base = ContractExpression::CFragment(CExpression::Variable("new".into()));
        let expression = ContractExpression::ArrayIndex {
            base: Box::new(source_base.clone()),
            indexes: vec![CExpression::Value(int32(0)), CExpression::Value(int32(1))],
            lowered: CExpression::Index(
                Box::new(CExpression::Variable("old".into())),
                Box::new(CExpression::Value(int32(1))),
            ),
        };
        let (rewritten, changed) =
            rewrite_contract_expression_exact(&expression, &source_base, &target_base);
        assert!(changed);
        let ContractExpression::ArrayIndex { lowered, .. } = rewritten else {
            panic!("array rewrite must retain its presentation node");
        };
        assert_eq!(
            lowered,
            CExpression::Index(
                Box::new(CExpression::Variable("new".into())),
                Box::new(CExpression::Value(int32(1))),
            )
        );
    }

    #[test]
    fn multidimensional_array_rewrite_fails_closed_for_non_c_bases() {
        let source_base = ContractExpression::CFragment(CExpression::Variable("old".into()));
        let expression = ContractExpression::ArrayIndex {
            base: Box::new(source_base.clone()),
            indexes: vec![CExpression::Value(int32(0)), CExpression::Value(int32(1))],
            lowered: CExpression::Index(
                Box::new(CExpression::Variable("old".into())),
                Box::new(CExpression::Value(int32(1))),
            ),
        };
        let target = ContractExpression::Call {
            name: "not_a_c_fragment".into(),
            arguments: vec![],
        };
        let (rewritten, changed) =
            rewrite_contract_expression_exact(&expression, &source_base, &target);
        assert!(!changed);
        assert_eq!(rewritten, expression);
    }
}
