use super::*;

pub(in crate::surface) fn unfold_available_predicate_facts(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    available_pure_facts: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    if unfolded_predicates.is_empty() {
        return Ok(available_pure_facts.to_vec());
    }

    // SourceProof contexts can contain large execution propositions whose trees do
    // not mention a Click predicate at all. Rebuilding every one of those
    // trees for each `unfold` made this otherwise structural tactic scale with
    // the entire execution history. Predicate applications only occur at the
    // proposition level, so select the small relevant subset first.
    let to_unfold = available_pure_facts
        .iter()
        .filter(|proposition| {
            proposition_contains_named_predicate(proposition, unfolded_predicates)
        })
        .collect::<Vec<_>>();
    if to_unfold.is_empty() {
        return Ok(available_pure_facts.to_vec());
    }

    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut propositions = available_pure_facts.to_vec();
    for proposition in to_unfold {
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            proposition,
            &assumptions,
        )?;
        if &unfolded != proposition && !propositions.contains(&unfolded) {
            propositions.push(unfolded);
        }
    }
    Ok(propositions)
}

fn proposition_contains_named_predicate(proposition: &Proposition, names: &[String]) -> bool {
    match proposition {
        Proposition::Predicate { name, .. } => names.iter().any(|candidate| candidate == name),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_contains_named_predicate(left, names)
                || proposition_contains_named_predicate(right, names)
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => proposition_contains_named_predicate(body, names),
        _ => false,
    }
}

pub(in crate::surface) fn unfold_predicates_in_proposition(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Result<Proposition, String> {
    let mut active = BTreeSet::new();
    unfold_predicates_in_proposition_with_active(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        proposition,
        assumptions,
        &mut active,
    )
}

pub(in crate::surface) fn unfold_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &PureFactContext,
    active: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        Proposition::Predicate { name, arguments }
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
            let unfolded = instantiate_predicate_definition(
                definition,
                arguments,
                assumptions,
                predicate_environment,
                click_function_environment,
            )?;
            let unfolded = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &unfolded,
                assumptions,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        Proposition::And(left, right) => Ok(Proposition::And(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Not(body) => Ok(Proposition::Not(Box::new(
            unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?,
        ))),
        Proposition::Implies(left, right) => {
            let left = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                &right_assumptions,
                active,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        Proposition::ForAll { var, sort, body } => Ok(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Ok(Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        _ => Ok(proposition.clone()),
    }
}

pub(in crate::surface) fn instantiate_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[Term],
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let (state, values, array_refs) = decode_predicate_arguments(definition, arguments)?;
    // The body takes the route every proof-side proposition takes:
    // elaborated with the parameters bound to the decoded arguments and
    // lowered by the kernel at the decoded state.
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        definition.body(),
        assumptions,
        &values,
        &array_refs,
        &state,
        &state,
        None,
        &RecordedSnapshots::new(),
        predicate_environment,
        click_function_environment,
    )
}

pub(in crate::surface) fn decode_predicate_arguments(
    definition: &PredicateDefinition,
    arguments: &[Term],
) -> Result<(CState, BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let expanded_len = 1 + definition
        .parameters()
        .iter()
        .map(|parameter| {
            if parameter_is_click_array_ref(parameter) {
                2
            } else {
                1
            }
        })
        .sum::<usize>();

    if arguments.len() == expanded_len {
        let Some(Term::CState(state)) = arguments.first() else {
            return Err(format!(
                "predicate `{}` is missing its resource-state snapshot",
                definition.name()
            ));
        };
        let mut values = BTreeMap::new();
        let mut array_refs = BTreeMap::new();
        let mut default_memory = None;
        let mut index = 1;
        for parameter in definition.parameters() {
            if parameter_is_click_array_ref(parameter) {
                let Some(Term::CMemory(memory)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref memory",
                        definition.name(),
                        parameter.name()
                    ));
                };
                let Some(Term::CValue(CValue::Pointer(pointer))) = arguments.get(index + 1) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                default_memory.get_or_insert_with(|| memory.clone());
                let element_type =
                    click_array_element_type(parameter.c_type()).ok_or_else(|| {
                        format!(
                            "predicate `{}` argument `{}` is not an array-ref parameter",
                            definition.name(),
                            parameter.name()
                        )
                    })?;
                values.insert(
                    parameter.name().to_string(),
                    CValue::typed_pointer(
                        pointer.pointer().clone(),
                        element_type.pointer_to().unwrap(),
                    ),
                );
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        memory: memory.clone(),
                        pointer: pointer.pointer().clone(),
                        element_type,
                    },
                );
                index += 2;
            } else {
                let Some(Term::CValue(value)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` did not lower to a C value",
                        definition.name(),
                        parameter.name()
                    ));
                };
                values.insert(parameter.name().to_string(), value.clone());
                index += 1;
            }
        }
        return Ok((
            state
                .clone()
                .with_memory(default_memory.unwrap_or_default()),
            values,
            array_refs,
        ));
    }

    Err(format!(
        "predicate `{}` has malformed lowered argument count: expected {} expanded argument term(s), got {}",
        definition.name(),
        expanded_len,
        arguments.len()
    ))
}
