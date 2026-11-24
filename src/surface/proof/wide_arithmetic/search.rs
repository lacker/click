//! Discovery over Surface proof presentations; semantic state remains in ProofObject.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Closes a `uint64` or `int64` order goal from the listed premises
    /// through their Integer observations. `Err(None)` is any other goal,
    /// which is left to the certificate families; `Err(Some(reason))` is a
    /// 64-bit order goal this route could not prove, with the step that
    /// stopped it.
    pub(in crate::surface::proof) fn try_wide_arithmetic_using(
        search_input: &Proof<'a>,
        surface_premises: &[ClickProposition],
    ) -> Result<Proof<'a>, Option<String>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_wide_arithmetic_using");
        // The caller wraps a refusal in the original arithmetic step's
        // diagnostic. Preserve bridge failures with raw summaries: rendering
        // their nested goals/premises here would embed a second diagnostic
        // inside that summary (and violate ClickError's debug invariant).
        let Some(_scope) = BridgeScope::enter() else {
            return Err(None);
        };
        let goal = search_input.goal();
        if let Some(carrier) = goal.and_then(|goal| match goal {
            Proposition::ConditionIs(_, true) => Carrier::of_order_goal(goal),
            _ => None,
        }) {
            // A `uint32` order this route misses keeps the certificate
            // families' refusal, which names the listed premises.
            if carrier == Carrier::UInt32 {
                return crate::kernel::search::ProofSearch::wide_arithmetic_with(
                    search_input,
                    carrier,
                    surface_premises,
                )
                .map_err(|_| None);
            }
            return crate::kernel::search::ProofSearch::wide_arithmetic_with(
                search_input,
                carrier,
                surface_premises,
            );
        }
        // An equality does not say which 64-bit type it compares, since
        // the two share one equality. A listed order premise does, and so
        // does a typed literal; with neither, the unsigned reading is
        // tried and then the signed one.
        if !matches!(&goal, Some(condition_source_0 @ Proposition::ConditionIs(
                _,
                true
            )) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                }, _))))
        {
            return Err(None);
        }
        if !search_input
            .surface_goal()
            .and_then(native_relation_parts)
            .is_some_and(|(left, right, ..)| linear(&left) && linear(&right))
        {
            return Err(None);
        }
        let written = |proposition: &ClickProposition| {
            relation_parts(proposition)
                .and_then(|(lower, upper, ..)| literal_carrier(&lower).or(literal_carrier(&upper)))
        };
        let stated = surface_premises
            .iter()
            .find_map(|premise| {
                search_input
                    .lower_cited_surface_proposition(premise, "`close() using` premise")
                    .ok()
                    .as_ref()
                    .and_then(Carrier::of)
            })
            .or_else(|| search_input.surface_goal().and_then(written))
            .or_else(|| surface_premises.iter().find_map(written));
        if let Some(carrier) = stated {
            return crate::kernel::search::ProofSearch::wide_arithmetic_with(
                search_input,
                carrier,
                surface_premises,
            );
        }
        let unsigned = match crate::kernel::search::ProofSearch::wide_arithmetic_with(
            search_input,
            Carrier::UInt64,
            surface_premises,
        ) {
            Ok(proof) => return Ok(proof),
            Err(reason) => reason,
        };
        let signed = match crate::kernel::search::ProofSearch::wide_arithmetic_with(
            search_input,
            Carrier::Int64,
            surface_premises,
        ) {
            Ok(proof) => return Ok(proof),
            Err(reason) => reason,
        };
        match (unsigned, signed) {
            (Some(unsigned), Some(signed)) => Err(Some(format!(
                "no listed premise says which 64-bit type the equality compares. Read as uint64: {unsigned}. Read as int64: {signed}"
            ))),
            (reason, other) => Err(reason.or(other)),
        }
    }

    /// [`Self::try_wide_arithmetic_using`] for a goal over `carrier`.
    pub(in crate::surface::proof) fn wide_arithmetic_with(
        search_input: &Proof<'a>,
        carrier: Carrier,
        surface_premises: &[ClickProposition],
    ) -> Result<Proof<'a>, Option<String>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("wide_arithmetic_with");
        let ty = carrier.name();
        let describe = crate::surface::diagnostics::describe_contract_expression;
        let spell = crate::surface::printing::source_click_proposition;
        let article = if carrier == Carrier::Int64 { "an" } else { "a" };
        let (goal_lower, goal_upper, goal_relation, goal_forward) = search_input
            .surface_goal()
            .and_then(native_relation_parts)
            .ok_or_else(|| Some(format!("the {ty} goal has no source spelling to read")))?;
        // A goal written the other way round, `n > i` or `not (i < n)`, is
        // the bridge's order read from the other side: prove it that way
        // round, then close the written goal from it.
        if !goal_forward {
            let forward = relate(
                carrier.typed_literals(&goal_lower),
                carrier.typed_literals(&goal_upper),
                goal_relation,
            );
            return search_input
                .driver()
                .apply_step(have(
                    forward,
                    vec![ProofStep::ArithmeticUsing(surface_premises.to_vec())],
                ))
                .and_then(|proof| proof.driver().apply_step(ProofStep::Known))
                .map_err(|error| Some(error.raw_summary().to_string()));
        }

        let goal_lower = carrier.typed_literals(&goal_lower);
        let goal_upper = carrier.typed_literals(&goal_upper);
        let mut proof = search_input.clone();
        // The Integer facts established so far, each an exact premise of
        // the Integer steps that follow.
        let mut facts = Vec::new();
        // What is still to be carried to Integer: a listed order premise,
        // or a sum or difference to observe term by term.
        enum Pending {
            Premise(
                ClickProposition,
                ContractExpression,
                ContractExpression,
                Relation,
            ),
            Operation(ContractExpression),
        }
        let mut pending = Vec::new();
        let mut operations = Vec::new();
        let mut atoms = Vec::new();
        let literal = |text: &str| ContractExpression::IntegerLiteral(text.to_string());
        for premise in surface_premises {
            let kernel = search_input
                .lower_cited_surface_proposition(premise, "`close() using` premise")
                .map_err(|error| {
                    Some(format!(
                        "the premise `{}` could not be read: {}",
                        spell(premise),
                        error.raw_summary()
                    ))
                })?;
            let equality = matches!(&kernel, condition_source_0 @ Proposition::ConditionIs(
                    _,
                    true
                ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        ..
                    }, _))));
            // An equality the kernel already holds by identity: a local
            // whose value is the other side, `next == i + 1u64` after
            // `next = i + 1`. It needs no bridge, since both observations
            // are one term, but the sum it names is still to be observed.
            if kernel == Proposition::condition_is(ConditionTerm::Constant(true), true)
                && let Some((left, right, Relation::Equal, _)) = relation_parts(premise)
            {
                for side in [
                    &carrier.typed_literals(&left),
                    &carrier.typed_literals(&right),
                ] {
                    collect_operations(side, &mut operations);
                    collect_atoms(side, &mut atoms);
                }
                continue;
            }
            if Carrier::of_order_goal(&kernel) != Some(carrier) && !equality {
                // An Integer premise is used as it is written. One that
                // compares exact observations still names the sums it
                // observes, which are carried to Integer as a native
                // premise's are.
                if compares_observations(premise)
                    && let Some((left, right, ..)) = native_relation_parts(premise)
                {
                    for side in [
                        &carrier.typed_literals(&left),
                        &carrier.typed_literals(&right),
                    ] {
                        collect_operations(side, &mut operations);
                        collect_atoms(side, &mut atoms);
                    }
                }
                facts.push(premise.clone());
                continue;
            }
            let (lower, upper, relation, _) = native_relation_parts(premise).ok_or(None)?;
            let lower = carrier.typed_literals(&lower);
            let upper = carrier.typed_literals(&upper);
            // An order written the other way round, `i > 0` or `not (i <
            // n)`, is carried below by first restating it the bridge's way
            // round, which `known` closes from the listed fact.
            collect_operations(&lower, &mut operations);
            collect_operations(&upper, &mut operations);
            collect_atoms(&lower, &mut atoms);
            collect_atoms(&upper, &mut atoms);
            pending.push(Pending::Premise(premise.clone(), lower, upper, relation));
        }
        collect_operations(&goal_lower, &mut operations);
        collect_operations(&goal_upper, &mut operations);
        collect_atoms(&goal_lower, &mut atoms);
        collect_atoms(&goal_upper, &mut atoms);
        // A value's observation is in its type's range. A sum bounded only
        // by another value, `i + 1` under `i < length`, is shown not to wrap
        // or overflow from that, with no bound on `length` listed, and so is
        // `i - 1` under `0 < i`. One application per value written, and only
        // where a sum or difference could need it, or an equality: `n <= 0`
        // leaves `n == 0` because no `uint64` is below zero.
        if !operations.is_empty() || goal_relation == Relation::Equal {
            let (minimum, maximum) = carrier.range();
            for atom in &atoms {
                let lower = order(literal(&minimum), to_integer(atom), false);
                let upper = order(to_integer(atom), literal(&maximum), false);
                let Ok(next) = proof
                    .driver()
                    .apply_step(have(lower.clone(), vec![type_range(lower.clone())]))
                    .and_then(|proof| {
                        proof
                            .driver()
                            .apply_step(have(upper.clone(), vec![type_range(upper.clone())]))
                    })
                else {
                    continue;
                };
                proof = next;
                facts.push(lower);
                facts.push(upper);
            }
        }
        pending.extend(operations.into_iter().map(Pending::Operation));

        // Each item is tried against the facts so far, and the passes repeat
        // while one succeeds: a sum is observed once the facts keep it in
        // range, and a premise over a signed sum once that sum is defined.
        // At most one pass per item, so the attempts are quadratic in the
        // listed premises and the operations written in them.
        let mut stuck = None;
        while !pending.is_empty() {
            let mut remaining = Vec::new();
            let mut progressed = false;
            let mut stuck_on_operation = false;
            stuck = None;
            for item in pending {
                let attempt = match &item {
                    Pending::Premise(premise, lower, upper, relation) => {
                        // The carry below is `close()`, whose refusal
                        // would name the observed reading rather than the
                        // listed premise the proof lacks.
                        let available = search_input
                            .lower_surface_proposition(premise, "arithmetic premise")
                            .is_ok_and(|lowered| {
                                search_input
                                    .facts()
                                    .listed_premise_available(&lowered, &[], false)
                            });
                        if !available {
                            return Err(Some(format!(
                                "arithmetic requires an unavailable exact premise: `{}`",
                                spell(premise)
                            )));
                        }
                        let observed = relate(to_integer(lower), to_integer(upper), *relation);
                        // Equal values have equal observations: rewriting
                        // by the premise leaves an identity.
                        // A negated order is first stated as the order it
                        // is, which is the same fact to the kernel.
                        let stated = relate(lower.clone(), upper.clone(), *relation);
                        // A premise written over exact observations is
                        // already that order, in the spelling that reads it.
                        let restated = if premise != &stated && !compares_observations(premise) {
                            proof
                                .driver()
                                .apply_step(have(stated.clone(), vec![ProofStep::Known]))
                        } else {
                            Ok(proof.clone())
                        };
                        // A comparison of exact observations is the native
                        // comparison of their carriers, so the Integer
                        // order is the stated premise itself.
                        let carried = vec![ProofStep::Known];
                        restated
                            .and_then(|proof| {
                                proof.driver().apply_step(have(observed.clone(), carried))
                            })
                            .map(|proof| (proof, observed))
                            .map_err(|error| {
                                format!(
                                    "the premise `{}` could not be carried to Integer order: {}",
                                    spell(premise),
                                    error.raw_summary()
                                )
                            })
                    }
                    Pending::Operation(operation) => {
                        let (left, right, subtract) = match operation {
                            ContractExpression::Add(left, right) => (left, right, false),
                            ContractExpression::Subtract(left, right) => (left, right, true),
                            _ => unreachable!("only sums and differences are collected"),
                        };
                        let exact = if subtract {
                            ContractExpression::Subtract(
                                Box::new(to_integer(left)),
                                Box::new(to_integer(right)),
                            )
                        } else {
                            ContractExpression::Add(
                                Box::new(to_integer(left)),
                                Box::new(to_integer(right)),
                            )
                        };
                        let out_of_range = |guard: &ClickProposition| {
                            format!(
                                "the listed premises do not show that `{}` stays within {ty} (`{}`); {article} {ty} sum or difference that may leave its range is not the sum or difference of its operands",
                                describe(operation),
                                spell(guard)
                            )
                        };
                        let prove = |proof: &Proof<'a>, proposition: &ClickProposition| {
                            proof
                                .driver()
                                .apply_step(have(
                                    proposition.clone(),
                                    vec![ProofStep::ArithmeticUsing(facts.clone())],
                                ))
                                .map_err(|error| {
                                    format!(
                                        "{}: {}",
                                        out_of_range(proposition),
                                        error.raw_summary()
                                    )
                                })
                        };
                        // The exact value lies in the type's range, by both
                        // bounds: an unsigned sum does not exceed the type,
                        // an unsigned difference does not go below zero, and
                        // a signed operation is then defined.
                        let (minimum, maximum) = carrier.range();
                        let lower = order(literal(&minimum), exact.clone(), false);
                        let upper = order(exact.clone(), literal(&maximum), false);
                        let bounded = prove(&proof, &lower).and_then(|proof| prove(&proof, &upper));
                        // Both bounds of a signed operation's exact value
                        // are its definedness, which they now file as a
                        // fact. Where an operand is itself a sum, being
                        // defined also says that sum is, which is a fact by
                        // now, and `known` joins the two.
                        let bounded = match carrier {
                            Carrier::UInt64 | Carrier::UInt32 => bounded,
                            Carrier::Int64 => bounded.and_then(|proof| {
                                let defined = ClickProposition::Defined {
                                    expression: operation.clone(),
                                };
                                proof
                                    .driver()
                                    .apply_step(have(defined, vec![ProofStep::Known]))
                                    .map_err(|error| {
                                        format!("{}: {}", out_of_range(&upper), error.raw_summary())
                                    })
                            }),
                        };
                        bounded.and_then(|proof| {
                            let equation = ClickProposition::Comparison {
                                left: to_integer(operation),
                                operator: ComparisonOperator::Equal,
                                right: exact.clone(),
                            };
                            proof
                                .driver()
                                .apply_step(have(
                                    equation.clone(),
                                    vec![operation_identity(lower, upper, equation.clone())],
                                ))
                                .map(|proof| (proof, equation))
                                .map_err(|error| {
                                    format!(
                                        "`{}` could not be observed term by term: {}",
                                        describe(operation),
                                        error.raw_summary()
                                    )
                                })
                        })
                    }
                };
                match attempt {
                    Ok((next, fact)) => {
                        proof = next;
                        facts.push(fact);
                        progressed = true;
                        // An observed unsigned sum or difference is itself
                        // a `uint64`, in the type's range. Stating that
                        // gives the Integer step one fact where it would
                        // otherwise need the ranges of every operand.
                        if matches!(carrier, Carrier::UInt64 | Carrier::UInt32)
                            && let Pending::Operation(operation) = &item
                        {
                            let (minimum, maximum) = carrier.range();
                            let lower = order(literal(&minimum), to_integer(operation), false);
                            let upper = order(to_integer(operation), literal(&maximum), false);
                            if let Ok(next) = proof
                                .driver()
                                .apply_step(have(lower.clone(), vec![type_range(lower.clone())]))
                                .and_then(|proof| {
                                    proof.driver().apply_step(have(
                                        upper.clone(),
                                        vec![type_range(upper.clone())],
                                    ))
                                })
                            {
                                proof = next;
                                facts.push(lower);
                                facts.push(upper);
                            }
                        }
                    }
                    Err(reason) => {
                        // Operations come before the premises that need
                        // them, so the first one left is the one to name.
                        if stuck.is_none()
                            || (matches!(item, Pending::Operation(_)) && !stuck_on_operation)
                        {
                            stuck_on_operation = matches!(item, Pending::Operation(_));
                            stuck = Some(reason);
                        }
                        remaining.push(item);
                    }
                }
            }
            pending = remaining;
            if !progressed {
                break;
            }
        }
        // A sum or premise that could not be carried is left as it is: its
        // observation is then one opaque value to the Integer claim, which
        // may not need to look inside it (`x + 1 < 8` from `x <= 6`, for a
        // compound `x`). If the claim does not follow, the reason reported
        // is the item that could not be carried.
        let uncarried = (!pending.is_empty()).then(|| {
            stuck.unwrap_or_else(|| {
                "the listed premises could not be carried to Integer order".to_string()
            })
        });

        let observed_goal = relate(
            to_integer(&goal_lower),
            to_integer(&goal_upper),
            goal_relation,
        );
        proof = proof.driver().apply_step(have(
                observed_goal.clone(),
                vec![ProofStep::ArithmeticUsing(facts)],
            ))
            .map_err(|error| {
                Some(match &uncarried {
                    Some(reason) => format!("{reason}: {}", error.raw_summary()),
                    None => format!(
                        "the goal's Integer reading `{}` does not follow from the listed premises' Integer readings by one Integer arithmetic step, which combines a pair of order premises and at most one more taken whole; state an intermediate fact with `have` first: {}",
                        spell(&observed_goal),
                        error.raw_summary()
                    ),
                })
            })?;
        // The observed goal is the native goal's own form, so the fact just
        // proved closes it.
        let _ = (goal_lower, goal_upper);
        let applied = proof
            .driver()
            .apply_step(ProofStep::Known)
            .map_err(|error| {
                Some(format!(
                    "the Integer claim could not be carried back: {}",
                    error.raw_summary()
                ))
            })?;
        if applied.is_complete() || applied.goal() != search_input.goal() {
            return Ok(applied);
        }
        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
            .ok()
            .flatten()
            .ok_or_else(|| Some("the bridged goal did not close".to_string()))
    }
}
