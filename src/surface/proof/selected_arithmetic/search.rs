//! Discovery over Surface proof presentations; semantic state remains in ProofObject.
use super::*;

// The existing rewrite history tracks goals, not producer allocations. Use
// the same state-aware identity as fact lookup so a fresh shared call
// argument does not restart a branch already visited through a native reading.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum RewriteGoalKey {
    Identity(crate::kernel::proof::PropositionIdentityKey),
    Exact(Proposition),
}
impl RewriteGoalKey {
    pub(super) fn new(goal: &Proposition) -> Self {
        crate::kernel::proof::proposition_identity_key(goal)
            .map(Self::Identity)
            .unwrap_or_else(|| Self::Exact(goal.clone()))
    }
}

// Planner policy follows the compared word, independently of its carrier.
// Shared machine roots spell their comparisons as Integer observations.
fn is_word32_equality(goal: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, true) = goal else {
        return false;
    };
    crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.native_compat(),
    )
    .is_some_and(|view| {
        !view.negated
            && view.relation == CompareRelation::Equal
            && matches!(
                view.format,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32
            )
    })
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    fn establish_carried_arithmetic(
        proof: &Proof<'a>,
        carried: &Carried,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("establish_carried_arithmetic");
        #[cfg(test)]
        BRIDGE_ESTABLISHMENTS.with(|count| count.set(count.get() + 1));
        match &carried.establish {
            Establish::Steps(steps) => Ok(steps
                .iter()
                .try_fold(proof.clone(), |proof, step| {
                    proof.driver().apply_step(step.clone())
                })
                .ok()),
            Establish::Operation {
                operation,
                left,
                right,
                subtract,
                format,
            } => {
                let exact = if *subtract {
                    ContractExpression::Subtract(
                        Box::new(to_integer(left)),
                        Box::new(to_integer(right)),
                    )
                } else {
                    ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
                };
                let (minimum, maximum) = format.bounds();
                let (minimum, maximum) = (minimum.to_string(), maximum.to_string());
                let (lower, upper) = (
                    relate(
                        integer_literal(&minimum),
                        exact.clone(),
                        Relation::LessEqual,
                    ),
                    relate(
                        exact.clone(),
                        integer_literal(&maximum),
                        Relation::LessEqual,
                    ),
                );
                // The identity, once both constant bounds of the exact value
                // are facts.
                let observe = |proof: &Proof<'a>| {
                    proof
                        .driver()
                        .apply_step(have(
                            carried.surface.clone(),
                            vec![operation_identity(
                                lower.clone(),
                                upper.clone(),
                                carried.surface.clone(),
                            )],
                        ))
                        .ok()
                };
                if format.is_signed() {
                    // Definedness already is the pair of ordinary bounds.
                    // Cite each bound with the ordinary conjunction/known
                    // rule before checking the mathematical observation.
                    let bounded =
                        [&lower, &upper]
                            .into_iter()
                            .try_fold(proof.clone(), |proof, bound| {
                                proof
                                    .driver()
                                    .apply_step(have(bound.clone(), vec![ProofStep::Known]))
                                    .ok()
                            });
                    if let Some(observed) = bounded.as_ref().and_then(observe) {
                        return Ok(Some(observed));
                    }
                    let Some(_operation_scope) = OperationBridgeScope::enter(operation) else {
                        return Ok(None);
                    };
                    // Not yet known to be defined: prove both Integer bounds
                    // of the exact value, which together are its
                    // definedness, then observe. Each operand's type range,
                    // which the far bound of the exact value usually rests
                    // on, is stated first.
                    let mut ranged = proof.clone();
                    for operand in [left, right] {
                        if matches!(to_integer(operand), ContractExpression::IntegerLiteral(_)) {
                            continue;
                        }
                        for bound in [
                            relate(
                                integer_literal(&minimum),
                                to_integer(operand),
                                Relation::LessEqual,
                            ),
                            relate(
                                to_integer(operand),
                                integer_literal(&maximum),
                                Relation::LessEqual,
                            ),
                        ] {
                            if let Ok(next) = ranged
                                .driver()
                                .apply_step(have(bound.clone(), vec![type_range(bound)]))
                            {
                                ranged = next;
                            }
                        }
                    }
                    let Some(next) =
                        crate::kernel::search::ProofSearch::prove_stated_fact(&(ranged), &lower)?
                    else {
                        return Ok(None);
                    };
                    let Some(next) =
                        crate::kernel::search::ProofSearch::prove_stated_fact(&(next), &upper)?
                    else {
                        return Ok(None);
                    };
                    // The complete native domain must be an explicit fact
                    // before its observation becomes a theorem argument.
                    let domain = ClickProposition::Defined {
                        expression: operation.clone(),
                    };
                    let scope = next.driver().open_have(domain)?;
                    let defined = scope.driver().apply_step(ProofStep::Known)?.join()?;
                    return Ok(observe(&defined));
                }
                // An unsigned operation that does not wrap: a sum at most
                // the type's maximum, a difference whose subtrahend is at
                // most its minuend.
                let guard = if *subtract {
                    relate(to_integer(right), to_integer(left), Relation::LessEqual)
                } else {
                    upper.clone()
                };
                let unsigned = |proof: &Proof<'a>| -> Result<Option<Proof<'a>>, ClickError> {
                    let Some(bounded) =
                        crate::kernel::search::ProofSearch::prove_stated_fact(proof, &lower)?
                    else {
                        return Ok(None);
                    };
                    let Some(bounded) =
                        crate::kernel::search::ProofSearch::prove_stated_fact(&(bounded), &upper)?
                    else {
                        return Ok(None);
                    };
                    Ok(observe(&bounded))
                };
                let Some(_operation_scope) = OperationBridgeScope::enter(operation) else {
                    return Ok(None);
                };
                if let Ok(next) = proof
                    .driver()
                    .apply_step(have(guard.clone(), vec![ProofStep::Known]))
                {
                    return unsigned(&next);
                }
                let Some(next) =
                    crate::kernel::search::ProofSearch::prove_stated_fact(proof, &guard)?
                else {
                    return Ok(None);
                };
                unsigned(&next)
            }
        }
    }

    /// The equality `a == b` a disequality goal `a != b` over integers
    /// (machine or `Integer`) denies, in kernel and source form: the fact
    /// `intro()` adds when it opens the goal's refutation.
    pub(in crate::surface::proof) fn disequality_goal_equality(
        search_input: &Proof<'a>,
    ) -> Option<(Proposition, ClickProposition)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("disequality_goal_equality");
        let kernel = match search_input.goal()? {
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((ConditionTerm::IntegerNotEqual(left, right), _)) =
                    condition_source_0.condition_native() =>
            {
                Proposition::condition_is(
                    ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                    true,
                )
            }
            condition_source_0 @ Proposition::ConditionIs(_, false)
                if let Some((condition @ (ConditionTerm::IntegerEqual(..)
                // An 8- or 16-bit equality is the same fact as the `int32`
                // equality of its widenings (rule K8).
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32
                        | MachineIntegerType::UInt32
                        | MachineIntegerType::Int8
                        | MachineIntegerType::UInt8
                        | MachineIntegerType::Int16
                        | MachineIntegerType::UInt16,
                    relation: CompareRelation::Equal,
                    ..
                }
                | ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                }), _)) = condition_source_0.condition_native() =>
            {
                Proposition::condition_is(condition.clone(), true)
            }
            _ => return None,
        };
        let surface = match search_input.surface_goal()? {
            ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::NotEqual,
                right,
            } => ClickProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::Equal,
                right: right.clone(),
            },
            ClickProposition::Not(inner)
                if matches!(
                    inner.as_ref(),
                    ClickProposition::Comparison {
                        operator: ComparisonOperator::Equal,
                        ..
                    }
                ) =>
            {
                inner.as_ref().clone()
            }
            _ => return None,
        };
        Some((kernel, surface))
    }

    /// Refute the equality in one arm of a proof-level split. The other arm
    /// has the requested disequality as a fact.
    pub(in crate::surface::proof) fn disequality_by_refutation(
        search_input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Option<Result<Proof<'a>, ClickError>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("disequality_by_refutation");
        let (_, equality) =
            crate::kernel::search::ProofSearch::disequality_goal_equality(search_input)?;
        let mut listed = premises.to_vec();
        listed.push(equality.clone());
        Some((|| {
            let (split_proof, split, ids) = search_input.split_focused_if(equality.clone())?;
            let marker = split_proof.checkpoint();
            let equal_arm = split_proof.focus_branch(ids[0])?;
            let falsehood = ClickProposition::Value(crate::surface::bool_literal(false));
            let refuted_scope = equal_arm.driver().open_have(falsehood.clone())?;
            let refuted = refuted_scope
                .driver()
                .apply_step(ProofStep::ArithmeticUsing(listed))?
                .join()?;
            let equal_done = refuted
                .driver()
                .apply_step(ProofStep::Contradiction(falsehood))?;
            let unequal_done = equal_done
                .focus_branch(ids[1])?
                .driver()
                .apply_step(ProofStep::Known)?;
            unequal_done.join_focused_if(&marker, split, ids, equality)
        })())
    }

    /// `solve`'s route for a disequality goal `a != b`: a linear refutation
    /// of `a == b` leaves `a` on one side of `b`, so prove `a < b`, or else
    /// `b < a`, by selected-premise arithmetic, and refute `a == b` from it.
    pub(in crate::surface::proof) fn try_disequality_by_selected_refutation(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_disequality_by_selected_refutation");
        let Some((_, ClickProposition::Comparison { left, right, .. })) =
            crate::kernel::search::ProofSearch::disequality_goal_equality(search_input)
        else {
            return Ok(None);
        };
        for order in [
            relate(left.clone(), right.clone(), Relation::Less),
            relate(right.clone(), left.clone(), Relation::Less),
        ] {
            check_verification_deadline()?;
            let Ok(scope) = search_input.driver().open_have(order.clone()) else {
                continue;
            };
            // An order that is itself a fact is not among the premises the
            // arithmetic selects; `known` states it.
            let closed = match scope.driver().apply_step(ProofStep::Known) {
                Ok(closed) => closed,
                Err(_) => {
                    let Some(closed) = (scope).driver().try_selected_arithmetic()? else {
                        continue;
                    };
                    closed
                }
            };
            let Ok(ordered) = closed.join() else {
                continue;
            };
            if let Some(Ok(closed)) =
                crate::kernel::search::ProofSearch::disequality_by_refutation(&(ordered), &[order])
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Close an `Integer` bound goal with selected-premise arithmetic after carrying the
    /// connected machine order facts to `Integer`. Any miss leaves the proof
    /// unchanged.
    pub(in crate::surface::proof) fn try_bridged_selected_arithmetic(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_bridged_selected_arithmetic");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        if !crate::kernel::proof::integer_arithmetic::written_integer_affine_claim(goal) {
            return Ok(None);
        }
        let Some(candidates) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                search_input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        let mut carried =
            crate::kernel::search::ProofSearch::carried_machine_facts(search_input, &candidates);
        // A mask is a single atom of the affine expression. Offer its
        // Integer bounds directly, even when the held word comparisons
        // are indexed under the compound word instead of its variables.
        for value in crate::kernel::proof::integer_arithmetic::integer_affine_machine_values(goal) {
            let Some(bounds) = crate::kernel::proof::fact_reasoning::literal_mask_bounds(&value)
            else {
                continue;
            };
            for bound in bounds {
                check_verification_deadline()?;
                if let Some(surface) = search_input.structural_proposition_candidate(&bound) {
                    carried.push(Carried {
                        establish: Establish::Steps(vec![have(
                            surface.clone(),
                            vec![ProofStep::Known],
                        )]),
                        surface,
                    });
                }
            }
        }
        // Every sum or difference an `Integer` claim observes, from the
        // goal, the carried facts, and the connected `defined(...)` facts,
        // and every one nested inside an observed operation: each gets its
        // term-by-term observation and its type range.
        let mut operations = proposition_operations(surface_goal);
        for item in &carried {
            operations.extend(proposition_operations(&item.surface));
        }
        operations.extend(crate::kernel::search::ProofSearch::defined_operations(
            search_input,
            &candidates,
        ));
        let mut seen: Vec<ContractExpression> = Vec::new();
        while let Some(operation) = operations.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if seen.contains(&operation) {
                continue;
            }
            seen.push(operation.clone());
            let (left, right, subtract) = match &operation {
                ContractExpression::Add(left, right) => (left, right, false),
                ContractExpression::Subtract(left, right) => (left, right, true),
                _ => continue,
            };
            for operand in [left.as_ref(), right.as_ref()] {
                if matches!(
                    operand,
                    ContractExpression::Add(..) | ContractExpression::Subtract(..)
                ) {
                    operations.push(operand.clone());
                }
            }
            let exact = if subtract {
                ContractExpression::Subtract(
                    Box::new(to_integer(left)),
                    Box::new(to_integer(right)),
                )
            } else {
                ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
            };
            // The operation's own format, from its lowered observation: one
            // rule at every width.
            let surface = relate(to_integer(&operation), exact, Relation::Equal);
            let Some(format) = search_input
                .lower_cited_surface_proposition(&surface, "planned carried fact")
                .ok()
                .as_ref()
                .and_then(observed_operation_format)
            else {
                continue;
            };
            carried.push(Carried {
                surface,
                establish: Establish::Operation {
                    left: left.as_ref().clone(),
                    right: right.as_ref().clone(),
                    subtract,
                    operation: operation.clone(),
                    format,
                },
            });
            carried.extend(range_items(&operation, format));
        }
        if carried.is_empty() {
            return Ok(None);
        }

        // Lower candidate statements without constructing proofs for them.
        // Only a successful arithmetic plan selects which bridge steps to issue.
        let planned = carried
            .iter()
            .filter_map(|item| {
                search_input
                    .lower_cited_surface_proposition(&item.surface, "planned carried fact")
                    .ok()
                    .map(|kernel| (kernel, item))
            })
            .collect::<Vec<_>>();
        let mut rejected = BTreeSet::new();
        let mut established = BTreeSet::new();
        let mut proof = search_input.clone();
        loop {
            let mut premises = candidates.clone();
            premises.extend(
                planned
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| !rejected.contains(index))
                    .map(|(_, (kernel, _))| kernel.clone()),
            );
            check_verification_deadline()?;
            let IntegerRefutation::Proved { premises: used, .. } =
                crate::instrumentation::measure_operation(
                    "surface",
                    "solve arithmetic",
                    "solve arithmetic: bridged integer refutation",
                    || refute_integer_goal(goal, &premises, &[]),
                )
            else {
                return Ok(None);
            };
            // A proposed bridge can have an unproved prerequisite, such as
            // an unsigned operation's no-wrap bound. Remove that candidate
            // and try another plan, retaining every successful construction.
            let mut failed = None;
            for (index, (kernel, item)) in planned.iter().enumerate() {
                if rejected.contains(&index)
                    || established.contains(&index)
                    || !used.contains(kernel)
                {
                    continue;
                }
                if proof.facts().contains(kernel) {
                    established.insert(index);
                    continue;
                }
                match Self::establish_carried_arithmetic(&proof, item)? {
                    Some(next) => {
                        proof = next;
                        established.insert(index);
                    }
                    None => {
                        failed = Some(index);
                        break;
                    }
                }
            }
            if let Some(index) = failed {
                rejected.insert(index);
                continue;
            }
            // The plan selected the premises; `arithmetic` proves the goal
            // from them. A cited fact with no source spelling cannot be
            // listed, so selected-premise arithmetic does not close the goal.
            let Some(listed) =
                used.iter()
                    .map(|premise| {
                        match planned.iter().enumerate().find(|(index, (kernel, _))| {
                            !rejected.contains(index) && kernel == premise
                        }) {
                            Some((_, (_, item))) => Some(item.surface.clone()),
                            None => crate::kernel::search::ProofSearch::resolve_solve_premises(
                                &(proof),
                                std::slice::from_ref(premise),
                                &[],
                            )
                            .and_then(|mut spelled| spelled.pop())
                            .map(|(_, surface)| surface),
                        }
                    })
                    .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            return attempt::candidate_outcome(
                proof
                    .driver()
                    .apply_step(ProofStep::ArithmeticUsing(listed)),
            );
        }
    }

    /// The equality-by-bounds closure as `solve` tries it early. A plain
    /// 64-bit equality, with no sum or difference on either side, waits for
    /// `solve`'s other strategies and the wide-equality route after them:
    /// proving it by bounds here would run a nested `solve` for each bound
    /// ahead of them.
    pub(in crate::surface::proof) fn try_equality_by_bounds_early(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_equality_by_bounds_early");
        if let (
            Some((
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    ..
                },
                true,
            )),
            Some(ClickProposition::Comparison { left, right, .. }),
        ) = (
            search_input.goal().and_then(Proposition::condition_native),
            search_input.surface_goal(),
        ) && !writes_sum_or_difference(left, right)
        {
            return Ok(None);
        }
        crate::kernel::search::ProofSearch::try_equality_by_bounds(search_input)
    }

    /// Close an `Integer` equality goal `l == r` by proving `l <= r` and
    /// `r <= l` with `solve` on each stated fact and joining them with
    /// `equal_from_bounds`. Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_equality_by_bounds(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_equality_by_bounds");
        crate::kernel::search::ProofSearch::equality_by_bounds(search_input, false)
    }

    /// [`Self::try_equality_by_bounds`], also for a plain 32-bit
    /// equality when `plain_32_bit`: `solve`'s last route, after the indexed
    /// native-reading route has missed, as it does for an Integer fact such
    /// as `to_integer(i) + 1 == 2`.
    pub(in crate::surface::proof) fn equality_by_bounds(
        search_input: &Proof<'a>,
        plain_32_bit: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("equality_by_bounds");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        // A plain 32-bit equality, with no sum or difference on either side,
        // already has the indexed native-reading arithmetic route; proving it by
        // bounds would repeat that search for each bound.
        if !plain_32_bit
            && is_word32_equality(goal)
            && let ClickProposition::Comparison { left, right, .. } = surface_goal
            && !writes_sum_or_difference(left, right)
        {
            return Ok(None);
        }
        // A 64-bit equality has a reading in each signedness; either is an
        // Integer equality.
        if !crate::kernel::proof::integer_arithmetic::integer_affine_claims(goal)
            .iter()
            .any(|claim| {
                claim.relation
                    == crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::Equal
            })
        {
            return Ok(None);
        }
        let _arithmetic_scope = is_word32_equality(goal).then(MachineEqualityBridgeScope::enter);
        // A native equality is split as its observed reading, so a bound
        // such as `0u64 <= x` that holds by its type stays a stated Integer
        // fact rather than folding to `true`.
        let observed =
            super::smart_closures::observed_native_surface_comparison(goal, surface_goal);
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = &observed
        else {
            return Ok(None);
        };
        let lower = relate(left.clone(), right.clone(), Relation::LessEqual);
        let upper = relate(right.clone(), left.clone(), Relation::LessEqual);
        // A lower bound the facts prove alone needs no operation identity.
        // Otherwise the goal's identities are proved once, here, rather than
        // once inside each bound's `have`, where the first bound's proof of
        // them would be dropped when its `have` closes.
        let Ok(scope) = search_input.driver().open_have(lower.clone()) else {
            return Ok(None);
        };
        let mut lower_alone = scope
            .driver()
            .try_selected_arithmetic_without_identities()?;
        let mut proof = match lower_alone {
            Some(_) => search_input.clone(),
            None => match crate::kernel::search::ProofSearch::with_goal_operation_identities(
                search_input,
                &observed,
            )? {
                // A goal that is one of the identities needs no bounds.
                Some(identities) => {
                    if let Some(closed) = attempt::candidate_outcome(
                        identities.driver().apply_step(ProofStep::Known),
                    )? {
                        return Ok(Some(closed));
                    }
                    identities
                }
                None => search_input.clone(),
            },
        };
        for bound in [&lower, &upper] {
            let closed = match lower_alone.take() {
                Some(closed) => closed,
                None => {
                    let Ok(scope) = proof.driver().open_have(bound.clone()) else {
                        return Ok(None);
                    };
                    // Splitting an equality must not recursively launch general
                    // solve on both orders. The selected arithmetic route either
                    // emits a bound from its premises or misses promptly.
                    let Some(closed) = scope
                        .driver()
                        .try_selected_arithmetic_without_identities()?
                    else {
                        return Ok(None);
                    };
                    closed
                }
            };
            let Ok(joined) = closed.join() else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(
            proof
                .driver()
                .apply_step(ProofStep::ArithmeticUsing(vec![lower, upper])),
        )
    }

    /// A goal that restates an available fact through one connected
    /// equality, such as `f(Node(..)) == 1` beside `f(t) == 1` and
    /// `t == Node(..)`: one `rewrite` and `known`. `solve` tries it
    /// before the connected-equality chain, which would prove it too, at
    /// greater cost. At most `SINGLE_REWRITES` rewrites.
    pub(in crate::surface::proof) fn try_single_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_single_rewrite_closure");
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some(equalities) = crate::kernel::search::proposition_search::connected_equalities(
            search_input.facts().assumptions(),
            goal,
        ) else {
            return Ok(None);
        };
        let mut attempts = 0;
        for equality in &equalities {
            let applies = |kernel: &Proposition| {
                equality_rewrite_applies(goal, kernel)
                    || reverse_equality(kernel)
                        .is_some_and(|reverse| equality_rewrite_applies(goal, &reverse))
            };
            if !applies(equality) {
                continue;
            }
            check_verification_deadline()?;
            let Some(surface) = crate::kernel::search::ProofSearch::available_rewrite_equality(
                search_input,
                equality,
            ) else {
                continue;
            };
            let kernel = equality.clone();
            let mut forms = Vec::new();
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    search_input.lower_surface_proposition(&unanchored, "`solve` rewrite equality")
            {
                forms.extend(oriented_forms(lowered, unanchored));
            }
            forms.extend(oriented_forms(kernel, surface));
            for (kernel, surface) in forms {
                if !equality_rewrite_applies(goal, &kernel) {
                    continue;
                }
                if attempts == SINGLE_REWRITES {
                    return Ok(None);
                }
                attempts += 1;
                let Ok(rewritten) = search_input
                    .driver()
                    .apply_step(ProofStep::Rewrite(surface))
                else {
                    continue;
                };
                if let Ok(closed) = rewritten.driver().apply_step(ProofStep::Known)
                    && (closed.focused_discharged() || closed.is_complete())
                {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Rewrite the goal by the equality facts connected to it until
    /// `known`, `normalize` or another direct closer finishes it: the
    /// congruence step `solve` takes only once its decider has selected the
    /// premises, here offered every connected equality, algebraic `==` facts
    /// included. Each rewrite is an ordinary checked step.
    pub(in crate::surface::proof) fn try_connected_equality_chain_closure(
        search_input: &Proof<'a>,
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_connected_equality_chain_closure");
        use crate::kernel::proof::equality_rewrite::{equality_rewrite_applies, reverse_equality};
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        // Intro searches an implication/forall body with its guard or fresh
        // variable available. Rewriting the entire wrapper repeats that body
        // search for every candidate chain, including already-refuted leaves.
        // Keep connected equality search on the resulting selected goal, as
        // the function-unfold strategy does for the same logical wrappers.
        if matches!(goal, Proposition::Implies(..) | Proposition::ForAll { .. }) {
            return Ok(None);
        }
        let Some(mut equalities) = crate::kernel::search::proposition_search::connected_equalities(
            search_input.facts().assumptions(),
            goal,
        ) else {
            return Ok(None);
        };
        // Equalities that rewrite the goal itself come first, so the
        // spelling cap keeps the ones a short chain starts from.
        let applies = |kernel: &Proposition| {
            equality_rewrite_applies(goal, kernel)
                || reverse_equality(kernel)
                    .is_some_and(|reverse| equality_rewrite_applies(goal, &reverse))
        };
        equalities.sort_by_cached_key(|equality| !applies(equality));
        let forms = |kernel: Proposition, surface: ClickProposition| {
            let mut forms = oriented_forms(kernel.clone(), surface.clone());
            if matches!(closers, RewriteClosers::GoalLocal { .. })
                && forms
                    .first()
                    .is_some_and(|(_, observed)| observed != &surface)
                && let Some(native) = explicit_native_rewrite_equality(&kernel, &surface)
            {
                // A native rewrite preserves a structural successor in an
                // abstract contract post-state where its Integer observation
                // can change the goal's carrier. Casts keep that native
                // arithmetic explicit when the certificate is reparsed.
                let reverse = reverse_equality(&kernel)
                    .zip(super::fixed_state_proofs::reverse_surface_equality(&native));
                let mut native_forms = vec![(kernel, native)];
                native_forms.extend(reverse);
                native_forms.append(&mut forms);
                return native_forms;
            }
            forms
        };
        let mut candidates: Vec<Vec<(Proposition, ClickProposition)>> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if candidates.len() >= REWRITE_EQUALITIES {
                break;
            }
            let Some(surface) = crate::kernel::search::ProofSearch::available_rewrite_equality(
                search_input,
                equality,
            ) else {
                continue;
            };
            let kernel = equality.clone();
            // A fact recorded at a statement's entry is spelled there; its
            // unanchored form denotes the same fact where the proof stands
            // when nothing it names has changed since, which lowering and
            // the checked rewrite decide. Offer the unanchored form first.
            if let Some(unanchored) = unanchored_equality(&surface)
                && let Ok(lowered) =
                    search_input.lower_surface_proposition(&unanchored, "`solve` rewrite equality")
            {
                candidates.push(forms(lowered, unanchored));
            }
            candidates.push(forms(kernel, surface));
        }
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut seen =
            std::collections::BTreeMap::from([(RewriteGoalKey::new(goal), REWRITE_DEPTH)]);
        let mut budget = RewriteBudget {
            attempts: REWRITE_ATTEMPTS,
            solve_closures: REWRITE_SOLVE_CLOSURES,
        };
        crate::kernel::search::ProofSearch::rewrite_search(
            search_input,
            &candidates,
            &mut vec![false; candidates.len()],
            REWRITE_DEPTH,
            &mut seen,
            &mut budget,
            closers,
        )
    }

    /// The same search over equalities a step selected or listed instead
    /// of the goal's connected facts: `solve`'s premises from its
    /// derivation, or a `close() using` list. Each equality is used at most
    /// once, so the chain is as long as the list allows, and `closers`
    /// says what may close a rewritten goal.
    pub(in crate::surface::proof) fn try_premise_equality_chain_closure(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, ClickProposition)],
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_premise_equality_chain_closure");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let candidates = premise_pairs
            .iter()
            .filter(|(kernel, _)| is_rewrite_equality(kernel))
            .take(REWRITE_EQUALITIES)
            .map(|(kernel, surface)| oriented_forms(kernel.clone(), surface.clone()))
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return Ok(None);
        }
        let mut seen =
            std::collections::BTreeMap::from([(RewriteGoalKey::new(goal), candidates.len())]);
        let mut budget = RewriteBudget {
            attempts: REWRITE_ATTEMPTS,
            solve_closures: REWRITE_SOLVE_CLOSURES,
        };
        crate::kernel::search::ProofSearch::rewrite_search(
            search_input,
            &candidates,
            &mut vec![false; candidates.len()],
            candidates.len(),
            &mut seen,
            &mut budget,
            closers,
        )
    }

    /// `solve` on a goal about the fields of a value that two connected facts
    /// equate to constructor applications, `t == Node(c, r)` and
    /// `t == Node(Black, Empty)`: it states `Node(c, r) == Node(Black, Empty)`,
    /// proved by rewriting each application to `t`, and `solve` then reads the
    /// fields' equalities (or the constructors' mismatch) from it. At most
    /// `CONSTRUCTOR_EQUATIONS` connected equations are paired.
    pub(in crate::surface::proof) fn try_constructor_join_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_join_closure");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some(equalities) = crate::kernel::search::proposition_search::connected_equalities(
            search_input.facts().assumptions(),
            goal,
        ) else {
            return Ok(None);
        };
        // Each equation as the value it names, its constructor application,
        // and the fact oriented `application == value`.
        let mut equations: Vec<(
            crate::kernel::AlgebraicTerm,
            ContractExpression,
            ClickProposition,
        )> = Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            if equations.len() >= CONSTRUCTOR_EQUATIONS {
                break;
            }
            let Some((left, right)) = algebraic_sides(equality) else {
                continue;
            };
            let (left_built, right_built) = (is_constructor(left), is_constructor(right));
            if left_built == right_built {
                continue;
            }
            let Some((_, surface)) = crate::kernel::search::ProofSearch::resolve_solve_premises(
                search_input,
                std::slice::from_ref(equality),
                &[],
            )
            .and_then(|mut spelled| spelled.pop()) else {
                continue;
            };
            let ClickProposition::Comparison {
                left: written_left,
                operator: ComparisonOperator::Equal,
                right: written_right,
            } = surface
            else {
                continue;
            };
            let (value, application, value_written) = if left_built {
                (right, written_left, written_right)
            } else {
                (left, written_right, written_left)
            };
            let oriented = ClickProposition::Comparison {
                left: application.clone(),
                operator: ComparisonOperator::Equal,
                right: value_written,
            };
            equations.push((value.clone(), application, oriented));
        }
        for (index, (value, first, first_fact)) in equations.iter().enumerate() {
            for (other, second, second_fact) in &equations[index + 1..] {
                check_verification_deadline()?;
                if value != other || first == second {
                    continue;
                }
                let joined = ClickProposition::Comparison {
                    left: first.clone(),
                    operator: ComparisonOperator::Equal,
                    right: second.clone(),
                };
                let Ok(next) = search_input.driver().apply_step(have(
                    joined,
                    vec![
                        ProofStep::Rewrite(first_fact.clone()),
                        ProofStep::Rewrite(second_fact.clone()),
                        ProofStep::Known,
                    ],
                )) else {
                    continue;
                };
                if next.is_complete() {
                    return Ok(Some(next));
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_solve_closure(&(next))?
                {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// `solve` on a goal that is a condition inside a function's definition,
    /// given a fact `f(args) == k` whose arguments decide the definition's
    /// `match`es: `is_rb(left) == 1` from `is_rb(Node(.., left, right)) == 1`.
    /// Where every way through the definition's `if`s that does not take
    /// the goal's `then` arm ends in a constant other than `k`, the fact
    /// forces the goal. The proof is the one written by hand: `if` the goal
    /// holds, `known`; otherwise split on each condition met before the
    /// goal's, and at each end `have f(args) != k` by `unfold` and
    /// `normalize` using the conditions taken, then `contradiction`.
    pub(in crate::surface::proof) fn try_definition_condition_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_definition_condition_closure");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        let Some(equalities) = crate::kernel::search::proposition_search::connected_equalities(
            search_input.facts().assumptions(),
            goal,
        ) else {
            return Ok(None);
        };
        let functions = search_input.spec_functions();
        // Each fact as written, and the constructor each connected equation
        // names a value as, with that equation oriented `C(...) == value`.
        let mut spelled = Vec::new();
        let mut constructors: Vec<(ContractExpression, ContractExpression, ClickProposition)> =
            Vec::new();
        for equality in &equalities {
            check_verification_deadline()?;
            let Some((kernel, fact)) = crate::kernel::search::ProofSearch::resolve_solve_premises(
                search_input,
                std::slice::from_ref(equality),
                &[],
            )
            .and_then(|mut spelled| spelled.pop()) else {
                continue;
            };
            // A fact recorded at an earlier point is spelled there; its
            // unanchored form names the same fact when it lowers to it here.
            let fact = match unanchored_equality(&fact) {
                Some(unanchored)
                    if search_input
                        .lower_surface_proposition(&unanchored, "`solve` definition fact")
                        .is_ok_and(|lowered| lowered == kernel) =>
                {
                    unanchored
                }
                _ => fact,
            };
            if let ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = &fact
            {
                let built = |side: &ContractExpression| {
                    matches!(side, ContractExpression::AlgebraicConstructor { .. })
                };
                if built(left) != built(right) && constructors.len() < CONSTRUCTOR_EQUATIONS {
                    let (application, value) = if built(left) {
                        (left, right)
                    } else {
                        (right, left)
                    };
                    constructors.push((
                        value.clone(),
                        application.clone(),
                        ClickProposition::Comparison {
                            left: application.clone(),
                            operator: ComparisonOperator::Equal,
                            right: value.clone(),
                        },
                    ));
                }
            }
            spelled.push(fact);
        }
        let goal_forms = DefinitionGoal {
            text: crate::surface::printing::identity_click_proposition(surface_goal),
            surface: surface_goal,
            kernel: goal,
        };
        let mut tried = 0;
        for fact in &spelled {
            check_verification_deadline()?;
            let ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = fact
            else {
                continue;
            };
            let (call, value_side, call_left) = match (left, right) {
                (ContractExpression::Call { .. }, value) => (left, value, true),
                (value, ContractExpression::Call { .. }) => (right, value, false),
                _ => continue,
            };
            let (ContractExpression::Call { name, arguments }, Some(value)) =
                (call, definition_end_value(value_side))
            else {
                continue;
            };
            let truth = crate::surface::bool_literal_value(value_side).is_some();
            let Some(definition) = functions.get(name) else {
                continue;
            };
            let Some(definition_body) = definition.body() else {
                continue;
            };
            if definition.parameters().len() != arguments.len() {
                continue;
            }
            if tried == DEFINITION_FACTS {
                break;
            }
            tried += 1;
            // The fact as written, and the fact with each argument a connected
            // equation names as a constructor replaced by it, stated by
            // rewriting it back: `match` arms over the argument are decided
            // only in the second.
            let mut readings = vec![(arguments.clone(), fact.clone(), None)];
            let mut rewrites = Vec::new();
            let restated = arguments
                .iter()
                .map(
                    |argument| match constructors.iter().find(|(value, _, _)| value == argument) {
                        Some((_, application, equation)) => {
                            rewrites.push(ProofStep::Rewrite(equation.clone()));
                            application.clone()
                        }
                        None => argument.clone(),
                    },
                )
                .collect::<Vec<_>>();
            if !rewrites.is_empty() {
                let restated_call = ContractExpression::Call {
                    name: name.clone(),
                    arguments: restated.clone(),
                };
                let restated_fact = ClickProposition::Comparison {
                    left: if call_left {
                        restated_call.clone()
                    } else {
                        left.clone()
                    },
                    operator: ComparisonOperator::Equal,
                    right: if call_left {
                        right.clone()
                    } else {
                        restated_call
                    },
                };
                rewrites.push(ProofStep::Known);
                readings.push((restated, restated_fact, Some(rewrites)));
            }
            for (arguments, fact, restatement) in readings {
                // Plan first: it reads only the definition, so a fact whose
                // definition never reaches the goal costs no checked step.
                let environment = definition
                    .parameters()
                    .iter()
                    .zip(&arguments)
                    .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                    .collect::<BinderMap<_>>();
                let mut leaves = 0;
                let mut meets_goal = false;
                let Some(plan) = crate::kernel::search::ProofSearch::definition_condition_plan(
                    search_input,
                    definition_body,
                    &environment,
                    &goal_forms,
                    value,
                    &mut leaves,
                    &mut meets_goal,
                    &[],
                ) else {
                    continue;
                };
                if !meets_goal {
                    continue;
                }
                let base = match restatement {
                    None => search_input.clone(),
                    Some(steps) => {
                        match search_input.driver().apply_step(have(fact.clone(), steps)) {
                            Ok(base) => base,
                            Err(_) => continue,
                        }
                    }
                };
                if let Some(closed) = crate::kernel::search::ProofSearch::read_definition_condition(
                    &(base),
                    &plan,
                    surface_goal,
                    name,
                    &arguments,
                    fact,
                    call_left,
                    truth,
                )? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Closes the goal from one fact `f(arguments) == value` along `plan`,
    /// as [`Self::try_definition_condition_closure`] describes.
    pub(super) fn read_definition_condition(
        search_input: &Proof<'a>,
        plan: &DefinitionPlan,
        surface_goal: &ClickProposition,
        name: &str,
        arguments: &[ContractExpression],
        fact: ClickProposition,
        call_left: bool,
        truth: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("read_definition_condition");
        let ClickProposition::Comparison { left, right, .. } = &fact else {
            return Ok(None);
        };
        let call = if call_left { left } else { right };
        let refutation = DefinitionRefutation {
            application: ClickFunctionApplication {
                name: name.to_string(),
                arguments: arguments.to_vec(),
            },
            // A `bool` fact is refuted by its negation, which lowers to the
            // exact opposite polarity `contradiction` reads.
            differs: if truth {
                ClickProposition::Not(Box::new(fact.clone()))
            } else {
                ClickProposition::Comparison {
                    left: if call_left {
                        call.clone()
                    } else {
                        left.clone()
                    },
                    operator: ComparisonOperator::NotEqual,
                    right: if call_left {
                        right.clone()
                    } else {
                        call.clone()
                    },
                }
            },
            fact: fact.clone(),
        };
        let Ok((split_proof, split, ids)) = search_input.split_focused_if(surface_goal.clone())
        else {
            return Ok(None);
        };
        let marker = split_proof.checkpoint();
        let Some(then_done) = split_proof
            .focus_branch(ids[0])
            .and_then(|branch| branch.driver().apply_step(ProofStep::Known))
            .ok()
            .filter(Proof::focused_discharged)
        else {
            return Ok(None);
        };
        let Ok(else_branch) = then_done.focus_branch(ids[1]) else {
            return Ok(None);
        };
        let Some(else_done) = crate::kernel::search::ProofSearch::refute_definition_ends(
            &(else_branch),
            plan,
            &refutation,
            &[ClickProposition::Not(Box::new(surface_goal.clone()))],
        )?
        else {
            return Ok(None);
        };
        Ok(else_done
            .join_focused_if(&marker, split, ids, surface_goal.clone())
            .ok())
    }

    /// The conditional tree of a definition body under `environment`, cut
    /// at the goal's own condition, whose `else` arm alone is followed. A
    /// `match` must meet a constructor; an end that applies a defined
    /// function is followed into that definition, at most
    /// `DEFINITION_UNFOLDS` deep, and each end that remains must be an
    /// integer or `bool` constant other than `value`. `unfolds` are the
    /// applications already followed to reach `body`. `None` when any of
    /// that fails or the tree has more than `DEFINITION_LEAVES` ends.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn definition_condition_plan(
        search_input: &Proof<'a>,
        body: &ContractExpression,
        environment: &BinderMap<ContractExpression>,
        goal: &DefinitionGoal<'_>,
        value: i128,
        leaves: &mut usize,
        meets_goal: &mut bool,
        unfolds: &[ClickFunctionApplication],
    ) -> Option<DefinitionPlan> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("definition_condition_plan");
        match body {
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = substitute_click_proposition(condition, environment).ok()?;
                // Compared as written first; a condition spelled otherwise,
                // as `v == x` against a postcondition's `result == x`, is
                // lowered only when its shape is the goal's. The checked
                // steps decide whether the condition is the goal.
                if crate::surface::printing::identity_click_proposition(&condition) == goal.text
                    || (same_shape(&condition, goal.surface)
                        && search_input
                            .lower_surface_proposition(&condition, "`solve` definition condition")
                            .is_ok_and(|lowered| lowered == *goal.kernel))
                {
                    *meets_goal = true;
                    return crate::kernel::search::ProofSearch::definition_condition_plan(
                        search_input,
                        else_branch,
                        environment,
                        goal,
                        value,
                        leaves,
                        meets_goal,
                        unfolds,
                    );
                }
                let then_plan = crate::kernel::search::ProofSearch::definition_condition_plan(
                    search_input,
                    then_branch,
                    environment,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    unfolds,
                )?;
                let else_plan = crate::kernel::search::ProofSearch::definition_condition_plan(
                    search_input,
                    else_branch,
                    environment,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    unfolds,
                )?;
                Some(DefinitionPlan::Split {
                    condition,
                    then_plan: Box::new(then_plan),
                    else_plan: Box::new(else_plan),
                })
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                let ContractExpression::AlgebraicConstructor {
                    variant, arguments, ..
                } = substitute_contract_expression(scrutinee, environment).ok()?
                else {
                    return None;
                };
                let arm = arms.iter().find(|arm| arm.variant == variant)?;
                if arm.bindings.len() != arguments.len() {
                    return None;
                }
                let mut environment = environment.clone();
                environment.extend(arm.bindings.iter().cloned().zip(arguments));
                crate::kernel::search::ProofSearch::definition_condition_plan(
                    search_input,
                    &arm.body,
                    &environment,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    unfolds,
                )
            }
            ContractExpression::Call { name, arguments } if unfolds.len() < DEFINITION_UNFOLDS => {
                let definition = search_input.spec_functions().get(name)?;
                if definition.parameters().len() != arguments.len() {
                    return None;
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| substitute_contract_expression(argument, environment).ok())
                    .collect::<Option<Vec<_>>>()?;
                let inner = definition
                    .parameters()
                    .iter()
                    .zip(&arguments)
                    .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                    .collect::<BinderMap<_>>();
                let mut unfolds = unfolds.to_vec();
                unfolds.push(ClickFunctionApplication {
                    name: name.clone(),
                    arguments,
                });
                crate::kernel::search::ProofSearch::definition_condition_plan(
                    search_input,
                    definition.body()?,
                    &inner,
                    goal,
                    value,
                    leaves,
                    meets_goal,
                    &unfolds,
                )
            }
            end => {
                *leaves += 1;
                (*leaves <= DEFINITION_LEAVES
                    && definition_end_value(end).is_some_and(|end| end != value))
                .then(|| DefinitionPlan::End {
                    unfolds: unfolds.to_vec(),
                    value: end.clone(),
                })
            }
        }
    }

    /// Closes the focused branch, where the goal is false, along `plan`:
    /// each split is a proof `if`, and each end refutes the fact.
    pub(super) fn refute_definition_ends(
        search_input: &Proof<'a>,
        plan: &DefinitionPlan,
        refutation: &DefinitionRefutation,
        taken: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("refute_definition_ends");
        check_verification_deadline()?;
        // A split may revisit a guard already established by the caller.
        // Its impossible arm needs only the explicit conflicting guard.
        if let Some(guard) = taken.last()
            && let Ok(closed) = search_input
                .driver()
                .apply_step(ProofStep::Contradiction(guard.clone()))
        {
            return Ok(Some(closed));
        }
        match plan {
            DefinitionPlan::End { unfolds, value } => {
                let refuted = (|| {
                    let equation = ClickProposition::Comparison {
                        left: ContractExpression::Call {
                            name: refutation.application.name.clone(),
                            arguments: refutation.application.arguments.clone(),
                        },
                        operator: ComparisonOperator::Equal,
                        right: value.clone(),
                    };
                    let mut scope = search_input.driver().open_have(equation.clone())?;
                    for application in std::iter::once(&refutation.application).chain(unfolds) {
                        if scope.is_complete() {
                            break;
                        }
                        scope = scope
                            .driver()
                            .apply_step(ProofStep::UnfoldFunction(application.clone()))?;
                    }
                    if !scope.is_complete() {
                        if let Ok(closed) = scope.driver().apply_step(ProofStep::Known) {
                            scope = closed;
                        } else if let Some(rewritten) =
                            scope.driver().try_rewrite_conditional_arms_using(taken)?
                        {
                            scope = rewritten;
                            if !scope.is_complete() {
                                scope = scope.driver().apply_step(ProofStep::Known)?;
                            }
                        }
                    }
                    if let Some(goal) = scope.body().surface_goal()
                        && !scope.is_complete()
                    {
                        return Err(scope.body().step_error(format!(
                            "definition branch did not prove its literal: {}",
                            crate::surface::printing::source_click_proposition(goal),
                        )));
                    }
                    let proof = scope.join()?;
                    let mut differs = proof.driver().open_have(refutation.differs.clone())?;
                    differs = differs.driver().apply_step(ProofStep::Rewrite(equation))?;
                    if !differs.is_complete() {
                        differs = differs.driver().apply_step(ProofStep::Known)?;
                    }
                    differs
                        .join()?
                        .driver()
                        .apply_step(ProofStep::Contradiction(refutation.fact.clone()))
                })();
                if let Some(closed) =
                    attempt::candidate_outcome(refuted)?.filter(Proof::focused_discharged)
                {
                    return Ok(Some(closed));
                }

                // Some unfolds expose constructor matches as well as conditionals.
                // Keep the checked route when arm equations cannot express the
                // whole reduction.
                let mut steps = vec![ProofStep::UnfoldFunction(refutation.application.clone())];
                steps.extend(unfolds.iter().cloned().map(ProofStep::UnfoldFunction));
                steps.push(ProofStep::CompatibilityNormalize(Some(taken.to_vec())));
                let checked = search_input
                    .driver()
                    .apply_step(have(refutation.differs.clone(), steps))
                    .and_then(|next| {
                        next.driver()
                            .apply_step(ProofStep::Contradiction(refutation.fact.clone()))
                    });
                Ok(attempt::candidate_outcome(checked)?.filter(Proof::focused_discharged))
            }
            DefinitionPlan::Split {
                condition,
                then_plan,
                else_plan,
            } => {
                let Ok((split_proof, split, ids)) =
                    search_input.split_focused_if(condition.clone())
                else {
                    return Ok(None);
                };
                let marker = split_proof.checkpoint();
                let mut then_taken = taken.to_vec();
                then_taken.push(condition.clone());
                let Ok(then_branch) = split_proof.focus_branch(ids[0]) else {
                    return Ok(None);
                };
                let Some(then_done) = crate::kernel::search::ProofSearch::refute_definition_ends(
                    &(then_branch),
                    then_plan,
                    refutation,
                    &then_taken,
                )?
                else {
                    return Ok(None);
                };
                let mut else_taken = taken.to_vec();
                else_taken.push(ClickProposition::Not(Box::new(condition.clone())));
                let Ok(else_branch) = then_done.focus_branch(ids[1]) else {
                    return Ok(None);
                };
                let Some(else_done) = crate::kernel::search::ProofSearch::refute_definition_ends(
                    &(else_branch),
                    else_plan,
                    refutation,
                    &else_taken,
                )?
                else {
                    return Ok(None);
                };
                Ok(else_done
                    .join_focused_if(&marker, split, ids, condition.clone())
                    .ok())
            }
        }
    }

    /// A bounded depth-first search over rewrite sequences: every applicable
    /// equality in either direction, each used at most once, closing after
    /// every step by `known`, `normalize` or the direct logical closer.
    /// An orientation whose left side does not occur in the goal costs no
    /// checked step. A goal already reached with at least as many rewrites
    /// left is not explored again, and the whole search tries at most
    /// `REWRITE_ATTEMPTS` rewrites.
    pub(super) fn rewrite_search(
        search_input: &Proof<'a>,
        candidates: &[Vec<(Proposition, ClickProposition)>],
        used: &mut Vec<bool>,
        depth: usize,
        seen: &mut std::collections::BTreeMap<RewriteGoalKey, usize>,
        budget: &mut RewriteBudget,
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("rewrite_search");
        let Some(current) = search_input.goal() else {
            return Ok(None);
        };
        for (index, forms) in candidates.iter().enumerate() {
            if used[index] {
                continue;
            }
            for (kernel, surface) in forms {
                check_verification_deadline()?;
                if !crate::kernel::proof::equality_rewrite::equality_rewrite_applies(
                    current, kernel,
                ) {
                    continue;
                }
                if budget.attempts == 0 {
                    return Ok(None);
                }
                budget.attempts -= 1;
                let Ok(rewritten) = search_input
                    .driver()
                    .apply_step(ProofStep::Rewrite(surface.clone()))
                else {
                    continue;
                };
                let Some(goal) = rewritten.goal().cloned() else {
                    continue;
                };
                let left = depth - 1;
                let goal = RewriteGoalKey::new(&goal);
                match seen.get(&goal) {
                    Some(&reached) if reached >= left => continue,
                    Some(_) => {}
                    None => {
                        if let Some(closed) =
                            crate::kernel::search::ProofSearch::try_close_after_rewrite(
                                &(rewritten),
                                budget,
                                closers,
                            )?
                        {
                            return Ok(Some(closed));
                        }
                    }
                }
                seen.insert(goal, left);
                if depth > 1 {
                    used[index] = true;
                    let found = crate::kernel::search::ProofSearch::rewrite_search(
                        &(rewritten),
                        candidates,
                        used,
                        depth - 1,
                        seen,
                        budget,
                        closers,
                    )?;
                    used[index] = false;
                    if found.is_some() {
                        return Ok(found);
                    }
                }
            }
        }
        Ok(None)
    }

    pub(super) fn try_close_after_rewrite(
        search_input: &Proof<'a>,
        budget: &mut RewriteBudget,
        closers: RewriteClosers<'_>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_close_after_rewrite");
        // Inside a `have`, the stated fact is the focused goal; the proof
        // around it is not complete yet.
        let closes = |proof: &Proof<'a>| proof.focused_discharged() || proof.is_complete();
        if let RewriteClosers::ExactListed(premise_pairs) = closers {
            let Some(goal) = search_input.goal() else {
                return Ok(None);
            };
            let mirrored = crate::kernel::mirrored_equality(goal);
            return Ok((crate::surface::planning::solve::computes_with_known(goal)
                || premise_pairs
                    .iter()
                    .any(|(premise, _)| premise == goal || Some(premise) == mirrored.as_ref()))
            .then(|| search_input.driver().apply_step(ProofStep::Known).ok())
            .flatten()
            .filter(closes));
        }
        if let RewriteClosers::Listed(premise_pairs) = closers {
            if let Ok(closed) =
                crate::kernel::search::ProofSearch::apply_normalization_closure(search_input, None)
                && closes(&closed)
            {
                return Ok(Some(closed));
            }
            return Ok(
                crate::kernel::search::ProofSearch::try_typed_atomic_solve_from_selected_premises(
                    search_input,
                    premise_pairs,
                )
                .filter(closes),
            );
        }
        if let RewriteClosers::GoalLocal {
            allow_function_unfold,
        } = closers
        {
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::try_typed_atomic_solve_closure(
                            search_input,
                        )
                    })
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::apply_normalization_closure(
                            search_input,
                            None,
                        )
                        .ok()
                        .filter(closes)
                    })
            {
                return Ok(Some(closed));
            }
            if !allow_function_unfold || budget.solve_closures == 0 {
                return Ok(None);
            }
            budget.solve_closures -= 1;
            return crate::kernel::search::ProofSearch::try_function_unfold_solve_closure(
                search_input,
                &[],
            );
        }
        if let RewriteClosers::Selected = closers {
            let closed =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::try_typed_atomic_solve_closure(
                            search_input,
                        )
                    })
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::apply_normalization_closure(
                            search_input,
                            None,
                        )
                        .ok()
                        .filter(closes)
                    });
            return Ok(closed.filter(closes));
        }
        if let Ok(closed) = search_input.driver().apply_step(ProofStep::Known)
            && closes(&closed)
        {
            return Ok(Some(closed));
        }
        if let Ok(closed) =
            crate::kernel::search::ProofSearch::apply_normalization_closure(search_input, None)
            && closes(&closed)
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)
                .ok()
                .flatten()
        {
            return Ok(Some(closed));
        }
        if budget.solve_closures == 0 {
            return Ok(None);
        }
        budget.solve_closures -= 1;
        Ok(crate::kernel::search::ProofSearch::try_solve_closure(search_input)?.filter(closes))
    }

    /// Prove the arithmetic subgoal `fact` where the proof stands, by
    /// arithmetic alone.
    pub(in crate::surface::proof) fn prove_stated_fact(
        search_input: &Proof<'a>,
        fact: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prove_stated_fact");
        let Ok(scope) = search_input.driver().open_have(fact.clone()) else {
            return Ok(None);
        };
        let Some(closed) = (scope).driver().try_arithmetic_fact_closure()? else {
            return Ok(None);
        };
        Ok(closed.join().ok())
    }

    /// Close `defined(a + b)` or `defined(a - b)` over `int32` or `int64`:
    /// prove both `Integer` bounds of the exact result by arithmetic.
    /// Together they are the definedness fact, which they file as a fact.
    pub(in crate::surface::proof) fn try_definedness_by_bounds(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_definedness_by_bounds");
        let Some(ClickProposition::Defined { expression }) = search_input.surface_goal() else {
            return Ok(None);
        };
        let (left, right, subtract) = match expression {
            ContractExpression::Add(left, right) => (left, right, false),
            ContractExpression::Subtract(left, right) => (left, right, true),
            _ => return Ok(None),
        };
        let exact = if subtract {
            ContractExpression::Subtract(Box::new(to_integer(left)), Box::new(to_integer(right)))
        } else {
            ContractExpression::Add(Box::new(to_integer(left)), Box::new(to_integer(right)))
        };
        // An operand that is itself an operation must be defined too; prove
        // that first so the goal is complete once the outer one is.
        let mut base = search_input.clone();
        for operand in [left.as_ref(), right.as_ref()] {
            if matches!(
                operand,
                ContractExpression::Add(..) | ContractExpression::Subtract(..)
            ) {
                let defined = ClickProposition::Defined {
                    expression: operand.clone(),
                };
                if let Some(next) =
                    crate::kernel::search::ProofSearch::prove_stated_fact(&(base), &defined)?
                {
                    base = next;
                }
            } else {
                let defined = ClickProposition::Defined {
                    expression: operand.clone(),
                };
                let kernel =
                    base.lower_cited_surface_proposition(&defined, "signed read domain")?;
                if matches!(kernel, Proposition::MemoryReadDefined { .. }) {
                    let scope = base.driver().open_have(defined)?;
                    let closed = scope.driver().apply_step(ProofStep::Known).or_else(|_| {
                        scope
                            .driver()
                            .apply_step(ProofStep::CompatibilityNormalize(None))
                    })?;
                    base = closed.join()?;
                }
            }
        }
        // The formats a definedness fact can be stated at, each by its
        // range (`machine_integer::definedness`).
        for ty in crate::kernel::machine_integer::definedness::defined_formats() {
            let (minimum, maximum) = crate::kernel::machine_integer::range::range(ty);
            let lower = ClickProposition::Comparison {
                left: exact.clone(),
                operator: ComparisonOperator::GreaterEqual,
                right: ContractExpression::IntegerLiteral(minimum.to_string()),
            };
            let upper = relate(
                exact.clone(),
                ContractExpression::IntegerLiteral(maximum.to_string()),
                Relation::LessEqual,
            );
            let Some(bounded) =
                crate::kernel::search::ProofSearch::prove_stated_fact(&(base), &lower)?
            else {
                continue;
            };
            let Some(bounded) =
                crate::kernel::search::ProofSearch::prove_stated_fact(&(bounded), &upper)?
            else {
                continue;
            };
            // The goal may also ask that each operand is defined, which
            // the facts already say.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(bounded))
                    .ok()
                    .flatten()
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Close a machine order goal `a < b` or `a <= b` by proving its
    /// `Integer` reading, the native comparison itself, with selected-premise
    /// arithmetic. Any miss leaves the proof unchanged.
    pub(in crate::surface::proof) fn try_machine_goal_through_integer(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_machine_goal_through_integer");
        crate::kernel::search::ProofSearch::try_machine_goal_through_integer_for(
            search_input,
            false,
        )
    }

    /// `try_machine_goal_through_integer` for a 64-bit equality goal. Its
    /// `Integer` reading is proved before the type is known, so it costs
    /// more than the other machine goals; `solve` tries it last, after
    /// `solve` and its rewrite search.
    pub(in crate::surface::proof) fn try_wide_equality_through_integer(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_wide_equality_through_integer");
        crate::kernel::search::ProofSearch::try_machine_goal_through_integer_for(search_input, true)
    }

    pub(in crate::surface::proof) fn try_machine_goal_through_integer_for(
        search_input: &Proof<'a>,
        wide_equality: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_machine_goal_through_integer_for");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        if !matches!(goal, Proposition::ConditionIs(_, true)) {
            return Ok(None);
        }
        let Some(order) = MachineOrder::of(goal) else {
            return Ok(None);
        };
        if (order == MachineOrder::Equal64) != wide_equality {
            return Ok(None);
        }
        let Some((lower, upper, relation, true)) = relation_parts(surface_goal) else {
            return Ok(None);
        };
        let _arithmetic_scope = is_word32_equality(goal).then(MachineEqualityBridgeScope::enter);
        // A machine comparison is the Integer comparison of its operands'
        // exact observations, so its Integer reading is the goal itself:
        // state each sum or difference defined, as `to_integer` of it needs,
        // and close the goal by `Integer` arithmetic with operation identities.
        let _ = order;
        let mut base = search_input.clone();
        let mut stated = false;
        for side in [&lower, &upper] {
            if matches!(
                side,
                ContractExpression::Add(..) | ContractExpression::Subtract(..)
            ) {
                let defined = ClickProposition::Defined {
                    expression: side.clone(),
                };
                if let Some(next) =
                    crate::kernel::search::ProofSearch::prove_stated_fact(&(base), &defined)?
                {
                    base = next;
                    stated = true;
                }
            }
        }
        // Without a stated definedness fact this is the selected-premise arithmetic `solve`
        // already ran on the goal. Plain 32-bit equality, with no sum or
        // difference to observe, already has the indexed native-reading
        // arithmetic route; re-entering it by bounds repeats equality-by-bounds
        // and state search for the same comparison.
        if !stated && !wide_equality {
            return Ok(None);
        }
        // Simplex refutes bounds; an equality is proved from its two.
        if relation == Relation::Equal {
            return crate::kernel::search::ProofSearch::try_equality_by_bounds(&(base));
        }
        crate::kernel::search::ProofSearch::selected_arithmetic(&(base), true, &[])
    }

    /// The sums and differences named by connected complete arithmetic domains.
    pub(in crate::surface::proof) fn defined_operations(
        search_input: &Proof<'a>,
        candidates: &[Proposition],
    ) -> Vec<ContractExpression> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("defined_operations");
        fn operation(surface: ClickProposition) -> Option<ContractExpression> {
            match surface {
                ClickProposition::Defined { expression } => match expression {
                    ContractExpression::Add(..) | ContractExpression::Subtract(..) => {
                        Some(expression)
                    }
                    _ => None,
                },
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    let anchor = |expression| {
                        Box::new(ContractExpression::At {
                            selector: selector.clone(),
                            expression,
                        })
                    };
                    match operation(*proposition)? {
                        ContractExpression::Add(a, b) => {
                            Some(ContractExpression::Add(anchor(a), anchor(b)))
                        }
                        ContractExpression::Subtract(a, b) => {
                            Some(ContractExpression::Subtract(anchor(a), anchor(b)))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        let mut operations = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for candidate in candidates {
            // Select the operation structurally from either ordinary bound.
            // The private query supplies its format and operands, not evidence.
            // Naming uses the same indexed states as structural goal raising;
            // it does not require a recorded `defined(...)` source. The actual
            // observation theorem still proves the complete ordinary domain.
            let query = crate::kernel::machine_integer::definedness::definedness_of_integer_bound(
                candidate,
            )
            .unwrap_or_else(|| candidate.clone());
            if !matches!(
                &query, condition_source_0 @ Proposition::ConditionIs(
                    _,
                    false
                ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32 | MachineIntegerType::Int64,
                        op: OverflowOperation::Add | OverflowOperation::Subtract,
                        ..
                    }, _))))
                || !seen.insert(query.clone())
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(surface) = search_input.structural_proposition_candidate(&query)
                && let Some(operation) = operation(surface)
            {
                operations.push(operation);
            }
        }
        operations
    }

    /// The `Integer` reading of each connected machine order fact, and the
    /// type range of each unsigned value they mention.
    pub(super) fn carried_machine_facts(
        search_input: &Proof<'a>,
        candidates: &[Proposition],
    ) -> Vec<Carried> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("carried_machine_facts");
        let mut carried = Vec::new();
        let mut ranged: Vec<ContractExpression> = Vec::new();
        for candidate in candidates {
            // A 64-bit equality is not carried: rewriting by it serves an
            // `Integer` claim without reading both types' ranges into every
            // arithmetic call.
            let Some(order) =
                MachineOrder::of(candidate).filter(|order| *order != MachineOrder::Equal64)
            else {
                continue;
            };
            crate::instrumentation::record_deterministic_work(1);
            let Some(spelled) = crate::kernel::search::ProofSearch::resolve_solve_premises(
                search_input,
                std::slice::from_ref(candidate),
                &[],
            ) else {
                continue;
            };
            let Some((_, surface)) = spelled.into_iter().next() else {
                continue;
            };
            let Some((lower, upper, relation, _)) = relation_parts(&surface) else {
                continue;
            };
            let lower = order.typed_literals(&lower);
            let upper = order.typed_literals(&upper);
            let observed = relate(to_integer(&lower), to_integer(&upper), relation);
            let carry = match relation {
                // A comparison of exact observations is the native
                // comparison itself, a fact already.
                Relation::Less | Relation::LessEqual => vec![ProofStep::Known],
                // Equal values have equal observations: rewriting by the
                // fact, stated the way round it is written, leaves an
                // identity.
                Relation::Equal => {
                    let stated = relate(lower.clone(), upper.clone(), relation);
                    vec![ProofStep::Rewrite(stated), ProofStep::Known]
                }
            };
            let steps = vec![have(observed.clone(), carry)];
            carried.push(Carried {
                establish: Establish::Steps(steps),
                surface: observed,
            });
            if let Some((minimum, maximum)) = order.range() {
                for value in [lower, upper] {
                    if matches!(to_integer(&value), ContractExpression::IntegerLiteral(_))
                        || ranged.contains(&value)
                    {
                        continue;
                    }
                    ranged.push(value.clone());
                    for bound in [
                        relate(
                            integer_literal(&minimum),
                            to_integer(&value),
                            Relation::LessEqual,
                        ),
                        relate(
                            to_integer(&value),
                            integer_literal(&maximum),
                            Relation::LessEqual,
                        ),
                    ] {
                        carried.push(Carried {
                            establish: Establish::Steps(vec![have(
                                bound.clone(),
                                vec![type_range(bound.clone())],
                            )]),
                            surface: bound,
                        });
                    }
                }
            }
        }
        carried
    }
}

#[cfg(test)]
mod logical_wrapper_search_tests {
    #[test]
    fn guarded_equalities_close_in_the_introduced_body() {
        crate::surface::verify_click_theorems(
            r#"
            theorem guarded_equality(x: Integer, y: Integer) {
                ensures x == y implies x + 1 == y + 1 by { close(); }
            }
            theorem quantified_guarded_equality(x: Integer, y: Integer) {
                ensures forall (k: Integer) { x == y implies x + k == y + k } by { close(); }
            }
        "#,
        )
        .expect("the introduced body retains equality search");
    }
}

#[cfg(test)]
mod retained_match_policy_tests {
    use super::*;
    #[test]
    fn match_equality_keeps_word_planner_policy_in_both_carriers() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(crate::kernel::KernelMatch::test_scrutinee(vec![])),
            arms: vec![crate::kernel::AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                bindings: vec![],
                binding_names: Default::default(),
                body: MachineTerm::constant(0),
            }],
        };
        let observed =
            crate::kernel::IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                native.clone(),
            ));
        let common = ConditionTerm::IntegerEqual(
            observed.into(),
            crate::kernel::IntegerTerm::constant_i64(1).into(),
        );
        let written = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(native),
            right: Box::new(MachineTerm::constant(1)),
        };
        for condition in [common, written] {
            assert!(is_word32_equality(&Proposition::condition_is(
                condition.clone(),
                true
            )));
            assert!(!is_word32_equality(&Proposition::condition_is(
                condition, false
            )));
        }
        assert!(!is_word32_equality(&Proposition::condition_is(
            ConditionTerm::IntegerEqual(
                crate::kernel::IntegerTerm::Variable(crate::kernel::Variable(991989)).into(),
                crate::kernel::IntegerTerm::constant_i64(1).into()
            ),
            true
        )));
    }
}
