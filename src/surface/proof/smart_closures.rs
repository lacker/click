//! Smart closure search and linear script interpretation.

use super::*;
use crate::kernel::{CFloatClassification, CFloatCondition};
use proof_object::{collect_surface_conjunct_leaves, frontier_premise_anchor};

fn kernel_upper_bound_split_candidate(
    proposition: &Proposition,
) -> Option<(Variable, Bitvector32Term)> {
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let (left, right, plus_one) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right, true),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => (left, right, false),
        _ => return None,
    };
    let Bitvector32Term::Variable(variable) = left.as_ref() else {
        return None;
    };
    if !plus_one {
        return Some((*variable, right.as_ref().clone()));
    }
    let Bitvector32Term::Add(pivot, one) = right.as_ref() else {
        return None;
    };
    (**one == Bitvector32Term::Constant(1)).then(|| (*variable, pivot.as_ref().clone()))
}

fn surface_upper_bound_split_condition(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_upper_bound_split_condition(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: right.clone(),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Add(pivot, one),
        } if **one == ContractExpression::CFragment(CExpression::Value(int32(1))) => {
            Some(ClickProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::LessThan,
                right: pivot.as_ref().clone(),
            })
        }
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Subtract(
                Box::new(right.clone()),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            ),
        }),
        _ => None,
    }
}

fn surface_upper_bound_direct_condition(
    proposition: &ClickProposition,
) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_upper_bound_direct_condition(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: right.clone(),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: right.clone(),
        }),
        _ => None,
    }
}

fn surface_split_equality(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_split_equality(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::Equal,
            right: right.clone(),
        }),
        _ => None,
    }
}

fn surface_split_nonstrict_bound(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_split_nonstrict_bound(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: right.clone(),
        }),
        _ => None,
    }
}

fn surface_split_disequality(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_split_disequality(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::NotEqual,
            right: right.clone(),
        }),
        _ => None,
    }
}

impl<'a> Proof<'a> {
    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// sole nonterminal move and strictly removes one outer goal connective.
    ///
    /// A miss is `Ok(None)` and leaves `self` the unchanged authority. An
    /// error is a tooling failure such as an exceeded deadline; it must abort
    /// the enclosing search rather than read as one more rejection.
    pub(in crate::surface::proof) fn try_direct_logical_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let mut budget = attempt::AttemptBudget::unbounded();
        let mut proof = self.clone();
        loop {
            if let Some(closed) = attempt::try_steps(
                &proof,
                &mut budget,
                [
                    ProofStep::Normalize,
                    ProofStep::Assumption,
                    ProofStep::Split,
                    ProofStep::Left,
                    ProofStep::Right,
                    ProofStep::Enumerate,
                ],
            )? {
                return Ok(Some(closed));
            }
            match attempt::candidate_outcome(proof.apply_step(ProofStep::Intro))? {
                Some(introduced) => proof = introduced,
                None => return Ok(None),
            }
        }
    }

    /// Searches the currently migrated `simp` vocabulary against this proof.
    ///
    /// Direct logical closers remain the cheap first choice. For a pure or
    /// fixed-state signed-order/equality derivation, the kernel-selected edge path
    /// is translated into a candidate made only of checked theorem
    /// applications, rewrites, and nested `have` scopes. The candidate
    /// advances this same `Proof`; no semantic result is produced before
    /// those proof steps have been accepted.
    pub(in crate::surface::proof) fn try_simp_closure(&self) -> Result<Option<Self>, ClickError> {
        if let Some(proof) = self.try_direct_logical_closure()? {
            return Ok(Some(proof));
        }
        self.try_simp_closure_after_direct(false)
    }

    /// Continues smart closure after direct logical candidates have either
    /// missed or been deliberately rejected as non-checkable. When
    /// `exclude_exact_goal` is true, the atomic derivation query may not cite
    /// the goal's own ambient fact; every selected theorem step is still
    /// checked against this unchanged Proof.
    pub(super) fn try_simp_closure_after_direct(
        &self,
        exclude_exact_goal: bool,
    ) -> Result<Option<Self>, ClickError> {
        self.try_simp_closure_after_direct_with_surfaces(exclude_exact_goal, &[])
    }

    pub(super) fn try_simp_closure_with_surfaces(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        if let Some(proof) = self.try_direct_logical_closure()? {
            return Ok(Some(proof));
        }
        self.try_simp_closure_after_direct_with_surfaces(false, introduced_surfaces)
    }

    fn try_simp_closure_after_direct_with_surfaces(
        &self,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        self.try_simp_closure_after_direct_with_surfaces_and_function_unfold(
            exclude_exact_goal,
            introduced_surfaces,
            true,
        )
    }

    fn try_simp_closure_after_direct_with_surfaces_and_function_unfold(
        &self,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
        allow_function_unfold: bool,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_selected_unchanged_load_forall_goal(surface_goal, &[])
        {
            return Ok(Some(proof));
        }
        let atomic = (|| {
            let (goal, derivation, premise_pairs, fixed_state_application_closes_goal) = self
                .selected_simp_derivation_with_surfaces(exclude_exact_goal, introduced_surfaces)?;
            self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                &premise_pairs,
                fixed_state_application_closes_goal,
            )
            .or_else(|| self.try_selected_equality_rewrite_chain(&premise_pairs))
            .or_else(|| self.try_selected_predecessor_upper_bound(&goal, &premise_pairs))
            .or_else(|| self.try_selected_constant_bound_weakening(&goal, &derivation))
            .or_else(|| {
                self.surface_goal().and_then(|surface_goal| {
                    self.try_selected_unchanged_load_forall_goal(surface_goal, &premise_pairs)
                        .or_else(|| {
                            self.try_selected_forall_goal(&goal, surface_goal, &premise_pairs)
                        })
                })
            })
            .or_else(|| self.try_selected_forall_instantiation(&goal, &premise_pairs))
            .or_else(|| self.try_selected_disjunction_cases(&premise_pairs))
        })();
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
        }
        let anchored_pairs = self
            .selected_simp_derivation_with_surfaces(exclude_exact_goal, introduced_surfaces)
            .map(|(_, _, pairs, _)| pairs)
            .unwrap_or_default();
        if let Some(anchored) = self
            .try_outcome_anchored_order_transitivity(&anchored_pairs)
            .or_else(|| self.try_outcome_anchored_increment_order(&anchored_pairs))
        {
            return Ok(Some(anchored));
        }
        if let Some(rewritten) = self.try_indexed_goal_equality_rewrite_closure_excluding(
            exclude_exact_goal,
            allow_function_unfold,
        ) {
            return Ok(Some(rewritten));
        }
        if allow_function_unfold
            && let Some(rewritten) =
                self.try_introduced_equality_then_function_unfold_closure(introduced_surfaces)?
        {
            return Ok(Some(rewritten));
        }
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_snapshot_transport_closure(surface_goal)?
        {
            return Ok(Some(proof));
        }
        if let Some(instantiated) =
            self.try_indexed_forall_instantiation_with_surfaces(introduced_surfaces)
        {
            return Ok(Some(instantiated));
        }
        // The atomic helpers still classify their internal candidate misses
        // as `Option`; surface a deadline that fired inside them here rather
        // than continuing into structural search with it exceeded.
        check_verification_deadline()?;
        let Some(surface_goal) = self.surface_goal().cloned() else {
            return Ok(None);
        };
        if let Some(enumerated) = self.try_finite_forall_enumeration(&surface_goal)? {
            return Ok(Some(enumerated));
        }
        if let Some(split) = self.try_upper_bound_split_closure(introduced_surfaces)? {
            return Ok(Some(split));
        }
        // Enter logical binders before looking for function applications.
        // An application below `forall (x)` cannot be checked until `intro`
        // has associated the surface name `x` with its fresh kernel variable.
        // The recursive structural call retains that checked `Intro` step and
        // then discovers applications in the now-focused body goal.
        if let Some(structural) =
            self.try_structural_simp_closure_with_surfaces(&surface_goal, introduced_surfaces)?
        {
            return Ok(Some(structural));
        }
        if allow_function_unfold
            && let Some(unfolded) = self.try_function_unfold_simp_closure(introduced_surfaces)?
        {
            return Ok(Some(unfolded));
        }
        Ok(None)
    }

    /// Uses one explicitly supplied equality before unfolding applications in
    /// the rewritten goal. Loop preservation supplies its entry invariants in
    /// this list: rewriting through that checked premise first changes a
    /// function-entry comparison into the smaller loop-entry frame that the
    /// defining equation can expose.
    fn try_introduced_equality_then_function_unfold_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        for surface in introduced_surfaces {
            for oriented in
                std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
            {
                let Some(rewritten) =
                    attempt::candidate_outcome(self.apply_step(ProofStep::Rewrite(oriented)))?
                else {
                    continue;
                };
                if let Some(closed) = rewritten.try_direct_logical_closure()? {
                    return Ok(Some(closed));
                }
                if let Some(closed) =
                    rewritten.try_function_unfold_simp_closure(introduced_surfaces)?
                {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Tries the finite set of function applications already present in the
    /// current surface goal. Each accepted candidate is a normal checked
    /// `unfold` step. The recursive simplification attempt disables further
    /// function unfolding, so recursive definitions cannot turn this smart
    /// tactic into unbounded evaluation.
    fn try_function_unfold_simp_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let Some(surface_goal) = self.surface_goal() else {
            return Ok(None);
        };
        let applications =
            pure_theorems::click_function_applications(surface_goal, introduced_surfaces);
        let mut proof = self.clone();
        for application in applications {
            let attempted = proof.apply_step(ProofStep::UnfoldFunction(application));
            let Some(unfolded) = attempt::candidate_outcome(attempted)? else {
                continue;
            };
            proof = unfolded;
            if let Some(closed) = proof.try_direct_logical_closure()? {
                return Ok(Some(closed));
            }
            if let Some(closed) = proof
                .try_simp_closure_after_direct_with_surfaces_and_function_unfold(
                    false,
                    introduced_surfaces,
                    false,
                )?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Splits one atomic goal at the final index licensed by an available
    /// upper bound. Selection happens over recorded Surface facts, and the
    /// result is an ordinary checked proof `if`: the then arm learns
    /// `variable < pivot`, while the else arm derives equality from the same
    /// bound and the exact negated branch fact through normal theorem search.
    ///
    /// Once either polarity of the proposed condition is available, the
    /// candidate is no longer a split. That structural fact is what makes
    /// recursive closure terminate inside both arms; no search-depth guard or
    /// hidden kernel recursion participates.
    fn try_upper_bound_split_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        if matches!(
            goal,
            Proposition::And(_, _)
                | Proposition::Or(_, _)
                | Proposition::Implies(_, _)
                | Proposition::ForAll { .. }
                | Proposition::Exists { .. }
        ) {
            return Ok(None);
        }
        let mut goal_variables = crate::kernel::proposition_variables(goal);
        if let Some(surface_goal) = self.surface_goal() {
            let mut surface_names = BTreeSet::new();
            collect_current_proposition_variables(surface_goal, &mut surface_names);
            for name in surface_names {
                let expression = ContractExpression::CFragment(CExpression::Variable(name));
                let probe = ClickProposition::Comparison {
                    left: expression.clone(),
                    operator: ComparisonOperator::Equal,
                    right: expression,
                };
                if let Ok(kernel) =
                    self.lower_surface_proposition(&probe, "upper-bound goal variable")
                {
                    goal_variables.extend(crate::kernel::proposition_variables(&kernel));
                }
            }
        }
        if goal_variables.is_empty() {
            return Ok(None);
        }

        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => {
                if let Some(data) = self.focused_outcome_data() {
                    (&data.surface_propositions, data.premise_anchor.as_ref())
                } else {
                    let Some(execution) = self.execution() else {
                        return Ok(None);
                    };
                    frontier_anchor = frontier_premise_anchor(execution);
                    (
                        &execution.presentation.surface_propositions,
                        frontier_anchor.as_ref(),
                    )
                }
            }
        };

        // An introduced implication guard is the nearest and smallest source
        // of the bound in the quantified-extension shape. Prefer those named
        // facts so ordinary closure does not clone and probe the ambient fact
        // set at every atomic leaf. Fall back to ambient facts only when no
        // introduced bound can concern this goal.
        let mut bound_sources = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let bound = self
                    .lower_surface_proposition(surface, "introduced upper bound")
                    .ok()?;
                let (variable, _) = kernel_upper_bound_split_candidate(&bound)?;
                goal_variables
                    .contains(&variable)
                    .then(|| (bound, Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        if bound_sources.is_empty() {
            bound_sources.extend(self.facts().to_vec().into_iter().filter_map(|bound| {
                let (variable, _) = kernel_upper_bound_split_candidate(&bound)?;
                goal_variables.contains(&variable).then_some((bound, None))
            }));
        }
        let candidates = bound_sources
            .into_iter()
            .filter_map(|(bound, introduced_surface)| {
                let (variable, pivot) = kernel_upper_bound_split_candidate(&bound)?;
                let pivot_probe = Proposition::Equal(
                    Term::Bitvector32(pivot.clone()),
                    Term::Bitvector32(pivot.clone()),
                );
                if crate::kernel::proposition_variables(&pivot_probe).contains(&variable) {
                    return None;
                }
                let bound_surface = introduced_surface.or_else(|| {
                    self.available_surface_fact(surface_facts, premise_anchor, &bound)
                })?;
                let split_kernel = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(Bitvector32Term::Variable(variable)),
                        Box::new(pivot),
                    ),
                    true,
                );
                let direct = surface_upper_bound_direct_condition(&bound_surface)?;
                let direct_surface = std::iter::once(direct.clone())
                    .chain(
                        self.premise_fixed_state_view()
                            .into_iter()
                            .flat_map(|view| {
                                view.recorded_snapshots.keys().rev().filter_map(|selector| {
                                    surface_at_snapshot(&direct, selector).ok()
                                })
                            }),
                    )
                    .find(|surface| {
                        self.lower_surface_proposition(surface, "upper-bound premise")
                            .is_ok_and(|lowered| lowered == bound)
                    })?;
                let mut surface_candidates = vec![
                    surface_upper_bound_split_condition(&bound_surface)?,
                    direct.clone(),
                ];
                if let Some(view) = self.premise_fixed_state_view() {
                    surface_candidates.extend(
                        view.recorded_snapshots
                            .keys()
                            .rev()
                            .filter_map(|selector| surface_at_snapshot(&direct, selector).ok()),
                    );
                }
                let split_surface = surface_candidates.into_iter().find(|surface| {
                    self.lower_surface_proposition(surface, "upper-bound split condition")
                        .is_ok_and(|lowered| lowered == split_kernel)
                })?;
                let split_negation = ClickProposition::Not(Box::new(split_surface.clone()));
                if introduced_surfaces
                    .iter()
                    .any(|surface| surface == &split_surface || surface == &split_negation)
                    || condition_polarity_forms(&split_kernel)
                        .iter()
                        .any(|form| self.facts().contains(form))
                {
                    return None;
                }
                Some((split_surface, direct_surface))
            })
            .collect::<Vec<_>>();
        for (condition, direct_bound) in candidates {
            let (split_proof, split, ids) = self.split_focused_if(condition.clone())?;
            let marker = split_proof.checkpoint();
            let mut then_surfaces = introduced_surfaces.to_vec();
            then_surfaces.push(condition.clone());
            let then_branch = split_proof.focus_branch(ids[0])?;
            let disequality = surface_split_disequality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let disequality_scope = then_branch.begin_have(disequality.clone())?;
            let disequality_done = disequality_scope
                .try_simp_closure_with_surfaces(&then_surfaces)?
                .or_else(|| {
                    let (left, right) = surface_strict_parts(&condition)?;
                    disequality_scope
                        .apply_step(ProofStep::ApplyTheoremUsing {
                            application: TheoremApplication {
                                name: "int32_lt_implies_neq".to_string(),
                                arguments: vec![left, right],
                            },
                            premises: vec![condition.clone()],
                        })
                        .ok()
                });
            let Some(disequality_done) = disequality_done else {
                continue;
            };
            let then_branch = disequality_done.join()?;
            then_surfaces.push(disequality);
            let Some(then_done) = then_branch.try_simp_closure_with_surfaces(&then_surfaces)?
            else {
                continue;
            };
            let negated = ClickProposition::Not(Box::new(condition.clone()));
            let mut else_surfaces = introduced_surfaces.to_vec();
            else_surfaces.push(negated.clone());
            let equality = surface_split_equality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let nonstrict = surface_split_nonstrict_bound(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let else_branch = then_done.focus_branch(ids[1])?;
            let equality_scope = else_branch.begin_have(equality.clone())?;
            let nonstrict_scope = equality_scope.begin_have(nonstrict.clone())?;
            let nonstrict_done = nonstrict_scope
                .try_simp_closure_with_surfaces(&else_surfaces)?
                .or_else(|| {
                    match nonstrict_scope.apply_step(ProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_lt_successor_implies_le".to_string(),
                            arguments: surface_nonstrict_parts(&nonstrict)
                                .map(|(left, right)| vec![left, right])?,
                        },
                        premises: vec![direct_bound.clone()],
                    }) {
                        Ok(proof) => Some(proof),
                        Err(_) => None,
                    }
                });
            let Some(nonstrict_done) = nonstrict_done else {
                continue;
            };
            let equality_scope = equality_scope.join_nested(nonstrict_done)?;
            else_surfaces.push(nonstrict);
            let Some(equality_done) =
                equality_scope.try_simp_closure_with_surfaces(&else_surfaces)?
            else {
                continue;
            };
            let else_branch = equality_done.join()?;
            else_surfaces.push(equality.clone());
            let rewritten_surface_goal =
                surface_strict_parts(&condition).and_then(|(left, right)| {
                    let ContractExpression::CFragment(CExpression::Variable(name)) = left else {
                        return None;
                    };
                    substitute_click_proposition(
                        else_branch.surface_goal()?,
                        &std::iter::once((name, right)).collect(),
                    )
                    .ok()
                });
            let transported_else = else_branch
                .surface_goal()
                .and_then(old_reflexive_transport_source)
                .and_then(|source| {
                    else_branch
                        .try_planned_execution_proposition_fact_transport(
                            &source,
                            else_branch.surface_goal()?,
                        )
                        .ok()
                        .flatten()
                })
                .filter(Proof::focused_discharged);
            let rewritten_else = match else_branch.apply_step(ProofStep::Rewrite(equality.clone()))
            {
                Ok(rewritten) if rewritten.focused_discharged() => Some(rewritten),
                Ok(rewritten) => {
                    let transported = rewritten_surface_goal
                        .as_ref()
                        .and_then(old_reflexive_transport_source)
                        .and_then(|source| {
                            rewritten
                                .try_planned_execution_proposition_fact_transport(
                                    &source,
                                    rewritten_surface_goal.as_ref()?,
                                )
                                .ok()
                                .flatten()
                        })
                        .filter(Proof::focused_discharged);
                    if transported.is_some() {
                        transported
                    } else {
                        rewritten.try_simp_closure_with_surfaces(&else_surfaces)?
                    }
                }
                Err(_) => None,
            };
            let else_done = if transported_else.is_some() {
                transported_else
            } else if rewritten_else.is_some() {
                rewritten_else
            } else {
                else_branch.try_simp_closure_with_surfaces(&else_surfaces)?
            };
            let Some(else_done) = else_done else {
                continue;
            };
            return else_done
                .join_focused_if(&marker, split, ids, condition)
                .map(Some);
        }
        Ok(None)
    }

    /// Proves a two-edge non-strict outcome bound at the return entry or its
    /// immediate predecessor. Outcome lowering deliberately keeps selected
    /// premises in their source form; anchoring those exact premises at
    /// the execution boundary lets the ordinary theorem checker connect a
    /// returned local to its result without consulting the retired planner.
    pub(super) fn try_outcome_anchored_order_transitivity(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let data = self.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let ordered = premise_pairs
                .iter()
                .filter_map(|(_, surface)| {
                    let anchored = surface_at_snapshot(surface, anchor).ok()?;
                    let parts = surface_nonstrict_parts(&anchored)?;
                    Some((anchored, parts))
                })
                .collect::<Vec<_>>();
            for (first_surface, (first, middle)) in &ordered {
                for (second_surface, (second_middle, last)) in &ordered {
                    if middle != second_middle {
                        continue;
                    }
                    let theorem = ProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_ge_transitive".to_string(),
                            arguments: vec![last.clone(), middle.clone(), first.clone()],
                        },
                        premises: vec![second_surface.clone(), first_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Proves an outcome increment bound at the return entry or its immediate
    /// predecessor. The latter is the assignment boundary that can connect a
    /// named return local to the increment expression. The two propositions
    /// come only from the atomic derivation's selected requirements; the
    /// ordinary theorem, nested-`have`, and assumption checkers decide whether
    /// either constant-size historical application establishes the current
    /// result-aware goal.
    pub(super) fn try_outcome_anchored_increment_order(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let data = self.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        let surface_goal = self.surface_goal()?.clone();
        if surface_nonstrict_parts(&surface_goal).is_none() {
            return None;
        }
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let mut lower_bounds = Vec::new();
            let mut upper_bounds = Vec::new();
            for (_, surface) in premise_pairs {
                let anchored = surface_at_snapshot(surface, anchor).ok()?;
                if let Some(parts) = surface_nonstrict_parts(&anchored) {
                    lower_bounds.push((anchored.clone(), parts));
                }
                if let Some(parts) = surface_strict_parts(&anchored) {
                    upper_bounds.push((anchored, parts));
                }
            }
            for (lower_surface, (surface_lower, lower_value)) in &lower_bounds {
                for (upper_surface, (upper_value, surface_upper)) in &upper_bounds {
                    if lower_value != upper_value {
                        continue;
                    }
                    let theorem = ProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_increment_preserves_order".to_string(),
                            arguments: vec![
                                lower_value.clone(),
                                surface_lower.clone(),
                                surface_upper.clone(),
                            ],
                        },
                        premises: vec![lower_surface.clone(), upper_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    let one = ContractExpression::CFragment(CExpression::Value(int32(1)));
                    let theorem_conclusion = ClickProposition::Comparison {
                        left: ContractExpression::Add(
                            Box::new(surface_lower.clone()),
                            Box::new(one.clone()),
                        ),
                        operator: ComparisonOperator::LessEqual,
                        right: ContractExpression::Add(
                            Box::new(lower_value.clone()),
                            Box::new(one),
                        ),
                    };
                    if let Some(closed) = applied
                        .apply_step(ProofStep::TransportUsing {
                            source: theorem_conclusion,
                            target: surface_goal.clone(),
                            premises: Vec::new(),
                        })
                        .ok()
                        .or_else(|| applied.try_direct_logical_closure().ok().flatten())
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Tries the focused branch goal itself as one explicit fact transport from a
    /// recorded program point. This also applies to proposition scopes opened
    /// mid-execution, such as loop-invariant initialization and preservation.
    /// The candidate space is the execution's
    /// recorded-snapshot index, not the ambient fact set; every accepted source
    /// and target is checked by `TransportUsing` on this immutable Proof.
    pub(super) fn try_snapshot_transport_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        // Outcome transport is a general closure. Extending it to fixed-state
        // and mid-execution proposition scopes is needed specifically for
        // opaque Click applications whose snapshot arguments cannot be
        // refreshed by ordinary field rewrites. Keep non-function goals on
        // their established, more local rewrite plans.
        if self.outcome_fixed_state_view().is_none() {
            let mut calls = BTreeSet::new();
            crate::surface::validation::collect_click_function_calls_in_proposition(
                surface_goal,
                &mut calls,
            );
            if calls.is_empty() {
                return Ok(None);
            }
        }
        let Some(view) = self.premise_fixed_state_view() else {
            return Ok(None);
        };
        if let Some(source) = old_reflexive_transport_source(surface_goal) {
            if self.execution_proposition_fixed_state_view().is_some()
                && let Some(proof) =
                    self.try_planned_execution_proposition_fact_transport(&source, surface_goal)?
                && proof.is_complete()
            {
                return Ok(Some(proof));
            }
            match self.search_fixed_state_fact_transport(&source, surface_goal, std::iter::empty())
            {
                Ok(proof) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        let entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let selectors = std::iter::once(SnapshotSelector::ProgramPoint(entry))
            .chain(view.recorded_snapshots.keys().rev().cloned());
        let mut tried = BTreeSet::new();
        for selector in selectors {
            if !tried.insert(selector.clone()) {
                continue;
            }
            let source = ClickProposition::At {
                selector,
                proposition: Box::new(surface_goal.clone()),
            };
            match self.search_fixed_state_fact_transport(
                &source,
                surface_goal,
                std::iter::once(source.clone()),
            ) {
                Ok(proof) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        Ok(None)
    }

    /// Refines the Proof-owned Surface goal through audited scopes and steps.
    /// The caller cannot supply a second description of the judgment: this
    /// syntax is the view paired with the kernel goal in `PropositionObligation`.
    fn try_structural_simp_closure_with_surfaces(
        &self,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        match (surface_goal, goal) {
            (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                if let Some(enumerated) = self.try_finite_forall_enumeration(surface_goal)? {
                    return Ok(Some(enumerated));
                }
                match attempt::candidate_outcome(self.apply_step(ProofStep::Intro))? {
                    Some(introduced) => {
                        introduced.try_simp_closure_with_surfaces(introduced_surfaces)
                    }
                    None => Ok(None),
                }
            }
            (ClickProposition::Implies(surface_antecedent, _), Proposition::Implies(_, _)) => {
                let Some(mut introduced) =
                    attempt::candidate_outcome(self.apply_step(ProofStep::Intro))?
                else {
                    return Ok(None);
                };
                // The introduced antecedent itself is the uniquely selected
                // contradiction candidate. This is a constant-size probe:
                // `Contradiction` checks that exact fact and its indexed
                // opposite, without scanning ambient path facts.
                if let Some(closed) = introduced
                    .try_introduced_antecedent_contradiction(surface_antecedent.as_ref())?
                {
                    return Ok(Some(closed));
                }
                let mut conjuncts = Vec::new();
                if matches!(surface_antecedent.as_ref(), ClickProposition::And(_, _)) {
                    collect_surface_conjunct_leaves(surface_antecedent, &mut conjuncts);
                }
                for conjunct in &conjuncts {
                    let Some(extracted) = attempt::candidate_outcome(
                        introduced.apply_step(ProofStep::Extract(conjunct.clone())),
                    )?
                    else {
                        return Ok(None);
                    };
                    introduced = extracted;
                    if introduced.is_complete() {
                        return Ok(Some(introduced));
                    }
                }
                let mut available_surfaces = introduced_surfaces.to_vec();
                available_surfaces.extend(conjuncts.iter().cloned());
                if !conjuncts.is_empty()
                    && let Some(surface_goal) = introduced.surface_goal()
                    && let Some(source) = old_reflexive_transport_source(surface_goal)
                {
                    match introduced.search_fixed_state_fact_transport(
                        &source,
                        surface_goal,
                        conjuncts.iter().cloned(),
                    ) {
                        Ok(transported) if transported.is_complete() => {
                            return Ok(Some(transported));
                        }
                        Ok(_) => {}
                        Err(_) => check_verification_deadline()?,
                    }
                }
                if let Some(split) =
                    introduced.try_upper_bound_split_closure(&available_surfaces)?
                {
                    return Ok(Some(split));
                }
                introduced.try_simp_closure_with_surfaces(&available_surfaces)
            }
            (ClickProposition::And(surface_left, surface_right), Proposition::And(_, _)) => {
                let Some(left) =
                    attempt::candidate_outcome(self.begin_have(surface_left.as_ref().clone()))?
                else {
                    return Ok(None);
                };
                let Some(left) = left.try_simp_closure_with_surfaces(introduced_surfaces)? else {
                    return Ok(None);
                };
                let Some(proof) = attempt::candidate_outcome(left.join())? else {
                    return Ok(None);
                };
                let Some(right) =
                    attempt::candidate_outcome(proof.begin_have(surface_right.as_ref().clone()))?
                else {
                    return Ok(None);
                };
                let Some(right) = right.try_simp_closure_with_surfaces(introduced_surfaces)? else {
                    return Ok(None);
                };
                let Some(joined) = attempt::candidate_outcome(right.join())? else {
                    return Ok(None);
                };
                attempt::candidate_outcome(joined.apply_step(ProofStep::Split))
            }
            // A predicate-call goal unfolds to its body, which the
            // structural arms and logical closers then work over. Repeat
            // unfolds are refused so recursive predicate bodies cannot loop
            // the search.
            (ClickProposition::PredicateCall { name, .. }, _)
                if !self.focused_branch_unfolds().contains(name) =>
            {
                match attempt::candidate_outcome(
                    self.apply_step(ProofStep::UnfoldPredicate(name.clone())),
                )? {
                    Some(unfolded) => unfolded.try_simp_closure_with_surfaces(introduced_surfaces),
                    None => Ok(None),
                }
            }
            (ClickProposition::Or(surface_left, surface_right), Proposition::Or(_, _)) => {
                for (surface, closer) in [
                    (surface_left.as_ref(), ProofStep::Left),
                    (surface_right.as_ref(), ProofStep::Right),
                ] {
                    let selected = (|| {
                        let Some(scope) =
                            attempt::candidate_outcome(self.begin_have(surface.clone()))?
                        else {
                            return Ok(None);
                        };
                        let Some(scope) =
                            scope.try_simp_closure_with_surfaces(introduced_surfaces)?
                        else {
                            return Ok(None);
                        };
                        let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                            return Ok(None);
                        };
                        attempt::candidate_outcome(joined.apply_step(closer.clone()))
                    })();
                    if let Some(selected) = selected? {
                        return Ok(Some(selected));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Proves the kernel's deterministic constant-bounded universal table as
    /// checked nested `have` scopes, then closes with the ordinary
    /// `Enumerate` rule. Candidate discovery is output-sensitive in the
    /// explicit instance table; each non-vacuous instance recursively uses
    /// the same retained Proof search and no ambient universal scan.
    pub(super) fn try_finite_forall_enumeration(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(mut instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Ok(None);
        };
        // Instances over two indices are proved nearest pair first: a chain
        // fact between neighbours is what a wider span's proof cites, and an
        // earlier `have` is an available fact for a later one.
        instances.sort_by_key(|(values, _)| match values.as_slice() {
            [first, second] => ((second - first).abs(), *first, *second),
            _ => (0, 0, 0),
        });
        // A goal stated as a predicate call binds through the predicate's
        // body; unfold it at the surface to name the binders.
        let predicate_environment = match self.context.as_ref() {
            ProofContext::Pure(context) => context.predicate_environment,
            ProofContext::FixedState(context) => context.predicate_environment,
            ProofContext::Execution(context) => context.predicate_environment,
        };
        let all_predicates = predicate_environment
            .definitions
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        let unfolded = unfold_click_predicates_in_proposition_with_active(
            predicate_environment,
            &all_predicates,
            surface_goal,
            &mut BTreeSet::new(),
        )
        .unwrap_or_else(|_| surface_goal.clone());
        let mut binder_names = Vec::new();
        let mut surface_body = &unfolded;
        while let ClickProposition::ForAll { name, body, .. } = surface_body {
            binder_names.push(name.clone());
            surface_body = body;
        }
        if binder_names.is_empty() {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (values, instance) in instances {
            check_verification_deadline()?;
            if values.len() != binder_names.len() {
                return Ok(None);
            }
            if matches!(normalize_proposition(&instance), SimpProposition::True) {
                continue;
            }
            let Some(value_expressions) = values
                .iter()
                .map(|value| {
                    u32::try_from(*value)
                        .ok()
                        .map(|bits| ContractExpression::CFragment(CExpression::Value(int32(bits))))
                })
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            let substitutions = binder_names
                .iter()
                .cloned()
                .zip(value_expressions)
                .collect::<BTreeMap<_, _>>();
            let Ok(surface_instance) = substitute_click_proposition(surface_body, &substitutions)
            else {
                return Ok(None);
            };
            // An instance whose guard is constant true is stated as its
            // conclusion: that is the fact a later instance's proof cites, and
            // `enumerate()` reads the table through the same normalization.
            let surface_instance = match (&instance, &surface_instance) {
                (Proposition::Implies(guard, _), ClickProposition::Implies(_, conclusion))
                    if matches!(normalize_proposition(guard), SimpProposition::True) =>
                {
                    conclusion.as_ref().clone()
                }
                _ => surface_instance,
            };
            let Some(scope) = attempt::candidate_outcome(proof.begin_have(surface_instance))?
            else {
                return Ok(None);
            };
            let Some(scope) = scope.try_simp_closure()? else {
                return Ok(None);
            };
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.apply_step(ProofStep::Enumerate))
    }

    /// Closes from the just-introduced antecedent and one exact indexed
    /// opposite. The antecedent fixes the kernel pair; Surface lookup visits
    /// only forms recorded for those two facts, never the ambient set.
    pub(super) fn try_introduced_antecedent_contradiction(
        &self,
        surface_antecedent: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(introduced) = self.checked_facts().first() else {
            return Ok(None);
        };
        let opposite = match introduced {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        if !self.facts().contains(&opposite) {
            return Ok(None);
        }
        if let Some(closed) = attempt::candidate_outcome(
            self.apply_step(ProofStep::Contradiction(surface_antecedent.clone())),
        )? {
            return Ok(Some(closed));
        }
        let surfaces = match self.context.as_ref() {
            ProofContext::Pure(context) => context
                .theorem_context
                .surface_requirements
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::FixedState(context) => context
                .surface_propositions
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Execution(_) => self
                .outcome_fixed_state_view()
                .into_iter()
                .flat_map(|view| view.surface_propositions.surfaces(&opposite))
                .cloned()
                .collect::<Vec<_>>(),
        };
        for surface in surfaces {
            if let Some(closed) =
                attempt::candidate_outcome(self.apply_step(ProofStep::Contradiction(surface)))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Retains the kernel decision and every exact checkable surface form
    /// among its context premises. A typed evidence translator selects and
    /// requires its own exact premises from this subset; unrelated transitive
    /// search context need not be Surface-synthesizable. This is a read-only smart
    /// query: only the later `apply_step` calls may advance the proof.
    pub(super) fn selected_simp_derivation(
        &self,
        exclude_exact_goal: bool,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
    )> {
        self.selected_simp_derivation_with_surfaces(exclude_exact_goal, &[])
    }

    fn selected_simp_derivation_with_surfaces(
        &self,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
    )> {
        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, theorem_application_closes_goal, premise_anchor) =
            match self.context.as_ref() {
                ProofContext::Pure(context) => {
                    (&context.theorem_context.surface_requirements, true, None)
                }
                ProofContext::FixedState(context) => (
                    context.surface_propositions,
                    true,
                    context.premise_anchor.as_ref(),
                ),
                // A judgment stated at a function outcome supplies the
                // outcome's recorded lowerings and statement-entry anchor.
                ProofContext::Execution(_) => {
                    if let Some(data) = self.focused_outcome_data() {
                        (
                            &data.surface_propositions,
                            // Entry-anchored premises can add a check-equivalent
                            // outcome fact without discharging the exact goal
                            // form. Keep the ordinary trailing assumption so
                            // the checked successor decides whether it is needed.
                            false,
                            data.premise_anchor.as_ref(),
                        )
                    } else {
                        // A judgment stated mid-execution (a `have` before
                        // function exit) supplies the frontier's recorded
                        // lowerings and the entry of the last executed
                        // statement, exactly as an outcome data does.
                        let execution = self.execution()?;
                        frontier_anchor = frontier_premise_anchor(execution);
                        (
                            &execution.presentation.surface_propositions,
                            false,
                            frontier_anchor.as_ref(),
                        )
                    }
                }
            };
        let goal = self.goal()?.clone();
        let derivation = if exclude_exact_goal {
            self.facts()
                .assumptions()
                .derive_simp_proposition_without_exact_goal(&goal)?
        } else {
            let plan = plan_simp_certificate(&goal, self.facts().assumptions())?;
            let SimpEvidence::Derivation(derivation) = plan else {
                return None;
            };
            derivation
        };
        let context_premises = derivation.context_premises();
        let resolve_premise = |premise: &Proposition, anchor: Option<&ProgramPointRef>| {
            if let Some(surface) = self.available_surface_fact(surface_facts, anchor, premise) {
                return Some((premise.clone(), surface));
            }
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                self.lower_surface_proposition(surface, "introduced simp premise")
                    .is_ok_and(|lowered| {
                        lowered == *premise || condition_polarity_equivalent(&lowered, premise)
                    })
            }) {
                return Some((premise.clone(), surface.clone()));
            }
            condition_polarity_forms(premise)
                .into_iter()
                .find_map(|form| {
                    let surface = self.available_surface_fact(surface_facts, anchor, &form);
                    surface.map(|surface| (form, surface))
                })
        };
        let mut premise_pairs = context_premises
            .iter()
            .filter_map(|premise| resolve_premise(premise, premise_anchor))
            .collect::<Vec<_>>();
        // A structured branch continuation can clear `last_step_entry`, or a
        // later common statement can move it past the point where the
        // selected premises were established. If the initially resolved
        // subset already carries one common explicit `at(...)` form,
        // retry this same finite premise list at that successor. No ambient fact
        // or program-point scan participates.
        let anchors = premise_pairs
            .iter()
            .filter_map(|(_, surface)| match surface_snapshot_selector(surface) {
                Some(SnapshotSelector::ProgramPoint(point)) => Some(point),
                Some(SnapshotSelector::Mark(_)) | None => None,
            })
            .collect::<BTreeSet<_>>();
        if anchors.len() == 1 {
            let inferred = anchors.first().expect("one inferred anchor");
            let anchored_pairs = context_premises
                .iter()
                .filter_map(|premise| resolve_premise(premise, Some(inferred)))
                .collect::<Vec<_>>();
            if anchored_pairs.len() >= premise_pairs.len() {
                premise_pairs = anchored_pairs;
            }
        }
        Some((
            goal,
            derivation,
            premise_pairs,
            theorem_application_closes_goal,
        ))
    }

    /// Resolves one exact retained fact to a surface form that will lower
    /// back to that same kernel proposition when the selected proof step is
    /// checked. Historical locals are anchored before ordinary forms are
    /// considered, so a same-written newer snapshot cannot be substituted.
    /// The fixed-state view against which a premise lookup is spelled: the
    /// focused branch's outcome data, or the frontier's current state for a
    /// judgment stated mid-execution.
    fn premise_fixed_state_view(&self) -> Option<FixedStateOperationView<'_>> {
        self.outcome_fixed_state_view()
            .or_else(|| self.execution_proposition_fixed_state_view())
    }

    pub(super) fn available_surface_fact(
        &self,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let matches_kernel = |candidate: &ClickProposition| {
            if self.focused_outcome_data().is_some()
                && surface_facts
                    .available_kernel_matching(candidate, |fact| self.facts().contains(fact))
                    .is_some_and(|lowered| {
                        lowered == kernel || condition_polarity_equivalent(lowered, kernel)
                    })
            {
                return Some(());
            }
            let lowered = self
                .lower_surface_proposition_direct(candidate, "typed simp premise form")
                .ok()?;
            (lowered == *kernel
                || condition_polarity_equivalent(&lowered, kernel)
                || quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                    .is_some())
            .then_some(())
        };
        if let Some(surface) = surface_facts.surfaces(kernel).find(|surface| {
            (proposition_contains_at_expression(surface)
                || proposition_contains_old_expression(surface))
                && matches_kernel(surface).is_some()
        }) {
            return Some(surface.clone());
        }
        // Function requirements retain their original unanchored Surface
        // form while their kernel fact is entry-relative. Probe that one
        // canonical source form before the moving statement-entry anchor;
        // the direct lowering check below rejects non-entry facts, and the
        // lookup visits only forms indexed under this selected premise.
        let function_entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let requirement_surface = if let Some(data) = self.focused_outcome_data() {
            data.requirement_surfaces.get(kernel).cloned()
        } else {
            // A judgment stated mid-execution selects its requirement
            // spellings from the frontier's own contract, as an outcome
            // outcome does from its recorded ones.
            self.execution_proposition_fixed_state_view()
                .and_then(|view| {
                    view.requirement_facts
                        .iter()
                        .zip(view.original_requirements)
                        .find(|(fact, _)| *fact == kernel)
                        .and_then(|(_, requirement)| requirement.proposition().cloned())
                })
        };
        if let Some(surface) = requirement_surface {
            let anchored = ClickProposition::At {
                selector: SnapshotSelector::ProgramPoint(function_entry.clone()),
                proposition: Box::new(surface.clone()),
            };
            if matches_kernel(&anchored).is_some() {
                return Some(anchored);
            }
            if let Ok(anchored) = surface_at_snapshot(&surface, &function_entry)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if self.premise_fixed_state_view().is_some() {
            if let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_snapshot(surface, &function_entry).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            }) {
                return Some(anchored);
            }
            if let Some(view) = self.premise_fixed_state_view()
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                )
                && let Ok(anchored) = surface_at_snapshot(&surface, &function_entry)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(anchor) = premise_anchor
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_snapshot(surface, anchor).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            })
        {
            return Some(anchored);
        }
        // Before accepting an unanchored recorded form, which may have been
        // stated at an earlier value of a variable that later changed,
        // spell the fact against the recorded snapshot where it was read.
        if let Some(anchor) = premise_anchor
            && let Some((parameters, arguments, recorded_snapshots)) = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => Some((
                    context.parameters,
                    context.arguments,
                    context.recorded_snapshots,
                )),
                ProofContext::Execution(_) => self
                    .premise_fixed_state_view()
                    .map(|view| (view.parameters, view.arguments, view.recorded_snapshots)),
            }
            && let Some(anchored) = synthesize_surface_at_recorded_snapshots(
                kernel,
                parameters,
                arguments,
                recorded_snapshots,
                anchor,
            )
            .into_iter()
            .find(|surface| matches_kernel(surface).is_some())
        {
            return Some(anchored);
        }
        // A checked branch interface can export a kernel fact whose arm-local
        // Surface recording does not survive as a common map entry. The
        // statement-entry anchor still names the exact retained state. Rebuild
        // only this selected fact at that indexed state, anchor it, and require
        // the ordinary direct lowering to recover the same kernel premise.
        if let Some(anchor) = premise_anchor {
            let synthesis_context = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => Some((
                    context.parameters,
                    context.arguments,
                    context.recorded_snapshots,
                )),
                ProofContext::Execution(_) => self
                    .premise_fixed_state_view()
                    .map(|view| (view.parameters, view.arguments, view.recorded_snapshots)),
            };
            if let Some((parameters, arguments, recorded_snapshots)) = synthesis_context
                && let Some(state) = recorded_snapshots.get(anchor)
                && let Some(surface) =
                    synthesize_surface_proposition(kernel, parameters, arguments, state)
                && let Ok(anchored) = surface_at_snapshot(&surface, anchor)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(surface) = surface_facts
            .surfaces(kernel)
            .find(|surface| matches_kernel(surface).is_some())
            .cloned()
        {
            return Some(surface);
        }
        // Quantified execution facts may be retained in the canonical memory
        // form used by the kernel while their recorded Surface form lowers to
        // a term carrying a check-equivalent memory snapshot. Probe only the
        // persistent alpha/canonical-form bucket for this selected premise;
        // `InstantiateUsing` validates the same equivalence on check.
        if matches!(kernel, Proposition::ForAll { .. }) {
            for candidate in self.facts().matching_quantified_facts(kernel) {
                for surface in surface_facts.surfaces(&candidate) {
                    let lowered = self
                        .lower_surface_proposition_direct(
                            surface,
                            "typed quantified simp premise form",
                        )
                        .ok()?;
                    if quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                        .is_some()
                    {
                        return Some(surface.clone());
                    }
                }
            }
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::FixedState(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let click_function_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.click_function_environment,
                ProofContext::FixedState(context) => context.click_function_environment,
                ProofContext::Execution(context) => context.click_function_environment,
            };
            for name in self.focused_branch_unfolds().iter() {
                for opaque in surface_facts.kernels_written_by_predicate(name) {
                    for opaque_surface in surface_facts.surfaces(opaque) {
                        let ClickProposition::PredicateCall {
                            name: surface_name,
                            arguments,
                        } = opaque_surface
                        else {
                            continue;
                        };
                        let Some(definition) = predicate_environment.get(surface_name) else {
                            continue;
                        };
                        let Ok(body_surface) =
                            instantiate_click_predicate_definition(definition, arguments)
                        else {
                            continue;
                        };
                        let unfolds_to_selected = unfold_predicates_in_proposition(
                            predicate_environment,
                            click_function_environment,
                            std::slice::from_ref(name),
                            opaque,
                            self.facts().assumptions(),
                        )
                        .is_ok_and(|unfolded| {
                            unfolded == *kernel
                                || quantified_equivalent_available_fact(
                                    kernel,
                                    std::slice::from_ref(&unfolded),
                                )
                                .is_some()
                        });
                        if unfolds_to_selected {
                            if matches_kernel(&body_surface).is_some() {
                                return Some(body_surface);
                            }
                            if let Some(view) = self.premise_fixed_state_view()
                                && let Some(anchored) = view
                                    .recorded_snapshots
                                    .keys()
                                    .rev()
                                    .filter_map(|selector| {
                                        surface_at_snapshot(&body_surface, selector).ok()
                                    })
                                    .find(|surface| matches_kernel(surface).is_some())
                            {
                                return Some(anchored);
                            }
                        }
                    }
                }
            }
        }
        // Branch-condition facts are checked execution outputs, but their
        // arm-local Surface map entry need not survive at the shared outcome.
        // Reconstruct only this derivation-selected premise at the current
        // symbolic state and accept it only when ordinary lowering recovers
        // the exact kernel fact. This is constant work per typed proof edge,
        // not an ambient form search.
        let synthesis_context = match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => Some((
                context.parameters,
                context.arguments,
                context.state,
                context.recorded_snapshots,
            )),
            ProofContext::Execution(_) => self.premise_fixed_state_view().map(|view| {
                (
                    view.parameters,
                    view.arguments,
                    view.state,
                    view.recorded_snapshots,
                )
            }),
        };
        let (parameters, arguments, state, recorded_snapshots) = synthesis_context?;
        let bound_variable_names = self
            .proposition_obligation()
            .into_iter()
            .flat_map(|goal| goal.surface_bindings.iter())
            .filter_map(|(name, binding)| match binding {
                ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(variable),
                ))) => Some((*variable, name.clone())),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        if let Some(surface) = synthesize_surface_proposition_with_bound_variable_names(
            kernel,
            parameters,
            arguments,
            state,
            &bound_variable_names,
        ) && matches_kernel(&surface).is_some()
        {
            return Some(surface);
        }
        // A certified statement fact may relate two execution snapshots (a
        // callee postcondition names a cell after the call and its value
        // before it), so no single snapshot denotes both operands. Spell each
        // operand at the nearest recorded statement entry that denotes it,
        // walking back from the selected premise anchor; the candidate is
        // accepted only when ordinary lowering recovers this exact fact.
        synthesize_surface_at_recorded_snapshots(
            kernel,
            parameters,
            arguments,
            recorded_snapshots,
            premise_anchor?,
        )
        .into_iter()
        .find(|surface| matches_kernel(surface).is_some())
    }

    /// Tries equalities attached to terms occurring in the current goal.
    /// This complements the kernel derivation path for arithmetic goals whose
    /// normal form is exposed only after selected historical equalities are
    /// rewritten. Candidate lookup is goal-local and persistently indexed.
    /// Atomic goals may retain a same-width renaming, but each selected
    /// equality is used at most once; structural goals keep only a closing
    /// rewrite so their recursive connective proof remains visible.
    #[cfg(test)]
    pub(super) fn try_indexed_goal_equality_rewrite_closure(&self) -> Option<Self> {
        self.try_indexed_goal_equality_rewrite_closure_excluding(false, true)
    }

    /// The closure above; with `exclude_goal_fact`, the goal's own ambient
    /// fact (in either orientation) is not a rewrite candidate, matching the
    /// atomic derivation's rule when direct closure was rejected as
    /// non-checkable.
    pub(super) fn try_indexed_goal_equality_rewrite_closure_excluding(
        &self,
        exclude_goal_fact: bool,
        allow_function_unfold: bool,
    ) -> Option<Self> {
        // A judgment stated at an execution frontier (a `have` inside an
        // `open` scope, before the outcome) reads its spellings from the
        // execution's surface map, anchored at the current statement entry.
        let frontier_anchor = match self.context.as_ref() {
            ProofContext::Execution(_) if self.focused_outcome_data().is_none() => {
                self.execution().map(|execution| ProgramPointRef {
                    region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
                    kind: ProgramPointKind::Entry,
                })
            }
            _ => None,
        };
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &self.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        let mut proof = self.clone();
        let mut used = BTreeSet::new();
        loop {
            let goal = proof.goal()?.clone();
            let allows_chain = matches!(goal, Proposition::ConditionIs(_, _));
            let mut refinement = None;
            let goal_variable_count = crate::kernel::proposition_variables(&goal).len();
            for equality in proof.facts().bitvector_equalities_mentioning(&goal) {
                let equality_has_literal_endpoint = matches!(
                    &equality,
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(left, right),
                        true
                    ) if matches!(left.as_ref(), Bitvector32Term::Constant(_))
                        || matches!(right.as_ref(), Bitvector32Term::Constant(_))
                );
                if used.contains(&equality) {
                    continue;
                }
                if exclude_goal_fact
                    && (equality == goal
                        || swapped_bitvector_equality(&equality)
                            .is_some_and(|swapped| swapped == goal))
                {
                    continue;
                }
                let Some(surface) =
                    proof.available_surface_fact(surface_facts, premise_anchor, &equality)
                else {
                    continue;
                };
                // Rewriting is directional even when its admitted premise is
                // a symmetric equality. Keep the selected fact fixed, but
                // try both Surface orientations so the side occurring in the
                // focused branch goal can be replaced.
                let reverse = reverse_surface_equality(&surface);
                for oriented in std::iter::once(surface).chain(reverse) {
                    let Ok(rewritten) = proof.apply_step(ProofStep::Rewrite(oriented)) else {
                        continue;
                    };
                    if let Some(closed) = rewritten
                        .try_direct_logical_closure()
                        .ok()
                        .flatten()
                        .or_else(|| rewritten.try_typed_atomic_simp_closure())
                        .or_else(|| {
                            allow_function_unfold
                                .then(|| {
                                    rewritten
                                        .try_function_unfold_simp_closure(&[])
                                        .ok()
                                        .flatten()
                                })
                                .flatten()
                        })
                    {
                        return Some(closed);
                    }
                    // Do not turn a value already present in the goal into a
                    // fresh symbolic variable merely because the reverse
                    // orientation of an equality happens to match first.
                    // Equal-sized variable-to-variable rewrites remain
                    // available for ordinary equality chains.
                    let does_not_expand_a_literal = !equality_has_literal_endpoint
                        || rewritten.goal().is_some_and(|rewritten_goal| {
                            crate::kernel::proposition_variables(rewritten_goal).len()
                                <= goal_variable_count
                        });
                    if allows_chain
                        && refinement.is_none()
                        && rewritten.goal() != Some(&goal)
                        && does_not_expand_a_literal
                    {
                        refinement = Some((equality.clone(), rewritten));
                    }
                }
            }
            let (equality, rewritten) = refinement?;
            used.insert(equality);
            proof = rewritten;
        }
    }

    /// Rewrites with only the explicitly selected equality premises, at most
    /// once each. Every candidate rewrite is checked transactionally, and
    /// the finite user-written premise list is the entire search space.
    pub(super) fn try_selected_equality_rewrite_chain(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        self.try_selected_equality_rewrite_chain_with_scope(premise_pairs, false)
    }

    /// The explicit-premise counterpart of
    /// [`Self::try_selected_equality_rewrite_chain`]. After each checked
    /// rewrite it may normalize without context or run a typed atomic plan
    /// against the same named premises, but it cannot consult ambient facts.
    fn try_restricted_equality_rewrite_chain(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        self.try_selected_equality_rewrite_chain_with_scope(premise_pairs, true)
    }

    fn try_selected_equality_rewrite_chain_with_scope(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
        restricted: bool,
    ) -> Option<Self> {
        let mut proof = self.clone();
        let mut remaining = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true)
                )
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        while !remaining.is_empty() {
            let mut selected = None;
            for (index, surface) in remaining.iter().enumerate() {
                for oriented in
                    std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
                {
                    match proof.apply_step(ProofStep::Rewrite(oriented)) {
                        Ok(rewritten) => {
                            selected = Some((index, rewritten));
                            break;
                        }
                        Err(_) => {}
                    }
                }
                if selected.is_some() {
                    break;
                }
            }
            let (index, rewritten) = selected?;
            remaining.remove(index);
            let closed = if restricted {
                rewritten.try_typed_atomic_simp_from_selected_premises(premise_pairs)
            } else {
                rewritten
                    .try_direct_logical_closure()
                    .ok()
                    .flatten()
                    .or_else(|| rewritten.try_typed_atomic_simp_closure())
            };
            if let Some(closed) = closed {
                return Some(closed);
            }
            proof = rewritten;
        }
        None
    }

    fn try_typed_atomic_simp_from_selected_premises(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let goal = self.goal()?.clone();
        if premise_pairs
            .iter()
            .any(|(kernel, _)| selected_premise_contains_goal(kernel, &goal))
        {
            return self
                .apply_step(ProofStep::Assumption)
                .ok()
                .filter(Proof::is_complete);
        }
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        match plan_simp_certificate(&goal, &assumptions_from_propositions(&restricted))? {
            SimpEvidence::Normalize => self
                .apply_step(ProofStep::Normalize)
                .ok()
                .filter(Proof::is_complete),
            SimpEvidence::Derivation(derivation) => self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                premise_pairs,
                !matches!(self.context.as_ref(), ProofContext::Execution(_)),
            ),
            SimpEvidence::Assumption => None,
        }
    }

    /// Weakens a constant bound. A goal `value >= c` (or `value <= c`)
    /// closes from a stronger context bound `value >= C` with `C >= c`
    /// (`value <= C` with `C <= c`), the shape a loop's negated guard leaves
    /// on its counter. The proof cites only facts it establishes itself, two
    /// nested `have`s closed by the direct logical closer, so the context
    /// bound needs no Surface spelling; the transitivity theorem then closes
    /// the goal.
    pub(super) fn try_selected_constant_bound_weakening(
        &self,
        goal: &Proposition,
        derivation: &PropositionDerivation,
    ) -> Option<Self> {
        let surface_goal = self.surface_goal()?.clone();
        let (goal_value, goal_bound, lower_bound) = match goal {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(value, bound),
                true,
            ) => (value, bound, true),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(value, bound),
                true,
            ) => (value, bound, false),
            _ => return None,
        };
        let Bitvector32Term::Constant(goal_bits) = goal_bound.as_ref() else {
            return None;
        };
        let goal_constant = *goal_bits as i32;
        let (surface_lower, surface_upper) = surface_nonstrict_parts(&surface_goal)?;
        let (surface_value, surface_goal_constant) = if lower_bound {
            (surface_upper, surface_lower)
        } else {
            (surface_lower, surface_upper)
        };
        let mut candidates = Vec::new();
        for premise in derivation.context_premises().iter() {
            let Proposition::ConditionIs(term, polarity) = premise else {
                continue;
            };
            let bound = match (term, polarity, lower_bound) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(value, bound), true, true)
                | (ConditionTerm::Bitvector32SignedLessThan(value, bound), false, true)
                | (ConditionTerm::Bitvector32SignedLessEqual(value, bound), true, false)
                | (ConditionTerm::Bitvector32SignedGreaterThan(value, bound), false, false)
                    if value == goal_value =>
                {
                    bound
                }
                _ => continue,
            };
            let Bitvector32Term::Constant(bits) = bound.as_ref() else {
                continue;
            };
            let constant = *bits as i32;
            let stronger = if lower_bound {
                constant > goal_constant
            } else {
                constant < goal_constant
            };
            if stronger && !candidates.contains(&constant) {
                candidates.push(constant);
            }
        }
        let operator = if lower_bound {
            ComparisonOperator::GreaterEqual
        } else {
            ComparisonOperator::LessEqual
        };
        for constant in candidates {
            let surface_constant =
                ContractExpression::CFragment(CExpression::Value(int32(constant as u32)));
            let bound_surface = ClickProposition::Comparison {
                left: surface_value.clone(),
                operator: operator.clone(),
                right: surface_constant.clone(),
            };
            let link_surface = ClickProposition::Comparison {
                left: surface_constant.clone(),
                operator: operator.clone(),
                right: surface_goal_constant.clone(),
            };
            let Ok(scope) = self.begin_have(bound_surface.clone()) else {
                continue;
            };
            let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let Ok(scope) = proof.begin_have(link_surface.clone()) else {
                continue;
            };
            let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let theorem = ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: if lower_bound {
                        "int32_ge_transitive".to_string()
                    } else {
                        "int32_le_transitive".to_string()
                    },
                    arguments: vec![
                        surface_value.clone(),
                        surface_constant.clone(),
                        surface_goal_constant.clone(),
                    ],
                },
                premises: vec![bound_surface, link_surface],
            };
            let Ok(applied) = proof.apply_step(theorem) else {
                continue;
            };
            if applied.is_complete() {
                return Some(applied);
            }
            if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                return Some(closed);
            }
        }
        None
    }

    /// Searches the structured predecessor proof already expressible through
    /// the checked API. The goal itself fixes the value and upper bound, so
    /// this visits only selected equalities connected to that value and one
    /// exact upper-bound premise; it never tries every partially synthesizable
    /// context fact as a candidate step.
    pub(super) fn try_selected_predecessor_upper_bound(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if !matches!(self.context.as_ref(), ProofContext::FixedState(_)) {
            return None;
        }
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(predecessor, goal_upper),
            true,
        ) = goal
        else {
            return None;
        };
        let Bitvector32Term::Subtract(value, amount) = predecessor.as_ref() else {
            return None;
        };
        if amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        let upper_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(value.clone(), goal_upper.clone()),
            true,
        );
        let (_, upper_surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &upper_kernel)?;
        let (surface_value, surface_upper) = surface_nonstrict_parts(upper_surface)?;
        let nonnegative_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: surface_value.clone(),
        };
        for (kernel, surface) in premise_pairs {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                kernel
            else {
                continue;
            };
            let selected_constant = if left.as_ref() == value.as_ref() {
                right.as_ref()
            } else if right.as_ref() == value.as_ref() {
                left.as_ref()
            } else {
                continue;
            };
            let Bitvector32Term::Constant(bits) = selected_constant else {
                continue;
            };
            if (*bits as i32) < 0 {
                continue;
            }
            let mut orientations = vec![surface.clone()];
            if let Some(reverse) = reverse_surface_equality(surface)
                && reverse != *surface
            {
                orientations.push(reverse);
            }
            for equality in orientations {
                let scope = self.begin_have(nonnegative_surface.clone()).ok()?;
                let Ok(scope) = scope.apply_step(ProofStep::Rewrite(equality)) else {
                    continue;
                };
                let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                    continue;
                };
                let joined = scope.join().ok()?;
                let theorem = ProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_nonnegative_predecessor_upper_bound".to_string(),
                        arguments: vec![surface_value.clone(), surface_upper.clone()],
                    },
                    premises: vec![nonnegative_surface.clone(), upper_surface.clone()],
                };
                let Ok(applied) = joined.apply_step(theorem) else {
                    continue;
                };
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                    return Some(closed);
                }
            }
        }
        None
    }

    /// Eliminates one disjunction selected by the kernel derivation and
    /// proves both arms on their branch-local `Proof`s. The disjunction is
    /// never reopened once either disjunct is already available, which makes
    /// recursive branch search descend through distinct case assumptions.
    pub(super) fn try_selected_disjunction_cases(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        for (kernel, surface) in premise_pairs {
            let Proposition::Or(left, right) = kernel else {
                continue;
            };
            if self.facts().contains(left) || self.facts().contains(right) {
                continue;
            }
            let (surface_left, surface_right) = match surface {
                ClickProposition::Or(left, right) => {
                    (left.as_ref().clone(), right.as_ref().clone())
                }
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    let ClickProposition::Or(left, right) = proposition.as_ref() else {
                        continue;
                    };
                    (
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(left.as_ref().clone()),
                        },
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(right.as_ref().clone()),
                        },
                    )
                }
                _ => continue,
            };
            // The in-`Proof` split: both case goals coexist in one state,
            // each arm is proven by focusing its recorded id on this one
            // lineage, and the join partitions the retained steps by the
            // per-step goal attribution recorded when they were applied.
            let Ok((split_proof, split, ids)) = self.split_focused_cases(surface.clone()) else {
                continue;
            };
            let marker = split_proof.checkpoint();
            let branch_surfaces = [&surface_left, &surface_right];
            let mut proof = split_proof;
            let mut complete = true;
            for (id, assumed_surface) in ids.into_iter().zip(branch_surfaces) {
                let Ok(focused_branch) = proof.focus_branch(id) else {
                    complete = false;
                    break;
                };
                let selected = focused_branch
                    .try_simp_closure()
                    .ok()
                    .flatten()
                    .or_else(|| {
                        let rewritten = focused_branch
                            .apply_step(ProofStep::Rewrite(assumed_surface.clone()))
                            .ok()?;
                        rewritten
                            .try_direct_logical_closure()
                            .ok()
                            .flatten()
                            .or_else(|| rewritten.try_typed_atomic_simp_closure())
                    });
                let Some(selected) = selected else {
                    complete = false;
                    break;
                };
                proof = selected;
            }
            if complete
                && let Ok(joined) = proof.join_focused_cases(&marker, split, ids, surface.clone())
            {
                return Some(joined);
            }
        }
        None
    }

    /// Applies a planner's flat explicit candidate directly to persistent
    /// `Proof` descendants. Planning may select surface operations, but only
    /// their checked implementations can advance the proof.
    ///
    /// Generated candidates historically retain a final `assumption()` even
    /// when the preceding operation already discharged the goal. Ignore only
    /// that final no-op; any other operation after closure rejects the
    /// candidate. No certificate is materialized or interpreted here.
    pub(super) fn try_planned_explicit_steps(&self, tactics: &[ProofTactic]) -> Option<Self> {
        if tactics.is_empty() {
            return None;
        }
        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == tactics.len() && matches!(tactic, ProofTactic::Assumption) {
                    continue;
                }
                return None;
            }
            let step = explicit_linear_step(tactic)?;
            proof = proof.apply_step(step).ok()?;
        }
        proof.focused_discharged().then_some(proof)
    }

    /// Specializes one checkable universal premise selected by the atomic
    /// decision at the current goal. Planning only chooses the explicit
    /// quantified fact, argument, and guards; each selected operation advances
    /// this `Proof` directly.
    pub(super) fn try_selected_forall_instantiation(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_instantiation(goal, premise_pairs).or_else(|| {
            let surface_goal = self.surface_goal()?;
            let extra_arguments = self
                .proposition_obligation()
                .into_iter()
                .flat_map(|goal| goal.surface_bindings.iter())
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::CFragment(CExpression::Value(CValue::Int32(value))) => {
                        Some((
                            value.clone(),
                            ContractExpression::CFragment(CExpression::Variable(name.clone())),
                        ))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            plan_explicit_forall_instantiation_transport(
                goal,
                surface_goal,
                premise_pairs,
                &extra_arguments,
                &|conclusion| {
                    self.facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone())
                        .derive_simp_atomic_proposition(goal)
                        .is_some()
                },
            )
        })?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Tries only universal facts introduced by checked predicate unfolds when
    /// the atomic decision cannot name an instantiated premise. Candidate
    /// discovery is read-only; a specialization is retained only after the
    /// ordinary `InstantiateUsing` operation advances and closes this Proof.
    #[cfg(test)]
    pub(super) fn try_indexed_forall_instantiation(&self) -> Option<Self> {
        self.try_indexed_forall_instantiation_with_surfaces(&[])
    }

    fn try_indexed_forall_instantiation_with_surfaces(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Self> {
        let goal = self.goal()?;
        let execution_view = matches!(self.context.as_ref(), ProofContext::Execution(_))
            .then(|| self.premise_fixed_state_view())
            .flatten();
        let surface_facts = match self.context.as_ref() {
            ProofContext::Pure(context) => &context.theorem_context.surface_requirements,
            ProofContext::FixedState(context) => context.surface_propositions,
            ProofContext::Execution(_) => &execution_view.as_ref()?.surface_propositions,
        };
        let bound_variable_names = match self.proposition_obligation() {
            Some(goal) => goal
                .surface_bindings
                .iter()
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Variable(variable),
                    ))) => Some((*variable, name.clone())),
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>(),
            _ => BTreeMap::new(),
        };
        let surface_form = |fact: &Proposition| {
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                self.lower_surface_proposition(surface, "introduced forall premise")
                    .is_ok_and(|lowered| {
                        lowered == *fact
                            || condition_polarity_equivalent(&lowered, fact)
                            || quantified_equivalent_available_fact(
                                fact,
                                std::slice::from_ref(&lowered),
                            )
                            .is_some()
                    })
            }) {
                return Some(surface.clone());
            }
            let recorded = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(fact)
                    .next()
                    .cloned(),
                ProofContext::FixedState(context) => {
                    context.surface_propositions.surfaces(fact).next().cloned()
                }
                ProofContext::Execution(_) => execution_view
                    .as_ref()?
                    .surface_propositions
                    .surfaces(fact)
                    .next()
                    .cloned(),
            };
            let synthesized = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => {
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        context.parameters,
                        context.arguments,
                        context.state,
                        &bound_variable_names,
                    )
                }
                ProofContext::Execution(_) => {
                    let view = execution_view.as_ref()?;
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        view.parameters,
                        view.arguments,
                        view.state,
                        &bound_variable_names,
                    )
                }
            };
            recorded.or(synthesized)
        };
        let mut quantified_candidates = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let quantified = surface_facts.available_kernel_matching(surface, |kernel| {
                    matches!(kernel, Proposition::ForAll { .. })
                        && self.facts().quantified_fact_available(kernel)
                })?;
                Some((quantified.clone(), Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        for quantified in self.facts().predicate_unfolded_universal_facts() {
            if !quantified_candidates
                .iter()
                .any(|(candidate, _)| candidate == quantified)
            {
                quantified_candidates.push((quantified.clone(), None));
            }
        }
        for (quantified, introduced_surface) in quantified_candidates {
            // Reject shape-incompatible universals before Surface lookup or
            // synthesis. Candidate extraction is structural and bounded by
            // this one indexed fact and the focused branch goal; the expensive
            // form work is reserved for a specialization that can
            // actually mention the goal's concrete argument.
            let candidate_values =
                crate::kernel::forall_guided_instantiation_candidate_values(&quantified, goal);
            let Proposition::ForAll { var, body, .. } = &quantified else {
                unreachable!("the predicate-unfolded universal index contains only universals")
            };
            if candidate_values.is_empty() {
                continue;
            }
            let recorded_surfaces = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::FixedState(context) => context
                    .surface_propositions
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => execution_view?
                    .surface_propositions
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::FixedState(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let mut surfaces = introduced_surface.into_iter().collect::<Vec<_>>();
            for recorded in recorded_surfaces {
                let candidate = match recorded {
                    ClickProposition::PredicateCall {
                        ref name,
                        ref arguments,
                    } => predicate_environment.get(name).and_then(|definition| {
                        instantiate_click_predicate_definition(definition, arguments).ok()
                    }),
                    other => Some(other),
                };
                if let Some(candidate) = candidate
                    && !surfaces.contains(&candidate)
                {
                    surfaces.push(candidate);
                }
            }
            let synthesized = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => synthesize_surface_proposition(
                    &quantified,
                    context.parameters,
                    context.arguments,
                    context.state,
                ),
                ProofContext::Execution(_) => {
                    let view = execution_view?;
                    synthesize_surface_proposition(
                        &quantified,
                        view.parameters,
                        view.arguments,
                        view.state,
                    )
                }
            };
            if let Some(synthesized) = synthesized
                && !surfaces.contains(&synthesized)
            {
                surfaces.push(synthesized);
            }
            // Unfolding retains the opaque predicate fact alongside its
            // checked body. Reconstruct that body's exact surface form
            // from only the active predicate indexes when generic synthesis
            // cannot express it (notably byte-indexed loads).
            if surfaces.is_empty() {
                let click_function_environment = match self.context.as_ref() {
                    ProofContext::Pure(context) => context.click_function_environment,
                    ProofContext::FixedState(context) => context.click_function_environment,
                    ProofContext::Execution(context) => context.click_function_environment,
                };
                for name in self.focused_branch_unfolds().iter() {
                    for opaque in self.facts().mentioning_predicate(name) {
                        let opaque_surfaces = match self.context.as_ref() {
                            ProofContext::Pure(context) => context
                                .theorem_context
                                .surface_requirements
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::FixedState(context) => context
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Execution(_) => execution_view?
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                        };
                        for opaque_surface in opaque_surfaces {
                            let ClickProposition::PredicateCall {
                                name: surface_name,
                                arguments,
                            } = opaque_surface
                            else {
                                continue;
                            };
                            let Some(definition) = predicate_environment.get(&surface_name) else {
                                continue;
                            };
                            let Ok(body_surface) =
                                instantiate_click_predicate_definition(definition, &arguments)
                            else {
                                continue;
                            };
                            if unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                std::slice::from_ref(name),
                                opaque,
                                self.facts().assumptions(),
                            )
                            .is_ok_and(|kernel| kernel == quantified)
                                && !surfaces.contains(&body_surface)
                            {
                                surfaces.push(body_surface);
                            }
                        }
                    }
                }
            }
            for surface in surfaces {
                for value in candidate_values.iter().cloned() {
                    let argument = match &value {
                        Bitvector32Term::Constant(bits) => Some(ContractExpression::CFragment(
                            CExpression::Value(CValue::Int32(Bitvector32Term::Constant(*bits))),
                        )),
                        Bitvector32Term::Variable(variable) => {
                            let Some(goal) = self.proposition_obligation() else {
                                continue;
                            };
                            goal.surface_bindings.iter().find_map(|(name, binding)| {
                                matches!(
                                    binding,
                                    ContractExpression::CFragment(CExpression::Value(
                                        CValue::Int32(Bitvector32Term::Variable(bound))
                                    )) if bound == variable
                                )
                                .then(|| {
                                    ContractExpression::CFragment(CExpression::Variable(
                                        name.clone(),
                                    ))
                                })
                            })
                        }
                        _ => None,
                    };
                    let Some(argument) = argument else {
                        continue;
                    };
                    let instantiated =
                        substitute_int32_variable_in_proposition(body, *var, value.clone());
                    let mut guard_facts = Vec::new();
                    let mut current = &instantiated;
                    let mut guards_available = true;
                    while let Proposition::Implies(guard, consequent) = current {
                        let mut conjuncts = Vec::new();
                        atomic_conjuncts(guard, &mut conjuncts);
                        for conjunct in conjuncts {
                            if matches!(normalize_proposition(conjunct), SimpProposition::True) {
                                continue;
                            }
                            let exact = std::iter::once(conjunct.clone())
                                .chain(condition_polarity_forms(conjunct))
                                .find(|candidate| self.facts().contains(candidate));
                            let selected = exact.map(|fact| vec![fact]).or_else(|| {
                                self.facts()
                                    .assumptions()
                                    .derive_simp_atomic_proposition(conjunct)
                                    .map(|derivation| derivation.context_premises())
                            });
                            let Some(selected) = selected else {
                                guards_available = false;
                                break;
                            };
                            for actual in selected {
                                let Some(form) = surface_form(&actual) else {
                                    guards_available = false;
                                    break;
                                };
                                if !guard_facts
                                    .iter()
                                    .any(|(candidate, _)| candidate == &actual)
                                {
                                    guard_facts.push((actual, form));
                                }
                            }
                            if !guards_available {
                                break;
                            }
                        }
                        if !guards_available {
                            break;
                        }
                        current = consequent;
                    }
                    if !guards_available {
                        continue;
                    }
                    let instantiated_proof = match self.apply_step(ProofStep::InstantiateUsing {
                        quantified: surface.clone(),
                        argument: argument.clone(),
                        premises: guard_facts
                            .iter()
                            .map(|(_, surface)| surface.clone())
                            .collect(),
                    }) {
                        Ok(proof) => proof,
                        Err(_) => continue,
                    };
                    let conclusion = current.clone();
                    if &conclusion == goal || conclusion.clone() == goal.clone() {
                        if let Ok(closed) = instantiated_proof.apply_step(ProofStep::Assumption) {
                            return Some(closed);
                        }
                        continue;
                    }

                    let transport_assumptions = self
                        .facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone());
                    let Some(transport_derivation) =
                        transport_assumptions.derive_simp_atomic_proposition(goal)
                    else {
                        continue;
                    };
                    let mut transport_surfaces = Vec::new();
                    let mut transport_written = true;
                    for premise in transport_derivation.context_premises() {
                        if premise == conclusion {
                            continue;
                        }
                        if matches!(premise, Proposition::ForAll { .. })
                            && quantified_equivalent_available_fact(
                                &premise,
                                std::slice::from_ref(&quantified),
                            )
                            .is_some()
                        {
                            // `InstantiateUsing` has already checked this
                            // universal and published its selected conclusion.
                            // Do not feed the quantified source back into the
                            // following transport as an unrelated premise.
                            continue;
                        }
                        let Some(form) = surface_form(&premise) else {
                            transport_written = false;
                            break;
                        };
                        if !transport_surfaces.contains(&form) {
                            transport_surfaces.push(form);
                        }
                    }
                    if !transport_written {
                        continue;
                    }
                    let (selector, quantified_surface) = match &surface {
                        ClickProposition::At {
                            selector,
                            proposition,
                        } => (Some(selector.clone()), proposition.as_ref()),
                        other => (None, other),
                    };
                    let ClickProposition::ForAll {
                        name,
                        body: surface_body,
                        ..
                    } = quantified_surface
                    else {
                        continue;
                    };
                    let substitutions = std::iter::once((name.clone(), argument.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let Ok(mut source) = substitute_click_proposition(surface_body, &substitutions)
                    else {
                        continue;
                    };
                    while let ClickProposition::Implies(_, body) = source {
                        source = *body;
                    }
                    if let Some(selector) = selector {
                        source = ClickProposition::At {
                            selector,
                            proposition: Box::new(source),
                        };
                    }
                    transport_surfaces.insert(0, source.clone());
                    let target = self.surface_goal()?.clone();
                    match instantiated_proof.search_fact_transport_from_candidates(
                        &source,
                        &target,
                        transport_surfaces,
                        "indexed universal conclusion transport",
                    ) {
                        Ok(transported) if transported.focused_discharged() => {
                            return Some(transported);
                        }
                        Ok(_) | Err(_) => {}
                    }
                }
            }
        }
        None
    }

    /// Builds the binder-introduction chain from only the universal premises
    /// selected by the atomic decision. The planner never scans the ambient
    /// fact set; every resulting refinement applies directly to this `Proof`.
    pub(super) fn try_selected_forall_goal(
        &self,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Retains the pointwise unchanged-load certificate for a guarded
    /// universal outcome. The kernel derivation has already selected the
    /// finite context premises relevant to this goal; after introducing the
    /// binder and guard, transport searches only those forms plus the
    /// freshly extracted guard leaves.
    pub(super) fn try_selected_unchanged_load_forall_goal(
        &self,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if self.focused_outcome_data().is_none() {
            return None;
        }
        let mut cursor = surface_goal;
        let mut proof = self.clone();
        let mut introduced_forall = false;
        while let ClickProposition::ForAll { body, .. } = cursor {
            proof = proof.apply_step(ProofStep::Intro).ok()?;
            cursor = body;
            introduced_forall = true;
        }
        if !introduced_forall {
            return None;
        }
        let ClickProposition::Implies(antecedent, _) = cursor else {
            return None;
        };
        proof = proof.apply_step(ProofStep::Intro).ok()?;
        let mut guard_surfaces = Vec::new();
        collect_surface_conjunct_leaves(antecedent, &mut guard_surfaces);
        for guard in &guard_surfaces {
            proof = proof.apply_step(ProofStep::Extract(guard.clone())).ok()?;
        }
        let target = proof.surface_goal()?.clone();
        let source = old_reflexive_transport_source(&target)?;
        let source_pairs = proof
            .lower_surface_proposition(&source, "unchanged-load transport source")
            .ok()
            .and_then(|kernel| {
                proof
                    .facts()
                    .assumptions()
                    .derive_atomic_proposition(&kernel)
            })
            .map(|derivation| {
                let data = proof.focused_outcome_data()?;
                let pairs = derivation
                    .context_premises()
                    .into_iter()
                    .filter_map(|premise| {
                        proof
                            .available_surface_fact(
                                &data.surface_propositions,
                                data.premise_anchor.as_ref(),
                                &premise,
                            )
                            .map(|surface| (premise, surface))
                    })
                    .collect::<Vec<_>>();
                Some(pairs)
            })
            .flatten()
            .unwrap_or_default();
        let data = proof.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let view = proof.outcome_fixed_state_view()?;
        let anchor_state = view.recorded_snapshots.get(anchor)?;
        let mut anchored_candidates = Vec::new();
        for (kernel, _) in premise_pairs.iter().chain(&source_pairs) {
            let Some(surface) = synthesize_surface_proposition(
                kernel,
                view.parameters,
                view.arguments,
                anchor_state,
            ) else {
                continue;
            };
            let Ok(surface) = surface_at_snapshot(&surface, anchor) else {
                continue;
            };
            let Some((left, right)) = surface_nonstrict_parts(&surface) else {
                continue;
            };
            let left_is_atomic_variable = match &left {
                ContractExpression::CFragment(CExpression::Variable(_)) => true,
                ContractExpression::At { expression, .. } => matches!(
                    expression.as_ref(),
                    ContractExpression::CFragment(CExpression::Variable(_))
                ),
                _ => false,
            };
            if left == right || !left_is_atomic_variable || anchored_candidates.contains(&surface) {
                continue;
            }
            let Ok(lowered) =
                proof.lower_surface_proposition(&surface, "unchanged-load transport premise")
            else {
                continue;
            };
            if lowered == *kernel || condition_polarity_equivalent(&lowered, kernel) {
                anchored_candidates.push(surface);
            }
        }
        // The source derivation must identify one exact non-strict bound at
        // the outcome anchor. Ambiguity is a prompt miss, never permission to
        // probe combinations of historical facts.
        let [anchored_candidate] = anchored_candidates.as_slice() else {
            return None;
        };
        let candidates = std::iter::once(anchored_candidate.clone()).chain(guard_surfaces);
        let transported =
            match proof.search_fixed_state_fact_transport(&source, &target, candidates) {
                Ok(transported) => transported,
                Err(error) => {
                    let _ = error;
                    return None;
                }
            };
        if transported.is_complete() {
            return Some(transported);
        }
        transported.try_direct_logical_closure().ok().flatten()
    }

    pub(super) fn try_typed_atomic_simp_closure(&self) -> Option<Self> {
        let (goal, derivation, premise_pairs, fixed_state_application_closes_goal) =
            self.selected_simp_derivation(false)?;
        self.check_typed_atomic_simp_candidate(
            &goal,
            &derivation,
            &premise_pairs,
            fixed_state_application_closes_goal,
        )
    }

    /// Searches from exactly the Surface premises named by `simp() using`.
    /// This query cannot add facts or close the goal: it returns only the
    /// descendant obtained by checking the typed atomic decision through the
    /// ordinary Proof transitions.
    pub(in crate::surface::proof) fn try_restricted_simp_closure(
        &self,
        surfaces: &[ClickProposition],
    ) -> Option<Self> {
        // A named restricted premise may be a leaf of one exact available
        // conjunction (commonly after `unfold(predicate)`). Materialize that
        // leaf through the checked `extract` transition before
        // asking the restricted planner to use it. The returned descendant
        // therefore owns both the semantic fact and the Surface provenance;
        // expansion does not need to reconstruct and check a certificate to
        // justify the premise later.
        let mut proof = self.clone();
        for surface in surfaces {
            let kernel = proof
                .lower_surface_proposition(surface, "restricted simp premise")
                .ok()?;
            proof = proof.materialize_selected_resource_separation(&kernel)?;
            if !proof.facts().contains_top_level(&kernel)
                && !normalizes_context_free(&kernel)
                && proof.facts().contains_proper_conjunct(&kernel)
            {
                proof = proof.apply_step(ProofStep::Extract(surface.clone())).ok()?;
                if proof.is_complete() {
                    return Some(proof);
                }
            }
        }
        let goal = proof.goal()?;
        let premise_pairs = surfaces
            .iter()
            .map(|surface| {
                let kernel = proof
                    .lower_surface_proposition(surface, "restricted simp premise")
                    .ok()?;
                // A listed premise that lowers to a context-free truth needs
                // no ambient fact authority. Retaining it lets the restricted
                // derivation erase reflexive field equalities after the
                // outcome state has evaluated their loads. Resource
                // separation may instead be supplied by the compact
                // composition authority, so use the same checked availability
                // query without publishing unrelated member pairs.
                (proof.facts().available_across_effects(&kernel, &[])
                    || normalizes_context_free(&kernel))
                .then_some((kernel, surface.clone()))
            })
            .collect::<Option<Vec<_>>>()?;
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let theorem_application_closes_goal =
            !matches!(self.context.as_ref(), ProofContext::Execution(_));
        plan_simp_certificate(goal, &assumptions_from_propositions(&restricted))
            .and_then(|plan| {
                let SimpEvidence::Derivation(derivation) = &plan else {
                    return None;
                };
                proof.check_typed_atomic_simp_candidate(
                    goal,
                    derivation,
                    &premise_pairs,
                    theorem_application_closes_goal,
                )
            })
            .or_else(|| proof.try_restricted_equality_rewrite_chain(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_order_transitivity(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_increment_order(&premise_pairs))
            // An exact selected premise or context-free normalization may
            // close directly. An arbitrary ambient `assumption` must remain
            // invisible through this explicitly restricted boundary.
            .or_else(|| proof.try_typed_atomic_simp_from_selected_premises(&premise_pairs))
    }

    pub(super) fn check_typed_atomic_simp_candidate(
        &self,
        goal: &Proposition,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
        fixed_state_application_closes_goal: bool,
    ) -> Option<Self> {
        let tactics = recorded_signed_order_pairs(derivation, &premise_pairs)
            .and_then(|ordered| {
                plan_recorded_signed_order_path_for_context(
                    goal,
                    &ordered,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| plan_recorded_bitvector_equality_path(goal, derivation, &premise_pairs))
            .or_else(|| plan_recorded_pointer_alignment(goal, derivation, &premise_pairs))
            .or_else(|| plan_recorded_pointer_word(goal, derivation, &premise_pairs))
            .or_else(|| {
                let recorded =
                    recorded_load_address_congruence_path_pairs(derivation, &premise_pairs)?;
                plan_recorded_load_address_congruence(goal, derivation, &recorded)
            })
            .or_else(|| {
                plan_explicit_loadability_transport(goal, self.surface_goal()?, premise_pairs)
            })
            .or_else(|| plan_pointer_advanced_load_equality(goal, premise_pairs))
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_upper_bound_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_upper_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_constant_upper_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_constant_upper_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_strictly_increases_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_strictly_increases_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_one_plus_strictly_increases_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_one_plus_strictly_increases_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_below_max_is_defined_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_below_max_is_defined_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_one_plus_below_max_is_defined_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_one_plus_below_max_is_defined_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_nonnegative_add_within_max_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_nonnegative_add_within_max_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_nonnegative_subtract_within_value_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_nonnegative_subtract_within_value_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_lower_bound_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_lower_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_greater_equal_lower_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_greater_equal_lower_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_strict_greater_lower_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_strict_greater_lower_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_strict_greater_from_strict_lower_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_strict_greater_from_strict_lower_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_preserves_order_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_preserves_order_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_positive_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_positive_predecessor_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_positive_predecessor_strictly_decreases_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_positive_predecessor_strictly_decreases_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_nonnegative_predecessor_upper_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_equal_one_predecessor_is_zero_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_equal_one_predecessor_is_zero(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
                        derivation,
                        &premise_pairs,
                    )
                })?;
                plan_recorded_int32_equal_one_predecessor_for_context(
                    goal,
                    derivation,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_one_le_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_one_le_predecessor_strictly_decreases_pairs(
                        derivation,
                        &premise_pairs,
                    )
                })?;
                plan_recorded_int32_one_le_predecessor_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_le_and_not_lt_implies_equality_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_ge_and_not_gt_implies_equality_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_ge_and_not_gt_implies_equality_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_positive_is_nonnegative_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_positive_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_strictly_positive_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_strictly_positive_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_successor_le_implies_lt_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_successor_le_implies_lt_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_constant_lower_bound_weakening_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_constant_lower_bound_weakening_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_negated_strict_successor_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_negated_strict_successor_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_le_and_neq_implies_strict_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_le_and_neq_implies_strict_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let finite_premises = premise_pairs
                    .iter()
                    .filter(|(premise, _)| {
                        matches!(
                            premise,
                            Proposition::ConditionIs(
                                ConditionTerm::Float32(CFloatCondition::Classification {
                                    classification: CFloatClassification::Finite,
                                    ..
                                }) | ConditionTerm::Float64(CFloatCondition::Classification {
                                    classification: CFloatClassification::Finite,
                                    ..
                                }),
                                true
                            )
                        )
                    })
                    .collect::<Vec<_>>();
                let kernels = finite_premises
                    .iter()
                    .map(|(premise, _)| premise.clone())
                    .collect::<Vec<_>>();
                crate::kernel::proof::fact_reasoning::check_float_reflexive_comparison(
                    goal, &kernels,
                )
                .then(|| {
                    vec![ProofTactic::ArithmeticUsing(
                        finite_premises
                            .into_iter()
                            .map(|(_, surface)| surface.clone())
                            .collect(),
                    )]
                })
            })?;
        // The planner selects only Surface-expressible explicit operations.
        // Apply those through the same recursive Proof driver used by
        // authoritative source scripts; the plan is provenance input, not an
        // independently interpreted semantic certificate.
        let proof = self.try_planned_linear_script(&tactics).ok().flatten()?;
        proof.focused_discharged().then_some(proof)
    }

    /// Runs one branch arm of the linear script driver on the focused branch sibling
    /// goal. Both smart and explicit bodies apply their operations directly to
    /// this `Proof`; ordinary source interpretation does not first construct a
    /// certificate.
    pub(super) fn try_focused_script_arm(
        &self,
        tactics: &[ProofTactic],
        authoritative: bool,
        generated: bool,
    ) -> Result<Option<Self>, ClickError> {
        if generated {
            self.try_planned_linear_script(tactics)
        } else if authoritative {
            self.try_authoritative_linear_script(tactics)
        } else {
            self.try_linear_script(tactics)
        }
    }

    /// Interprets one supported source script directly on this proof.
    ///
    /// Smart tactics search for checked descendants while explicit tactics
    /// apply their named operation. The returned proof already owns both the
    /// semantic result and its exact provenance; no certificate is constructed
    /// or checked to establish acceptance.
    pub(in crate::surface::proof) fn try_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let contains_search = script_contains_linear_search(tactics);
        match self.try_linear_script_inner(tactics, false, false) {
            // Before this migration, an explicit-only script was checked by
            // the established source interpreter whenever the typed Proof
            // surface did not yet admit it. Preserve that transactional
            // fallback while successful explicit scripts take the direct
            // path. Smart-script failures retain their checked diagnostic.
            Err(_) if !contains_search && !crate::instrumentation::deadline_exceeded() => {
                #[cfg(test)]
                record_explicit_linear_fallback();
                Ok(None)
            }
            result => result,
        }
    }

    /// Checks source whose caller has already selected this Proof driver as
    /// the semantic authority. Explicit operation failures propagate instead
    /// of being converted into a compatibility miss; recursive scopes and
    /// branch arms inherit the same rule.
    pub(in crate::surface::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_linear_script_inner(tactics, true, false)
    }

    /// Applies one planner-selected or expansion-generated Surface script to
    /// this Proof. Generated theorem plans may retain a final `assumption()`
    /// for outcome contexts where the theorem sometimes adds only an anchored
    /// equivalent fact. If an earlier checked operation closes that body
    /// exactly, only that final generated no-op is ignored. Ordinary explicit
    /// source scripts remain strict through `try_linear_script`.
    pub(in crate::surface::proof) fn try_planned_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_linear_script_inner(tactics, true, true)
    }

    pub(super) fn try_linear_script_inner(
        &self,
        tactics: &[ProofTactic],
        authoritative: bool,
        generated: bool,
    ) -> Result<Option<Self>, ClickError> {
        if tactics.is_empty() {
            return Ok(None);
        }

        // Recognize the complete path before doing any search. `simp` closes
        // the remaining goal and is therefore meaningful only at the end.
        if !linear_script_is_supported(tactics) {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                // A final `assumption` after a step that already discharged
                // the goal (a `transport` whose target is the goal, an exact
                // theorem conclusion) asserts a closed judgment: a harmless
                // no-op that emits no redundant certificate step. A final
                // `simp` likewise. Any other suffix after closure is a
                // declined shape.
                if index + 1 == tactics.len()
                    && matches!(tactic, ProofTactic::Assumption | ProofTactic::Simp)
                {
                    continue;
                }
                if matches!(tactic, ProofTactic::Simp) {
                    continue;
                }
                return Ok(None);
            }
            match tactic {
                ProofTactic::ApplyTheorem(application) => {
                    let Some(applied) = proof.try_theorem_application(application)? else {
                        return Ok(None);
                    };
                    proof = applied;
                }
                ProofTactic::Simp => {
                    let Some(closed) = proof.try_simp_closure()? else {
                        return Ok(None);
                    };
                    proof = closed;
                }
                ProofTactic::SimpUsing(simp) => {
                    let Some(closed) = proof.try_restricted_simp_closure(&simp.premises) else {
                        return Ok(None);
                    };
                    proof = closed;
                }
                ProofTactic::Have(have) => {
                    let scope = proof.begin_have(have.proposition.clone())?;
                    let selected = match &have.proof {
                        SourceProof::Default
                        | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
                            scope.try_simp_closure()?
                        }
                        SourceProof::Script(body) => {
                            if generated {
                                scope.try_planned_linear_script(body)?
                            } else if authoritative {
                                scope.try_authoritative_linear_script(body)?
                            } else {
                                scope.try_linear_script(body)?
                            }
                        }
                        SourceProof::Tactic(SmartTactic::Frame) => None,
                    };
                    let Some(selected) = selected else {
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let (split_proof, split, ids) =
                        proof.split_focused_if(proof_if.condition.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(then_done) = split_proof
                        .focus_branch(ids[0])?
                        .try_focused_script_arm(&proof_if.then_tactics, authoritative, generated)?
                    else {
                        return Ok(None);
                    };
                    let Some(both_done) = then_done.focus_branch(ids[1])?.try_focused_script_arm(
                        &proof_if.else_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = both_done.join_focused_if(
                        &marker,
                        split,
                        ids,
                        proof_if.condition.clone(),
                    )?;
                }
                ProofTactic::Cases(proof_cases) => {
                    let (split_proof, split, ids) =
                        proof.split_focused_cases(proof_cases.disjunction.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(left_done) =
                        split_proof.focus_branch(ids[0])?.try_focused_script_arm(
                            &proof_cases.left_tactics,
                            authoritative,
                            generated,
                        )?
                    else {
                        return Ok(None);
                    };
                    let Some(both_done) = left_done.focus_branch(ids[1])?.try_focused_script_arm(
                        &proof_cases.right_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = both_done.join_focused_cases(
                        &marker,
                        split,
                        ids,
                        proof_cases.disjunction.clone(),
                    )?;
                }
                tactic => {
                    let step = explicit_linear_step(tactic)
                        .expect("the linear script was recognized before execution");
                    proof = proof.apply_step(step)?;
                }
            }
        }

        Ok(proof.focused_discharged().then_some(proof))
    }

    /// Smart-only compatibility wrapper retained for focused branch regressions.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_linear_smart_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        if !script_contains_linear_search(tactics) {
            return Ok(None);
        }
        self.try_linear_script(tactics)
    }

    /// Whether this source proof is wholly represented by the recursive
    /// proposition driver. This is a syntax-only capability query.
    pub(in crate::surface::proof) fn supports_linear_source(proof: &SourceProof) -> bool {
        source_proof_is_supported(proof)
    }

    /// Tries one bare `step()` in the whole proof context. There is no premise
    /// selection: the checked step either advances the frontier or reports why
    /// the statement cannot run here. An undecided C `if` is left to the
    /// structural branch driver.
    pub(in crate::surface::proof) fn try_statement_step(&self) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Err(self.step_error("execution-frontier proof lost its semantic state"));
        };
        // Structural frontiers belong to the branch and loop operations.
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "smart step selection",
        )?;
        if matches!(statement, CStatement::While { .. }) {
            return Ok(None);
        }
        if matches!(statement, CStatement::If { .. } | CStatement::Switch { .. }) {
            // A C `if` the context decides is one step into that arm; one it
            // cannot decide is a fork for the driver's branch handling. A
            // symbolic switch likewise belongs to the bounded planner, which
            // materializes its case split before applying one switch theorem
            // per path.
            return match self.apply_step(ProofStep::Step) {
                Ok(proof) => Ok(Some(proof)),
                Err(_) => {
                    check_verification_deadline()?;
                    Ok(None)
                }
            };
        }
        // The statement runs in the whole proof context; nothing can supply
        // more than the step already sees, so its failure is the answer,
        // with the step's diagnostic.
        self.apply_step(ProofStep::Step).map(Some)
    }
}

/// Candidate spellings of one kernel fact from recorded program-point
/// snapshots, nearest first: the fact synthesized from a snapshot where its cells are
/// readable and re-read there (`at(statement(n).entry, ...)`), then, for an
/// equality whose operands were read from different snapshots, one anchor per
/// operand. Callers must re-lower each candidate and accept it only when it
/// denotes exactly `kernel`.
pub(super) fn synthesize_surface_at_recorded_snapshots(
    kernel: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    recorded_snapshots: &RecordedSnapshots,
    anchor: &ProgramPointRef,
) -> Vec<ClickProposition> {
    let anchor_index = match &anchor.region {
        CodeRegionRef::Statement(index) => *index,
        _ => usize::MAX,
    };
    // Recorded statement entries: those at or before the anchor, nearest
    // first, then any recorded later (a loop body's statements lie beyond
    // the loop's own index).
    let mut indices = recorded_snapshots
        .keys()
        .filter_map(|selector| match selector {
            SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Statement(index),
                kind: ProgramPointKind::Entry,
            }) => Some(*index),
            SnapshotSelector::ProgramPoint(_) | SnapshotSelector::Mark(_) => None,
        })
        .collect::<Vec<_>>();
    indices.sort_unstable();
    indices.dedup();
    let (before, after): (Vec<usize>, Vec<usize>) = indices
        .into_iter()
        .partition(|index| *index <= anchor_index);
    let points = before
        .into_iter()
        .rev()
        .chain(after)
        .filter_map(|index| {
            let point = ProgramPointRef {
                region: CodeRegionRef::Statement(index),
                kind: ProgramPointKind::Entry,
            };
            let state = recorded_snapshots.get(&point)?;
            Some((point, state))
        })
        .collect::<Vec<_>>();
    let mut candidates = points
        .iter()
        .filter_map(|(point, state)| {
            let surface = synthesize_surface_proposition(kernel, parameters, arguments, state)?;
            surface_at_snapshot(&surface, point).ok()
        })
        .collect::<Vec<_>>();
    candidates.extend(synthesize_surface_equality_across_points(
        kernel, parameters, arguments, &points,
    ));
    candidates
}

/// `b == a` for the fact `a == b`.
fn swapped_bitvector_equality(fact: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), value) = fact else {
        return None;
    };
    Some(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(right.clone(), left.clone()),
        *value,
    ))
}

/// Whether a goal is explicitly named by a restricted premise, either as
/// the premise itself or as one of its conjunction leaves. Checked fact
/// indexing makes those leaves available to `assumption`; this predicate
/// keeps that closure tied to the user's finite `using` list.
fn selected_premise_contains_goal(premise: &Proposition, goal: &Proposition) -> bool {
    if premise == goal || condition_polarity_equivalent(premise, goal) {
        return true;
    }
    match premise {
        Proposition::And(left, right) => {
            selected_premise_contains_goal(left, goal)
                || selected_premise_contains_goal(right, goal)
        }
        _ => false,
    }
}
