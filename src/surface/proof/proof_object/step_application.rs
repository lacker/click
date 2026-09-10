//! Simple-step dispatch (`apply_step`) and checked frame application.

use super::*;

impl<'a> Proof<'a> {
    /// Checks one explicit proof step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(in crate::surface::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, None)
    }

    /// Applies a step while retaining its source occurrence for any ordered
    /// terminal work the checked transition has to schedule. The source site
    /// affects diagnostics and finalization order only; the certificate node
    /// remains exactly the supplied `ProofStep`.
    pub(super) fn apply_step_with_origin(
        &self,
        step: ProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        // Diagnostics from this step, and from every scope it opens, name the
        // source occurrence the driver is checking rather than a tree depth.
        if let Some(origin) = origin
            && !self.site().addresses_source_tactic(origin.source_index)
        {
            return self
                .at_source_tactic(origin.source_index)
                .apply_step_with_origin(step, Some(origin));
        }
        if self.focused_discharged() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                proof_step_source_name(&step)
            )));
        }

        if let ProofStep::CloseInvariantsBy(body) = &step {
            return self.apply_close_invariants_body(&body.to_proof_tactics());
        }
        if let ProofStep::Have { proposition, proof } = &step {
            return self.apply_have_step(proposition, proof);
        }
        if matches!(&step, ProofStep::Step | ProofStep::StepContract(_)) {
            return self.apply_execution_statement_step(step);
        }

        let checked_proposition_successor = match &step {
            ProofStep::Assumption => Some(self.apply_assumption()),
            ProofStep::Normalize => Some(self.apply_normalize()),
            ProofStep::NormalizeUsing(premises) => Some(self.apply_normalize_using(premises)),
            ProofStep::ArithmeticUsing(premises) => Some(self.apply_arithmetic_using(premises)),
            ProofStep::Intro => Some(self.apply_intro()),
            ProofStep::Split => Some(self.apply_split()),
            ProofStep::Left => Some(self.apply_left()),
            ProofStep::Right => Some(self.apply_right()),
            ProofStep::Enumerate => Some(self.apply_enumerate()),
            ProofStep::Contradiction(surface) => Some(self.apply_contradiction(surface)),
            ProofStep::Extract(proposition) => Some(self.apply_extract(proposition)),
            ProofStep::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => Some(self.apply_fixed_state_instantiate_using(quantified, argument, premises)),
            ProofStep::Mark(name) => Some(self.apply_execution_mark(name)),
            ProofStep::CloseInvariants => Some(self.apply_close_invariants()),
            _ => None,
        };
        if let Some(successor) = checked_proposition_successor {
            return Ok(Self {
                site: self.site.clone(),
                context: self.context.clone(),
                state: successor?,
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: Some(Arc::new(step)),
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth + 1,
                }),
            });
        }

        let transition = match &step {
            ProofStep::Induct {
                parameter,
                hypothesis,
            } => self.apply_induct(parameter, hypothesis),
            ProofStep::ApplyInduction {
                hypothesis,
                argument,
                premises,
            } => self.apply_induction(hypothesis, argument, premises),
            ProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            ProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            ProofStep::UnfoldPredicate(name) => self.apply_predicate_unfold(name),
            ProofStep::UnfoldFunction(application) => self.apply_function_unfold(application),
            ProofStep::UnfoldResource(resource) => {
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_unfold(resource)
                } else {
                    self.apply_execution_resource_unfold(resource)
                }
            }
            ProofStep::FoldResource(resource) => {
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_fold(resource)
                } else {
                    self.apply_execution_resource_fold(resource)
                }
            }
            ProofStep::ConstructResource(resource) => {
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_construction(resource)
                } else {
                    Err(self.step_error("resource `construct` requires a function-outcome proof"))
                }
            }
            ProofStep::ObserveResource(resource) => {
                self.apply_execution_resource_observation(resource)
            }
            ProofStep::Choose(choice) => self.apply_fixed_state_choose(choice),
            ProofStep::Witness(witness) => self.apply_fixed_state_witness(witness),
            ProofStep::Rewrite(equality) => self.apply_rewrite(equality),
            _ => {
                Err(self
                    .step_error("this proof step has not yet migrated to the checked `Proof` API"))
            }
        }?;

        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: self.publish_checked_transition(transition)?,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth + 1,
            }),
        })
    }

    /// Applies one explicit `Have` through the same owned scope operations as
    /// a source `have` block. Each body step advances the scope's persistent
    /// child `Proof`; joining publishes only the checked proposition and
    /// retains the body's exact surface operations as provenance. A failed
    /// body leaves this immutable root untouched.
    pub(super) fn apply_have_step(
        &self,
        proposition: &ClickProposition,
        proof: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        let mut scope = self.begin_have(proposition.clone())?;
        for step in proof.steps() {
            scope = scope.apply_step(step.clone())?;
        }
        scope.join()
    }

    pub(in crate::surface::proof) fn apply_step_at(
        &self,
        step: ProofStep,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )
    }

    /// Searches for a terminal frame candidate and submits the selected
    /// Surface-operation plan directly to this Proof. Successful search returns
    /// the already-checked descendant; it does not export outcomes or check
    /// the candidate through a second semantic representation.
    pub(super) fn apply_assumption(&self) -> Result<KernelProofHandle, ClickError> {
        let context = match self.context.as_ref() {
            ProofContext::FixedState(_) => PropositionAssumptionContext::Pure,
            ProofContext::Execution(_) => PropositionAssumptionContext::Materialized,
            ProofContext::Pure(_) => PropositionAssumptionContext::Exact,
        };
        self.state
            .apply_assumption(context)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`assumption` requires a proposition goal")
                }
                PropositionCloseError::Unavailable => self.step_error(
                    "`assumption` requires the current goal as an available semantic fact",
                ),
                _ => unreachable!("kernel returned an unrelated assumption error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_normalize(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_normalize().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`normalize` requires a proposition goal")
            }
            PropositionCloseError::DoesNotNormalize => {
                self.step_error("`normalize` goal did not normalize to true")
            }
            _ => unreachable!("kernel returned an unrelated normalize error"),
        })
    }

    #[inline(never)]
    pub(super) fn apply_normalize_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<KernelProofHandle, ClickError> {
        use crate::kernel::proof::fact_reasoning::ConditionalNormalizationError;
        let premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "`normalize using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        self.state
            .apply_normalize_using(&premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`normalize` requires a proposition goal")
                }
                PropositionCloseError::ConditionalNormalization(
                    ConditionalNormalizationError::UnavailablePremise(index),
                ) => self.step_error(format!(
                    "`normalize using` premise {index} is not exactly available"
                )),
                PropositionCloseError::ConditionalNormalization(
                    ConditionalNormalizationError::UnsupportedPremise(index),
                ) => self.step_error(format!(
                    "`normalize using` premise {index} must be a consistent single condition"
                )),
                PropositionCloseError::ConditionalNormalization(
                    ConditionalNormalizationError::DoesNotNormalize,
                ) => self.step_error(
                    "`normalize using` goal did not normalize to true using the listed conditions",
                ),
                _ => unreachable!("kernel returned an unrelated normalize-using error"),
            })
    }

    #[inline(never)]
    pub(super) fn apply_arithmetic_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<KernelProofHandle, ClickError> {
        let premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "`arithmetic using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        self.state
            .apply_arithmetic(&premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`arithmetic` requires a proposition goal")
                }
                PropositionCloseError::ArithmeticPremiseUnavailable(index) => self.step_error(
                    format!("`arithmetic using` premise {index} is not exactly available"),
                ),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::UnsupportedGoal,
                ) => self.step_error(
                    "`arithmetic` requires a supported signed int32 comparison or equality goal",
                ),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::UnsupportedPremise(
                        index,
                    ),
                ) => self.step_error(format!(
                    "`arithmetic using` premise {index} is not a supported signed int32 comparison"
                )),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::GoalMayBeUndefined,
                ) => self.step_error(
                    "`arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises",
                ),
                PropositionCloseError::Arithmetic(
                    crate::kernel::proof::fact_reasoning::ArithmeticCheckError::DoesNotFollow,
                ) => self.step_error(
                    "the current goal does not follow from exactly the listed arithmetic premises",
                ),
                _ => unreachable!("kernel returned an unrelated arithmetic error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    pub(super) fn apply_intro(&self) -> Result<KernelProofHandle, ClickError> {
        self.state
            .apply_intro(|current, introduction| {
                let mut surface_bindings = current.surface_bindings.clone();
                let surface = match (introduction, current.surface.as_deref()) {
                    (PropositionIntroduction::Implication, Some(surface)) => {
                        surface_implication_parts(surface)
                            .map(|(_, consequent)| Arc::new(consequent))
                            // Definedness premises introduced by lowering are
                            // intentionally absent from Surface syntax. Keep
                            // the written goal focused while `intro` exposes
                            // one such kernel implication at a time.
                            .or_else(|| Some(Arc::new(surface.clone())))
                    }
                    (
                        PropositionIntroduction::Universal { variable },
                        Some(ClickProposition::ForAll { name, body, .. }),
                    ) => {
                        surface_bindings = surface_bindings.with_inserted(
                            name.clone(),
                            ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                                Bitvector32Term::Variable(variable),
                            ))),
                        );
                        Some(Arc::new(body.as_ref().clone()))
                    }
                    _ => None,
                };
                PropositionPresentation {
                    surface,
                    surface_bindings,
                }
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`intro` requires a proposition goal")
                }
                PropositionCloseError::ExpectedIntroduction(goal) => self.step_error(format!(
                    "`intro` requires an implication, negation, or universal goal, got {goal:?}"
                )),
                _ => unreachable!("kernel returned an unrelated intro error"),
            })
    }

    #[inline(never)]
    fn apply_induct(
        &self,
        parameter: &str,
        hypothesis: &str,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("`induct` requires a pure theorem proof"));
        };
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("`induct` is not active for this pure theorem"));
        };
        if parameter != setup.parameter || hypothesis != setup.hypothesis {
            return Err(self.step_error("induction step does not match the theorem setup"));
        }
        let expected_goal =
            self.lower_surface_proposition(&setup.surface_goal, "induction theorem goal")?;
        if self.goal() != Some(&expected_goal) {
            return Err(
                self.step_error("`induct` must be the first step of the pure theorem proof")
            );
        }
        let Some(CValue::Int32(current)) = context.theorem_context.values.get(parameter) else {
            return Err(self.step_error("induction parameter must have type int32"));
        };
        let nonnegative = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(current.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        if !self.facts().contains(&nonnegative) {
            return Err(self.step_error(format!(
                "`induct({parameter})` requires an exact nonnegative requirement"
            )));
        }
        let quantified = super::super::pure_theorems::pure_induction_hypothesis(
            setup,
            context.theorem_context,
            context.predicate_environment,
            context.click_function_environment,
        )?;
        if self.facts().contains(&quantified) {
            return Err(self.step_error("induction hypothesis was already introduced"));
        }
        let facts = self.facts().with_kernel_checked_fact(quantified.clone());
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            false,
            vec![quantified.clone()],
            vec![quantified],
        ))
    }

    #[inline(never)]
    fn apply_induction(
        &self,
        hypothesis: &str,
        argument: &ContractExpression,
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("induction application requires a pure theorem proof"));
        };
        if let Some(setup) = context.structural_induction_setup.as_ref() {
            return self.apply_structural_induction_hypothesis(
                context,
                setup,
                hypothesis,
                argument,
                surface_premises,
            );
        }
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("induction hypothesis is not active"));
        };
        if hypothesis != setup.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "induction premise"))
            .collect::<Result<Vec<_>, _>>()?;

        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let mut active_functions = BTreeSet::new();
        let value = evaluate_contract_expression_with_environment(
            &context.theorem_context.values,
            &context.theorem_context.array_refs,
            &state,
            &state,
            None,
            self.facts().assumptions(),
            argument,
            context.predicate_environment,
            context.click_function_environment,
            &RecordedSnapshots::new(),
            &mut active_functions,
        )
        .map_err(|message| {
            self.step_error(format!("could not evaluate induction argument: {message}"))
        })?;
        let CValue::Int32(argument) = value else {
            return Err(self.step_error("induction argument must have type int32"));
        };
        let quantified = super::super::pure_theorems::pure_induction_hypothesis(
            setup,
            context.theorem_context,
            context.predicate_environment,
            context.click_function_environment,
        )?;
        self.state
            .apply_instantiate(quantified, argument, &explicit_premises)
            .map(|state| {
                // `apply_instantiate` has performed the complete kernel
                // premise/order/conclusion check. Publish its exact fact
                // delta through the same Proof transition used by ordinary
                // quantified instantiation.
                let added_facts = state.state().checked_facts().to_vec();
                let mut facts = self.facts().clone();
                for fact in &added_facts {
                    facts = facts.with_kernel_checked_fact(fact.clone());
                }
                let complete = self.goal().is_some_and(|goal| facts.contains(goal));
                self.checked_fact_transition(
                    self.state().locals().clone(),
                    facts,
                    complete,
                    added_facts.clone(),
                    added_facts,
                )
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("induction application requires a proposition goal")
                }
                PropositionCloseError::InstantiatePremiseUnavailable(premise) => self.step_error(
                    format!("induction premise is not exactly available: {premise:?}"),
                ),
                PropositionCloseError::InstantiateQuantifiedUnavailable => {
                    self.step_error("induction hypothesis is not exactly available")
                }
                PropositionCloseError::InstantiateInvalid(message) => {
                    let _ = message;
                    self.step_error("kernel rejected induction application")
                }
                _ => unreachable!("kernel returned an unrelated induction error"),
            })
    }

    fn apply_structural_induction_hypothesis(
        &self,
        _context: &PureProofContext<'_>,
        setup: &PureStructuralInductionBranchSetup,
        hypothesis: &str,
        argument: &ContractExpression,
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if hypothesis != setup.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        let Some(application) = setup
            .applications
            .iter()
            .find(|candidate| candidate.argument == *argument)
        else {
            return Err(self.step_error(
                "structural induction hypothesis expects an immediate recursive field",
            ));
        };
        if surface_premises != application.surface_premises {
            return Err(self.step_error(
                "structural induction application changed its exact requirement premises",
            ));
        }
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "induction premise"))
            .collect::<Result<Vec<_>, _>>()?;
        if explicit_premises != application.kernel_premises {
            return Err(self.step_error(
                "structural induction application lowered different requirement premises",
            ));
        }
        if !self.facts().contains(&application.implication) {
            return Err(self.step_error("structural induction hypothesis is not active"));
        }
        if let Some(missing) = explicit_premises
            .iter()
            .find(|premise| !self.facts().available_across_effects(premise, &[]))
        {
            return Err(self.step_error(format!(
                "induction premise is not exactly available: {missing:?}"
            )));
        }
        if !self.facts().contains(&application.conclusion)
            && !self
                .facts()
                .contains_discharged_implication_consequent(&application.conclusion)
        {
            return Err(self.step_error("kernel rejected structural induction application"));
        }
        let added = (!self.facts().contains_top_level(&application.conclusion))
            .then(|| application.conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let mut facts = self.facts().clone();
        for fact in &added {
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            complete,
            added.clone(),
            added,
        ))
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_split(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_split().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`split` requires a proposition goal")
            }
            PropositionCloseError::ExpectedConjunction(goal) => {
                self.step_error(format!("`split` requires a conjunction goal, got {goal:?}"))
            }
            PropositionCloseError::MissingConjuncts(left, right) => self.step_error(format!(
                "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
            )),
            _ => unreachable!("kernel returned an unrelated split error"),
        })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_left(&self) -> Result<KernelProofHandle, ClickError> {
        self.apply_disjunct(true, "left")
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_right(&self) -> Result<KernelProofHandle, ClickError> {
        self.apply_disjunct(false, "right")
    }

    fn apply_disjunct(
        &self,
        take_left: bool,
        step_name: &str,
    ) -> Result<KernelProofHandle, ClickError> {
        self.state
            .apply_disjunct(take_left)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error(format!("`{step_name}` requires a proposition goal"))
                }
                PropositionCloseError::ExpectedDisjunction(goal) => self.step_error(format!(
                    "`{step_name}` requires a disjunction goal, got {goal:?}"
                )),
                PropositionCloseError::MissingDisjunct(selected) => self.step_error(format!(
                    "`{step_name}` requires its selected disjunct as an exact fact: {selected:?}"
                )),
                _ => unreachable!("kernel returned an unrelated disjunction error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above; instance
    // materialization is local to this rule.
    #[inline(never)]
    pub(super) fn apply_enumerate(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_enumerate().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`enumerate` requires a proposition goal")
            }
            PropositionCloseError::ExpectedFiniteUniversal => {
                self.step_error("`enumerate` requires a universal goal with constant bounds")
            }
            PropositionCloseError::MissingFiniteInstance => self.step_error(
                "`enumerate` requires each in-range instance as an exact available fact",
            ),
            _ => unreachable!("kernel returned an unrelated enumerate error"),
        })
    }
}

/// The kernel variable identities named in a rendered kernel value, as
/// substrings that identify them in a rendered proposition. Candidate
/// selection only; every selected premise is still checked.
fn kernel_variable_keys(rendered_value: &str) -> Vec<String> {
    let mut keys = Vec::new();
    let mut rest = rendered_value;
    while let Some(start) = rest.find("Variable(Variable(") {
        let after = &rest[start + "Variable(Variable(".len()..];
        let digits: String = after.chars().take_while(char::is_ascii_digit).collect();
        if !digits.is_empty() {
            let key = format!("Variable(Variable({digits}))");
            if !keys.contains(&key) {
                keys.push(key);
            }
        }
        rest = after;
    }
    keys
}
