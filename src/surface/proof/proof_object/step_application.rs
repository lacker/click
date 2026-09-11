//! Simple-step dispatch (`apply_step`) and checked frame application.

use super::*;
use crate::kernel::LoweringIntroduction;

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
            ProofStep::IntegerCertificate(certificate) => {
                Some(self.apply_integer_certificate(certificate))
            }
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
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, Some(ProofStepOrigin { source_index }))
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
                PropositionCloseError::Unavailable => {
                    let detail = self
                        .goal()
                        .map(|goal| format!(": current goal is {}", describe_assumption_goal(goal)))
                        .unwrap_or_default();
                    self.step_error(format!(
                        "`assumption` requires the current goal as an available semantic fact{detail}"
                    ))
                }
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
            .map(|premise| {
                self.lower_cited_surface_proposition(premise, "`normalize using` premise")
            })
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
            .map(|premise| {
                self.lower_cited_surface_proposition(premise, "`arithmetic using` premise")
            })
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

    pub(super) fn apply_integer_certificate(
        &self,
        certificate: &IntegerCertificate,
    ) -> Result<KernelProofHandle, ClickError> {
        use crate::kernel::proof::integer_arithmetic::{
            IntegerArithmeticCertificate, IntegerArithmeticNode, integer_affine_claim,
        };

        // Source premise nodes are the only way a certificate imports facts.
        // Keep their explicit indices and reject holes or conflicting duplicate
        // declarations before handing anything to the kernel checker.
        let mut source_premises = std::collections::BTreeMap::new();
        for node in &certificate.nodes {
            let IntegerCertificateNode::Premise {
                index, proposition, ..
            } = node
            else {
                continue;
            };
            let lowered =
                self.lower_integer_surface_proposition(proposition, "integer certificate premise")?;
            if let Some(previous) = source_premises.insert(*index, lowered.clone())
                && previous != lowered
            {
                return Err(self.step_error(format!(
                    "integer certificate premise {index} is declared with two different propositions"
                )));
            }
        }
        let mut premises = Vec::with_capacity(source_premises.len());
        for index in 0..source_premises.len() {
            let Some(premise) = source_premises.remove(&index) else {
                return Err(self.step_error(format!(
                    "integer certificate premise indices must be contiguous; missing {index}"
                )));
            };
            premises.push(premise);
        }

        let claim = |proof: &Self,
                     proposition: &ClickProposition,
                     description: &str,
                     preserve_constant_relation: bool| {
            let proposition = if preserve_constant_relation {
                if let Some(raw) = lower_integer_constant_comparison(proposition) {
                    raw
                } else {
                    proof.lower_integer_surface_proposition(proposition, description)?
                }
            } else {
                proof.lower_integer_surface_proposition(proposition, description)?
            };
            integer_affine_claim(&proposition).ok_or_else(|| {
                proof.step_error(format!(
                    "{description} must be a supported mathematical Integer affine proposition"
                ))
            })
        };
        let mut nodes = Vec::with_capacity(certificate.nodes.len());
        for (node_index, node) in certificate.nodes.iter().enumerate() {
            let lowered = match node {
                IntegerCertificateNode::Premise {
                    index,
                    proposition,
                    result,
                } => {
                    let supplied = premises.get(*index).ok_or_else(|| {
                        self.step_error(format!("integer certificate premise {index} is out of range"))
                    })?;
                    let declared = self.lower_integer_surface_proposition(
                        proposition,
                        "integer certificate premise",
                    )?;
                    if supplied != &declared {
                        return Err(self.step_error(format!(
                            "integer certificate premise {index} does not match its declared source proposition"
                        )));
                    }
                    IntegerArithmeticNode::Premise {
                        index: *index,
                        result: claim(
                            self,
                            result,
                            "integer certificate premise result",
                            false,
                        )?,
                    }
                }
                IntegerCertificateNode::Scale {
                    source,
                    coefficient,
                    result,
                } => IntegerArithmeticNode::Scale {
                    source: *source,
                    coefficient: integer_constant_expression(coefficient).ok_or_else(|| {
                        self.step_error(
                            "integer certificate scale coefficient must be a constant Integer expression",
                        )
                    })?,
                    result: claim(self, result, "integer certificate scale result", false)?,
                },
                IntegerCertificateNode::Add { left, right, result } => {
                    IntegerArithmeticNode::Add {
                        left: *left,
                        right: *right,
                        result: claim(self, result, "integer certificate addition result", false)?,
                    }
                }
                IntegerCertificateNode::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => IntegerArithmeticNode::EqualityToLessEqual {
                    source: *source,
                    reverse: *reverse,
                    result: claim(self, result, "integer certificate equality bound", false)?,
                },
                IntegerCertificateNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => IntegerArithmeticNode::EqualityFromBounds {
                    lower: *lower,
                    upper: *upper,
                    result: claim(self, result, "integer certificate equality", false)?,
                },
                IntegerCertificateNode::Trivial { result } => IntegerArithmeticNode::Trivial {
                    result: claim(
                        self,
                        result,
                        "integer certificate trivial result",
                        node_index != certificate.conclusion,
                    )?,
                },
            };
            if nodes.len() != node_index {
                return Err(self.step_error("integer certificate node indexing is not contiguous"));
            }
            nodes.push(lowered);
        }
        let kernel_certificate = IntegerArithmeticCertificate {
            nodes,
            conclusion: certificate.conclusion,
        };
        self.state
            .apply_integer_arithmetic(&kernel_certificate, &premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("integer certificate requires a proposition goal")
                }
                PropositionCloseError::IntegerArithmeticPremiseUnavailable(index) => self
                    .step_error(format!(
                        "integer certificate premise {index} is not exactly available"
                    )),
                PropositionCloseError::IntegerArithmetic(error) => self.step_error(format!(
                    "integer arithmetic certificate rejected: {error:?}"
                )),
                _ => unreachable!("kernel returned an unrelated integer arithmetic error"),
            })
    }

    fn lower_integer_surface_proposition(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                let mut names = BTreeSet::new();
                collect_click_proposition_referenced_names(surface, &mut names);
                let mut integer_values = context.theorem_context.integer_values.clone();
                for name in &names {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(value) = self.state().locals().integer_values.get(name) {
                        integer_values = integer_values.with_inserted(name.clone(), value.clone());
                    }
                }
                let promoted = self.proposition_obligation().map_or_else(
                    || surface.clone(),
                    |goal| {
                        crate::surface::proof::surface_lowering::promote_integer_comparison(
                            surface,
                            &integer_values,
                            &goal.surface_bindings,
                        )
                    },
                );
                if let Ok(proposition) = crate::surface::lower_integer_certificate_proposition(
                    &promoted,
                    &integer_values,
                ) {
                    return Ok(proposition);
                }
                // Mixed atoms need the ordinary checked specification lowerer.
                // Select only bindings referenced by this explicit certificate
                // node, so unrelated theorem parameters are never copied.
                let values = names
                    .iter()
                    .filter_map(|name| {
                        if integer_values.get(name).is_some() {
                            return None;
                        }
                        context
                            .theorem_context
                            .values
                            .get(name)
                            .map(|value| (name.clone(), value.clone()))
                    })
                    .collect();
                let arrays = names
                    .iter()
                    .filter_map(|name| {
                        context
                            .theorem_context
                            .array_refs
                            .get(name)
                            .map(|value| (name.clone(), value.clone()))
                    })
                    .collect();
                let algebraic = names
                    .iter()
                    .filter_map(|name| {
                        context
                            .structural_induction_setup
                            .as_ref()?
                            .algebraic_values
                            .get(name)
                            .map(|value| (name.clone(), value.clone()))
                    })
                    .collect();
                super::super::pure_theorems::lower_pure_theorem_proposition_recording_introductions(
                    context.claim_label,
                    &promoted,
                    self.facts().assumptions(),
                    &values,
                    &arrays,
                    &algebraic,
                    &integer_values,
                    &context.theorem_context.memory,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map(|(proposition, _)| proposition)
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            _ => self.lower_surface_proposition_direct(surface, description),
        }
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    pub(super) fn apply_intro(&self) -> Result<KernelProofHandle, ClickError> {
        let mut integer_binding = None;
        let state = self
            .state
            .apply_intro(|current, introduction, introduced| {
                let mut surface_bindings = current.surface_bindings.clone();
                let mut introduced_antecedents = current.introduced_antecedents.clone();
                let recorded = current.introductions.head();
                let surface = match (recorded, introduction, current.surface.as_deref()) {
                    // Lowering inserts implications that guard a body with a
                    // path fact it established or with a load obligation the
                    // state did not discharge. Neither has a Surface
                    // connective, so the written goal stays focused while
                    // `intro` exposes one such kernel implication.
                    (
                        Some(
                            LoweringIntroduction::PathFactGuard
                            | LoweringIntroduction::ObligationGuard,
                        ),
                        PropositionIntroduction::Implication,
                        Some(surface),
                    ) => Some(Arc::new(surface.clone())),
                    // A written implication consumes the written connective.
                    // The pair `intro` just checked is retained here, with
                    // its structural conjuncts, so a later citation does not
                    // re-lower the antecedent under the fact context this
                    // step changed.
                    (
                        Some(LoweringIntroduction::WrittenImplication),
                        PropositionIntroduction::Implication,
                        Some(surface),
                    ) => match written_implication_consequent(surface) {
                        Some(WrittenAntecedent::Implication {
                            antecedent,
                            consequent,
                        }) => {
                            if let Some(kernel) = introduced {
                                introduced_antecedents = retain_introduced_antecedent(
                                    &introduced_antecedents,
                                    &antecedent,
                                    kernel,
                                );
                            }
                            Some(Arc::new(consequent))
                        }
                        // A range quantifier writes no implication of its
                        // own: its kernel form is the binder followed by the
                        // range guard, whose consequent is the written body.
                        Some(WrittenAntecedent::RangeGuard { body }) => Some(Arc::new(body)),
                        None => Some(Arc::new(surface.clone())),
                    },
                    (
                        Some(LoweringIntroduction::WrittenUniversal {
                            name,
                            pointer,
                            integer,
                            ..
                        }),
                        PropositionIntroduction::Universal {
                            variable,
                            pointer: introduced_pointer,
                        },
                        surface,
                    ) => {
                        if *integer {
                            integer_binding = Some((name.clone(), variable));
                        }
                        // The binding names the exact variable the kernel
                        // bound the body to, not the one lowering first
                        // chose: `intro` freshens the binder away from
                        // ambient facts.
                        let value = match (pointer, introduced_pointer) {
                            (true, Some(c_type)) => {
                                CValue::typed_pointer(Pointer::symbolic(variable), c_type)
                            }
                            _ => CValue::Int32(Bitvector32Term::Variable(variable)),
                        };
                        if !*integer {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                ContractExpression::CFragment(CExpression::Value(value)),
                            );
                        }
                        surface.and_then(written_universal_body).map(Arc::new)
                    }
                    // No lowering provenance was recorded for this goal, so
                    // refine the written form structurally, as before.
                    (None, PropositionIntroduction::Implication, Some(surface)) => {
                        surface_implication_parts(surface)
                            .map(|(_, consequent)| Arc::new(consequent))
                            .or_else(|| Some(Arc::new(surface.clone())))
                    }
                    (
                        None,
                        PropositionIntroduction::Universal { variable, .. },
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
                    introductions: current.introductions.advanced(),
                    introduced_antecedents,
                }
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`intro` requires a proposition goal")
                }
                PropositionCloseError::ExpectedIntroduction(goal) => self.step_error(format!(
                    "`intro` requires an implication, negation, or universal goal, got {}",
                    describe_assumption_goal(&goal)
                )),
                PropositionCloseError::IntegerFresheningExhausted => {
                    self.step_error("`intro` requires a fresh Integer binder variable")
                }
                _ => unreachable!("kernel returned an unrelated intro error"),
            })?;
        if let Some((name, variable)) = integer_binding {
            let mut locals = state.locals().clone();
            locals.integer_values = locals.integer_values.with_inserted(
                name,
                crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(
                    variable,
                )),
            );
            Ok(state.with_locals(locals))
        } else {
            Ok(state)
        }
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
                PropositionCloseError::InstantiatePremiseUnavailable(premise) => {
                    self.step_error(format!(
                        "induction premise is not exactly available: {}",
                        crate::surface::proof_diagnostics::render::render_proposition(&premise)
                    ))
                }
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
                "induction premise is not exactly available: {}",
                crate::surface::proof_diagnostics::render::render_proposition(missing)
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
            PropositionCloseError::ExpectedConjunction(goal) => self.step_error(format!(
                "`split` requires a conjunction goal, got {}",
                describe_assumption_goal(&goal)
            )),
            PropositionCloseError::MissingConjuncts(left, right) => self.step_error(format!(
                "`split` requires both conjuncts as exact facts: {} and {}",
                crate::surface::proof_diagnostics::render::render_proposition(&left),
                crate::surface::proof_diagnostics::render::render_proposition(&right)
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
                    "`{step_name}` requires a disjunction goal, got {}",
                    describe_assumption_goal(&goal)
                )),
                PropositionCloseError::MissingDisjunct(selected) => self.step_error(format!(
                    "`{step_name}` requires its selected disjunct as an exact fact: {}",
                    crate::surface::proof_diagnostics::render::render_proposition(&selected)
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

fn describe_assumption_goal(goal: &Proposition) -> &'static str {
    match goal {
        Proposition::And(..) => "a conjunction",
        Proposition::Or(..) => "a disjunction",
        Proposition::Implies(..) => "an implication",
        Proposition::Not(..) => "a negation",
        Proposition::ForAll { .. } => "a universal proposition",
        Proposition::Exists { .. } => "an existential proposition",
        Proposition::CMemoryLoadable { .. } => "a memory-loadability fact",
        Proposition::ConditionIs(condition, _) => match condition {
            ConditionTerm::IntegerLessThan(..) => "an Integer less-than fact",
            ConditionTerm::IntegerLessEqual(..) => "an Integer less-or-equal fact",
            ConditionTerm::IntegerGreaterThan(..) => "an Integer greater-than fact",
            ConditionTerm::IntegerGreaterEqual(..) => "an Integer greater-or-equal fact",
            ConditionTerm::IntegerEqual(..) => "an Integer equality fact",
            ConditionTerm::IntegerNotEqual(..) => "an Integer disequality fact",
            _ => "a condition fact",
        },
        Proposition::Equal(Term::Integer(_), Term::Integer(_)) => "an Integer equality fact",
        Proposition::Equal(..) => "an equality fact",
        _ => "a proposition fact",
    }
}

/// Preserve the relation shape of an intermediate constant certificate node.
///
/// The ordinary Integer condition constructors intentionally evaluate two
/// constants immediately.  That is correct for a goal (whose checked claim
/// is then the canonical `Equal(0)` truth claim), but an intermediate
/// weakening node carries a nonzero affine constant that the arithmetic
/// certificate must validate before it is added to another claim.  Construct
/// the raw checked condition only at this certificate boundary; source
/// premise lowering continues to use the ordinary contextual lowerer.
fn lower_integer_constant_comparison(
    proposition: &ClickProposition,
) -> Option<crate::kernel::Proposition> {
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let left = crate::kernel::IntegerTerm::constant(integer_constant_expression(left)?).into();
    let right = crate::kernel::IntegerTerm::constant(integer_constant_expression(right)?).into();
    let condition = match operator {
        ComparisonOperator::Equal => crate::kernel::ConditionTerm::IntegerEqual(left, right),
        ComparisonOperator::NotEqual => crate::kernel::ConditionTerm::IntegerNotEqual(left, right),
        ComparisonOperator::LessThan => crate::kernel::ConditionTerm::IntegerLessThan(left, right),
        ComparisonOperator::LessEqual => {
            crate::kernel::ConditionTerm::IntegerLessEqual(left, right)
        }
        ComparisonOperator::GreaterThan => {
            crate::kernel::ConditionTerm::IntegerGreaterThan(left, right)
        }
        ComparisonOperator::GreaterEqual => {
            crate::kernel::ConditionTerm::IntegerGreaterEqual(left, right)
        }
        ComparisonOperator::In => return None,
    };
    Some(crate::kernel::Proposition::ConditionIs(condition, true))
}

fn integer_constant_expression(expression: &ContractExpression) -> Option<num_bigint::BigInt> {
    let literal = match expression {
        ContractExpression::IntegerLiteral(value) => value,
        ContractExpression::Negate(inner) => match inner.as_ref() {
            ContractExpression::IntegerLiteral(value) => value,
            _ => return None,
        },
        _ => return None,
    };
    if crate::instrumentation::deadline_exceeded_with_work(
        literal
            .len()
            .saturating_mul(literal.len().saturating_add(4))
            .max(1),
    ) {
        return None;
    }
    match expression {
        ContractExpression::IntegerLiteral(value) => value.parse::<num_bigint::BigInt>().ok(),
        // Keep the source coefficient grammar deliberately narrow.  Parsing
        // arbitrary arithmetic here would create a second unbounded evaluator
        // outside the checked certificate kernel.
        ContractExpression::Negate(inner) => match inner.as_ref() {
            ContractExpression::IntegerLiteral(value) => {
                value.parse::<num_bigint::BigInt>().ok().map(|value| -value)
            }
            _ => None,
        },
        _ => None,
    }
}
