//! Checked execution statement steps and loop-invariant bundles.

use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

/// Names the ranking members a ranked loop's bundle carries, so an explicit
/// `preserve by` body written before the `decreases` clause existed reports
/// what it now has to close instead of only that the bundle stayed open.
fn ranking_member_diagnostic(ranking_measures: &[CExpression]) -> String {
    if ranking_measures.is_empty() {
        return String::new();
    }
    let members = ranking_measures
        .iter()
        .map(|measure| {
            format!(
                "`0 <= {}` at the back edge",
                crate::kernel::c_ranking_measure_source(measure)
            )
        })
        .chain(std::iter::once(format!(
            "`{}` decreases at the back edge",
            crate::kernel::c_ranking_measures_source(ranking_measures)
        )))
        .collect::<Vec<_>>();
    format!(
        "; this loop declares `decreases`, so the bundle also has {}",
        members.join(", ")
    )
}

/// A premise the bundle closer may hand to `arithmetic() using`, as the
/// exact pair of lowered kernel proposition and the source text that lowers
/// to it. Only the loop head's guard and invariants at iteration entry and
/// the function's written preconditions ever become one of these.
pub(in crate::surface::proof) type NamedArithmeticPremise = (Proposition, ClickProposition);

/// Splits a written contract clause into the conjuncts a source proof would
/// cite one at a time. The walk is over the written proposition only; it
/// reads no fact context.
fn written_conjuncts(surface: &ClickProposition, collected: &mut Vec<ClickProposition>) {
    match surface {
        ClickProposition::And(left, right) => {
            written_conjuncts(left, collected);
            written_conjuncts(right, collected);
        }
        _ => collected.push(surface.clone()),
    }
}

impl<'a> Proof<'a> {
    /// The named premises a smart bundle closure may cite for a ranking
    /// member: the loop guard and the declared invariants, both read at
    /// iteration entry, then the function's written preconditions.
    ///
    /// The candidate list is exactly what the loop head and the contract
    /// name. A candidate is kept only when it lowers here, is exactly
    /// available, and is a premise the arithmetic checker supports, so the
    /// work is one indexed lookup and one classification per named clause and
    /// does not grow with unrelated ambient facts.
    fn named_arithmetic_premises(
        &self,
        bundle: &InvariantBodyContext,
        requires: &[Requirement],
    ) -> Vec<NamedArithmeticPremise> {
        let trivial = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true);
        let mut candidates = bundle.loop_head_premises.clone();
        for requirement in requires {
            if let Some(proposition) = requirement.proposition() {
                written_conjuncts(proposition, &mut candidates);
            }
        }
        let mut cited = Vec::new();
        for surface in candidates {
            let Ok(lowered) =
                self.lower_cited_surface_proposition(&surface, "loop closure premise")
            else {
                continue;
            };
            if !self.facts().exact_available_across_effects(&lowered, &[]) {
                continue;
            }
            // The premise classification is the checker's own: a clause it
            // would reject as unsupported must not be cited, or one unusable
            // premise would lose the whole candidate.
            if crate::kernel::proof::fact_reasoning::check_signed_affine_arithmetic(
                &trivial,
                std::slice::from_ref(&lowered),
            )
            .is_err()
            {
                continue;
            }
            // Two written spellings of one clause can lower to the same fact
            // here. Cite it once: a repeated premise is checked again for no
            // gain and prints as noise in the expansion.
            if cited
                .iter()
                .any(|(existing, _): &NamedArithmeticPremise| existing == &lowered)
            {
                continue;
            }
            cited.push((lowered, surface));
        }
        cited
    }

    /// Closes the back-edge bundle by descending its fixed structure.
    ///
    /// The bundle is a right-nested conjunction of members, and a tuple
    /// measure's decrease member is a right-nested disjunction over pivots.
    /// This planner therefore tries only checked structural operations over
    /// the bundle's fixed shape (`both` and `intro`), `left`/`right` over a
    /// pivot disjunction, and at a member one `arithmetic() using` step over
    /// the named premises above or the ordinary smart closer. Every
    /// candidate advances this same `Proof`, so the retained certificate is
    /// the explicit proof `click expand` prints and re-verifies.
    pub(in crate::surface::proof) fn plan_invariant_bundle_closure(
        &self,
        premises: &[NamedArithmeticPremise],
    ) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("loop invariant bundle closure");
        check_verification_deadline()?;
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        // The generated invariant bundle can have no Surface spelling. Its
        // conjunction and implication structure is nevertheless checked by
        // the kernel, so descend that structure directly and retain the
        // ordinary Both/Intro certificate nodes.
        if matches!(goal, Proposition::And(_, _)) {
            let (split_proof, split, ids) = self.split_focused_both()?;
            let marker = split_proof.checkpoint();
            let Some(left) = split_proof
                .focus_branch(ids[0])?
                .plan_invariant_bundle_closure(premises)?
            else {
                return Ok(None);
            };
            let Some(right) = left
                .focus_branch(ids[1])?
                .plan_invariant_bundle_closure(premises)?
            else {
                return Ok(None);
            };
            let result = attempt::candidate_outcome(right.join_focused_both(&marker, split, ids));
            if matches!(&result, Ok(Some(_))) {
                scope.succeed();
            }
            return result;
        }
        if matches!(goal, Proposition::Implies(_, _)) {
            let Some(introduced) = attempt::candidate_outcome(self.apply_step(ProofStep::Intro))?
            else {
                return Ok(None);
            };
            let result = introduced.plan_invariant_bundle_closure(premises)?;
            if result.is_some() {
                scope.succeed();
            }
            return Ok(result);
        }
        let surface_goal = self.surface_goal().cloned();
        if matches!(goal, Proposition::Or(_, _))
            && let Some(surface_goal) = surface_goal.as_ref()
            && let Some((surface_left, surface_right)) =
                crate::surface::proof::surface_certificates::surface_logical_children(
                    surface_goal,
                    false,
                )
        {
            for (surface, closer) in [
                (surface_left, ProofStep::Left),
                (surface_right, ProofStep::Right),
            ] {
                let selected = (|| {
                    let Some(scope) = attempt::candidate_outcome(self.begin_have(surface))? else {
                        return Ok(None);
                    };
                    let Some(scope) = scope.plan_invariant_bundle_closure(premises)? else {
                        return Ok(None);
                    };
                    let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                        return Ok(None);
                    };
                    attempt::candidate_outcome(joined.apply_step(closer))
                })();
                if let Some(selected) = selected? {
                    scope.succeed();
                    return Ok(Some(selected));
                }
            }
            return Ok(None);
        }
        let result = self.close_bundle_member(premises)?;
        if result.is_none() {
            // Keep one bounded, lazy diagnostic for the actual kernel leaf.
            // The enclosing closure may try several ordinary candidates, so
            // this is recorded only after every checked leaf operation has
            // declined; it does not turn a miss into an error.
            let diagnostic = self.step_error("checked loop invariant bundle leaf remained open");
            attempt::record_unclosed_goal("loop invariant bundle leaf", &diagnostic);
        }
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// One bundle member. The arithmetic candidate is tried first: its
    /// admission test is the kernel's own affine checker over the named
    /// premise list, so a miss costs one pass over that list rather than a
    /// search. The ordinary smart closer answers every other member.
    fn close_bundle_member(
        &self,
        premises: &[NamedArithmeticPremise],
    ) -> Result<Option<Self>, ClickError> {
        if !premises.is_empty()
            && let Some(goal) = self.goal()
        {
            let kernels = premises
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            if crate::kernel::proof::fact_reasoning::check_signed_affine_arithmetic(goal, &kernels)
                .is_ok()
            {
                let cited = premises
                    .iter()
                    .map(|(_, surface)| surface.clone())
                    .collect::<Vec<_>>();
                if let Some(closed) =
                    attempt::candidate_outcome(self.apply_step(ProofStep::ArithmeticUsing(cited)))?
                {
                    return Ok(Some(closed));
                }
            }
        }
        self.try_simp_closure()
    }

    pub(super) fn apply_execution_statement_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_execution_statement_step_with_policy(
            step,
            StatementPrerequisitePolicy::Contextual,
        )
    }

    pub(in crate::surface::proof) fn apply_execution_statement_step_with_policy(
        &self,
        step: ProofStep,
        prerequisite_policy: StatementPrerequisitePolicy,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        let selected_environment;
        let selected_context;
        let context = if let ProofStep::StepContract(application) = &step {
            let name = &application.name;
            if context
                .function_environment
                .get_function_contract(name)
                .is_none()
            {
                return Err(self.step_error(format!("unknown call contract `{name}`")));
            }
            let definition = context
                .predicate_environment
                .contract_definition(name)
                .ok_or_else(|| self.step_error(format!("unknown call contract `{name}`")))?;
            let parameters = definition.proof_parameters.as_deref().unwrap_or(&[]);
            if definition.proof_parameters.is_some() && application.arguments.is_none() {
                return Err(self.step_error(format!(
                    "contract `{name}` requires explicit application syntax: `{name}(...)`"
                )));
            }
            let arguments = application.arguments.as_deref().unwrap_or(&[]);
            if arguments.len() != parameters.len() {
                return Err(self.step_error(format!(
                    "contract `{name}` expects {} proof argument(s), got {}",
                    parameters.len(),
                    arguments.len()
                )));
            }
            let mut identities = BTreeSet::new();
            for (parameter, argument) in parameters.iter().zip(arguments) {
                let ResourceClause::Named { binding, resource } = parameter else {
                    unreachable!()
                };
                let ResourceClause::Declared { name: expected, .. } = resource.as_ref() else {
                    unreachable!()
                };
                if argument.resource_name != *expected {
                    return Err(self.step_error(format!(
                        "contract `{name}` parameter `{}` expects resource `{expected}`, got `{}`",
                        binding.name, argument.resource_name
                    )));
                }
                if !identities.insert(argument.identity) {
                    return Err(self.step_error(
                        "an exclusive instance cannot supply two contract proof parameters",
                    ));
                }
            }
            selected_environment = context
                .function_environment
                .clone()
                .with_selected_call_contract(name)
                .with_selected_call_resource_arguments(
                    arguments.iter().map(|argument| argument.identity).collect(),
                );
            selected_context = context.with_loop_binding(
                context.function_block,
                context.function,
                &selected_environment,
            );
            &selected_context
        } else if let ProofStep::StepCall(transport) = &step {
            let callee = transport.callee();
            // One lookup per written entry builds the whole binding; the
            // kernel consults nothing else at this call.
            let mut bindings = BTreeMap::new();
            for binding in transport.binders().iter().chain(transport.produced()) {
                crate::instrumentation::record_deterministic_work(1);
                if bindings
                    .insert(binding.binder_identity(), binding.identity())
                    .is_some()
                {
                    return Err(self.step_error(format!(
                        "duplicate binder `{}` in the call map",
                        binding.binder()
                    )));
                }
            }
            selected_environment = context
                .function_environment
                .clone()
                .with_selected_call_binders(callee, transport.arguments().len(), bindings);
            selected_context = context.with_loop_binding(
                context.function_block,
                context.function,
                &selected_environment,
            );
            &selected_context
        } else {
            context
        };
        self.require_execution_frontier("`step`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // Every statement step executes in the whole proof context.
        let fact_context = Some(self.facts().assumptions());
        let checked = if matches!(prerequisite_policy, StatementPrerequisitePolicy::Contextual) {
            check_statement_step(&mut execution, context, self.facts(), fact_context)?
        } else {
            check_statement_step_with_policy(
                &mut execution,
                context,
                self.facts(),
                fact_context,
                prerequisite_policy,
            )?
        };
        let mut checked = checked;
        // A fact the statement introduces (a callee's `ensures`, a store's
        // value) is recorded under its readable spelling at the successor
        // state, so a later premise can name it without re-lowering it against
        // another memory. Output-sized work: one synthesis per introduced
        // fact.
        for fact in &checked.added_facts {
            if let Some(surface) = synthesize_surface_proposition(
                fact,
                context.parsed_function.parameters(),
                context.arguments,
                &checked.execution.core.state,
            ) {
                // At a call successor, a synthesized `old(...)` names the
                // callee's entry snapshot, while the same surface syntax in
                // the caller names the caller's function entry. Do not cache
                // that ambiguous spelling as caller provenance. Explicit
                // Snapshot-qualified forms (including proof marks) retain the exact
                // call-frontier identity needed to name such a fact later.
                if proposition_contains_old_expression(&surface) {
                    continue;
                }
                let _ = checked
                    .execution
                    .presentation
                    .surface_propositions
                    .record_lowering(&surface, fact);
            }
        }
        let added_facts = checked.added_facts;
        let state = self
            .state
            .publish_checked_frontier_transition(
                checked.facts,
                checked.execution,
                added_facts.clone(),
                added_facts,
            )
            .map_err(|error| self.execution_update_error("`step`", error))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth + 1,
            }),
        })
    }

    pub(super) fn apply_execution_mark(&self, name: &str) -> Result<KernelProofHandle, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`mark`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let mut presentation = execution.presentation.clone();
        let selector = SnapshotSelector::Mark(name.to_string());
        if presentation.recorded_snapshots.contains_key(&selector) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        presentation
            .recorded_snapshots
            .insert(selector, (*execution.core.state).clone());
        self.state
            .replace_frontier_presentation(presentation)
            .map_err(|error| self.execution_update_error("`mark`", error))
    }

    /// Check the written proof immediately against the exact lowered goals.
    /// The kernel owns the scope and retains its completed proof as bound
    /// closure evidence; finalization validates it without reproving it.
    pub(in crate::surface::proof) fn apply_close_invariants_body(
        &self,
        body: &[ProofTactic],
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`close_invariants by`")?;
        if body.is_empty() {
            return Err(self.step_error("`close_invariants by` requires a nonempty proof body"));
        }
        if !self.is_at_region_boundary() {
            return Err(self.step_error("`close_invariants by` requires the loop back edge"));
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`close_invariants by` requires a loop proof"));
        };
        let Some(bundle) = context.constants.invariant_body_context.as_deref() else {
            return Err(self.step_error("`close_invariants by` requires a loop invariant context"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("missing loop execution state"))?;
        if execution.core.region_invariants_close_requested {
            return Err(
                self.step_error("the invariant bundle was closed more than once on one path")
            );
        }
        let (state, scope) = self
            .state
            .open_invariant_body(
                &bundle.loop_entry_state,
                &bundle.iteration_entry_state,
                &bundle.checks,
                &bundle.ranking_measures,
                &bundle.binders,
                |goal, introductions| {
                    let both_children = if introductions.len() == 2
                        && bundle.checks.len() == 2
                        && bundle.declared_invariant_surfaces.len() == 2
                    {
                        match goal {
                            Proposition::And(left, right) => Some(std::sync::Arc::new([
                                BothChildPresentation {
                                    kernel: left.as_ref().clone(),
                                    surface: bundle.declared_invariant_surfaces.first().cloned(),
                                    introductions: introductions[0]
                                        .clone()
                                        .unwrap_or_else(|| std::sync::Arc::new(Vec::new())),
                                },
                                BothChildPresentation {
                                    kernel: right.as_ref().clone(),
                                    surface: bundle.declared_invariant_surfaces.get(1).cloned(),
                                    introductions: introductions[1]
                                        .clone()
                                        .unwrap_or_else(|| std::sync::Arc::new(Vec::new())),
                                },
                            ])),
                            _ => None,
                        }
                    } else {
                        None
                    };
                    PropositionPresentation {
                        surface: crate::surface::proof::surface_synthesis::synthesize_surface_proposition_at_entry_post_and_snapshot(
                            goal,
                            context.parsed_function.parameters(),
                            context.arguments,
                            context.old_reference_state(&execution.core.frontier, &execution.core.state),
                            &execution.core.state,
                            bundle
                                .iteration_entry_selector
                                .as_ref()
                                .map(|selector| (&bundle.iteration_entry_state, selector)),
                        )
                        .map(Arc::new),
                        surface_bindings: PersistentMap::default(),
                        both_children,
                    ..PropositionPresentation::default()
                    }
                },
            )
            .map_err(|message| self.step_error(message))?;
        let root = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
        };
        let mut search = attempt::search_scope("close invariants body");
        let checkpoint = root.checkpoint();
        let attempted = match root.try_authoritative_linear_script(body) {
            Ok(attempted) => attempted,
            Err(error) => {
                let detail = ranking_member_diagnostic(&bundle.ranking_measures);
                let error = if detail.is_empty() {
                    error
                } else {
                    error.with_context(detail)
                };
                return Err(error.with_search_failures(search.finish()));
            }
        };
        // A smart closure request is the one body this planner owns:
        // `close_invariants()`, `close_invariants by { simp(); }`, the omitted
        // preservation body, and the region `simp()` all reach here as the
        // single `simp` script. When the ordinary closer declines it, descend
        // the bundle's own structure and offer each member the loop head's and
        // the contract's named arithmetic premises.
        let attempted = match attempted {
            Some(completed) => Some(completed),
            None if body == [ProofTactic::Simp] => {
                let premises =
                    root.named_arithmetic_premises(bundle, context.function_block.requires());
                match root.plan_invariant_bundle_closure(&premises) {
                    Ok(result) => result,
                    Err(error) => return Err(error.with_search_failures(search.finish())),
                }
            }
            None => None,
        };
        let Some(completed) = attempted else {
            let error = root.step_error(format!(
                "closure body did not prove every invariant obligation{}",
                ranking_member_diagnostic(&bundle.ranking_measures)
            ));
            return Err(error.with_search_failures(search.finish()));
        };
        search.succeed();
        let certificate = completed.certificate_since(&checkpoint)?;
        let state = self
            .state
            .retain_invariant_body(scope, &completed.state)
            .map_err(|message| self.step_error(message))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(ProofStep::CloseInvariantsBy(Box::new(
                    certificate,
                )))),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth + 1,
            }),
        })
    }

    pub(super) fn execution_update_error(
        &self,
        operation: &str,
        error: ExecutionUpdateError,
    ) -> ClickError {
        match error {
            ExecutionUpdateError::NotFrontier => self.step_error(format!(
                "{operation} cannot advance C execution inside a proposition proof"
            )),
            ExecutionUpdateError::MissingExecution => {
                self.step_error("execution-frontier proof lost its semantic state")
            }
            ExecutionUpdateError::NotLoopBody => {
                self.step_error("`close_invariants` is only available in a loop-region proof")
            }
            ExecutionUpdateError::InvariantsAlreadyClosed => {
                self.step_error("the invariant bundle was closed more than once on one path")
            }
        }
    }

    /// Checks the heap, resource, and counted-population components at this
    /// loop-state join using the Proof-owned state and facts.
    pub(in crate::surface::proof) fn check_loop_state_join(
        &self,
        loop_entry_state: &CState,
        loop_head_state: &CState,
        condition: &CExpression,
        invariant_checks: &[CLoopInvariantCheck],
        binders: &[crate::kernel::CLoopBinder],
        composite_resource_definitions: &[CCompositeResourceDefinition],
    ) -> Result<(), ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("loop state join requires an execution proof"));
        }
        self.require_execution_frontier("loop state join")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop state join lost its execution state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("loop state join requires a loop-region proof"));
        }
        let mut closer_facts = self.facts().to_vec();
        closer_facts.extend(
            execution
                .core
                .effect_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        closer_facts.extend(crate::kernel::certified_store_equations(
            &execution.core.effect_facts,
        ));
        let assumptions = assumptions_from_propositions(&closer_facts);
        // The back edge binds the loop's names again before anything reads
        // them: whatever the body called the instance it ends holding, the
        // binder names it, and a body that ends with no instance at those
        // arguments fails here by name.
        let back_edge_state = crate::kernel::c_loop_state_with_loop_binders_rebound(
            loop_head_state,
            &execution.core.state,
            binders,
            &assumptions,
        )
        .map_err(|message| self.step_error(format!("loop state join: {message}")))?;
        let invariant_obligations = crate::kernel::c_loop_invariant_obligations_at_back_edge(
            &back_edge_state,
            loop_entry_state,
            invariant_checks,
            &assumptions,
        )
        .map_err(|message| self.step_error(format!("loop invariant classification: {message}")))?;
        closer_facts.extend(
            invariant_obligations
                .into_iter()
                .map(|obligation| obligation.proposition().clone()),
        );
        let assumptions = assumptions_from_propositions(&closer_facts);
        if !crate::kernel::c_loop_condition_may_continue(&back_edge_state, condition, &assumptions)
            .map_err(|message| {
                self.step_error(format!("loop condition classification: {message}"))
            })?
        {
            return Ok(());
        }
        // Heap lifetime and resource ownership are compared against the head
        // the body actually started from. That is the loop entry context for
        // an ordinary loop, and the loop's own narrower resource context when
        // the loop declares `owns` or `views` clauses of its own. A binder's
        // model is what its invariants constrain, so the ownership comparison
        // sets it aside; the invariant obligations above checked it.
        crate::kernel::c_loop_state_components_match_at_back_edge(
            loop_head_state,
            &crate::kernel::c_loop_state_with_head_binder_models(
                &back_edge_state,
                loop_head_state,
                binders,
            ),
            &assumptions,
            composite_resource_definitions,
        )
        .map_err(|message| self.step_error(format!("loop state join: {message}")))
    }

    /// Prepare complete back-edge lowering evidence for the loop planner.
    /// `None` denotes a checked do-while exit with no continuing back edge.
    ///
    /// An exact completed closure body supplies both value and safety
    /// evidence. Automatic preservation plans that body through checked
    /// Surface operations; existing evidence is validated without discovery.
    /// Ordinary value facts alone do not replace the lowering's safety evidence.
    pub(in crate::surface::proof) fn prepare_loop_invariant_bundle(
        &self,
        loop_entry_state: &CState,
        loop_head_state: &CState,
        condition: &CExpression,
        invariant_checks: &[CLoopInvariantCheck],
        ranking_measures: &[CExpression],
        invariant_surfaces: &[ClickProposition],
        binders: &[crate::kernel::CLoopBinder],
        composite_resource_definitions: &[CCompositeResourceDefinition],
        do_while: bool,
    ) -> Result<Option<Self>, ClickError> {
        self.check_loop_state_join(
            loop_entry_state,
            loop_head_state,
            condition,
            invariant_checks,
            binders,
            composite_resource_definitions,
        )?;
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("loop invariant closure requires an execution proof"));
        }
        self.require_execution_frontier("loop invariant closure")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop invariant closure lost its execution state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("loop invariant closure requires a loop-region proof"));
        }

        if do_while {
            let mut closer_facts = self.facts().to_vec();
            closer_facts.extend(
                execution
                    .core
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            closer_facts.extend(crate::kernel::certified_store_equations(
                &execution.core.effect_facts,
            ));
            let condition_may_continue = crate::kernel::c_loop_condition_may_continue(
                &execution.core.state,
                condition,
                &assumptions_from_propositions(&closer_facts),
            )
            .map_err(|message| {
                self.step_error(format!("loop condition classification: {message}"))
            })?;
            if !condition_may_continue {
                return Ok(None);
            }
        }
        if invariant_surfaces.len() != invariant_checks.len() {
            return Err(self.step_error(
                "explicit invariant evidence does not align with the invariant bundle",
            ));
        }
        let proof = if execution.core.checked_invariant_lowerings.is_some() {
            self.clone()
        } else {
            self.apply_close_invariants_body(&[ProofTactic::Simp])?
        };
        proof.validate_loop_invariant_bundle(invariant_checks, ranking_measures)?;
        Ok(Some(proof))
    }

    /// Consume the complete prepared bundle without lowering or proof search.
    pub(in crate::surface::proof) fn validate_loop_invariant_bundle(
        &self,
        invariant_checks: &[CLoopInvariantCheck],
        ranking_measures: &[CExpression],
    ) -> Result<(), ClickError> {
        self.state
            .validate_checked_invariant_lowerings(invariant_checks, ranking_measures)
            .map_err(|message| self.step_error(message))
    }

    /// Record closure only after validating the exact retained evidence.
    ///
    /// The retained evidence is created by `retain_invariant_body`, which also
    /// requests the frontier's closure, so a validated bundle is always an
    /// already-closed one. Certification therefore adds no proof step of its
    /// own: the bundle's certificate step is the `close_invariants by` node
    /// carrying the checked body, never a bare closure request that no
    /// explicit proof could spell.
    pub(in crate::surface::proof) fn certify_loop_invariant_bundle(
        &self,
        invariant_checks: &[CLoopInvariantCheck],
        ranking_measures: &[CExpression],
    ) -> Result<Self, ClickError> {
        self.validate_loop_invariant_bundle(invariant_checks, ranking_measures)?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop invariant closure lost its execution state"))?;
        if execution.core.region_invariants_close_requested {
            Ok(self.clone())
        } else {
            Err(self.step_error(
                "the loop invariant bundle carries checked body evidence without a closed frontier",
            ))
        }
    }

    /// Splits the focused branch preservation frontier under a proof-level `if`,
    /// introducing each arm's case assumption through the one shared
    /// case-assumption law, so lowered spellings, recorded surface
    /// propositions, and feasibility match the checked form exactly.
    /// Infeasible arms are omitted; the returned slots align `[then, else]`.
    /// Sibling arms stay separate — a preservation path never rejoins across
    /// the back edge — so no join consumes this split.
    pub(in crate::surface::proof) fn split_preservation_case(
        &self,
        condition: &ClickProposition,
        tactic_index: usize,
    ) -> Result<(Self, [Option<BranchId>; 2]), ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a preservation `if` requires an execution proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("proof `if`")?;
        let mut base_execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // A mid-execution case condition may name the current statement's
        // entry snapshot before any step has crossed it; record it so the
        // form lowers, exactly as the checked `if` did.
        record_current_statement_entry(
            &base_execution.core.frontier,
            &mut base_execution.presentation.recorded_snapshots,
            &base_execution.core.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            tactic_index,
            "if",
        )?;
        let mut arms: [Option<(ProofFacts, ExecutionProofState, Vec<Proposition>)>; 2] =
            [None, None];
        for value in [true, false] {
            let mut arm_execution = base_execution.clone();
            let mut arm_facts = self.facts().to_vec();
            let base_facts = arm_facts.len();
            let feasible = introduce_proof_case_assumption(
                &mut arm_execution,
                &tactic_context,
                &mut arm_facts,
                base_execution.core.has_structured_branch_history,
                condition,
                value,
            )?;
            if !feasible {
                continue;
            }
            // Record where this proof-level case split sits in the path's
            // surface record, exactly as the checked form recorded it.
            if arm_execution.presentation.surface_record.blocker.is_none() {
                // The split sits after the Proof's own top-level steps: surface
                // synthesis splits sibling paths at this offset, so it is
                // measured on the checked derivation, not a mirrored record.
                let tactic_offset = self.certificate().steps().len();
                arm_execution
                    .presentation
                    .surface_record
                    .path_choices
                    .push(SurfacePathChoice {
                        occurrence: tactic_index,
                        condition: condition.clone(),
                        value,
                        tactic_offset,
                    });
            }
            let added = arm_facts[base_facts..].to_vec();
            let mut facts = self.facts().clone();
            for fact in &added {
                facts = facts.with_kernel_checked_fact(fact.clone());
            }
            arms[usize::from(!value)] = Some((facts, arm_execution, added));
        }
        match arms {
            [
                Some((then_facts, then_execution, then_added)),
                Some((else_facts, else_execution, else_added)),
            ] => {
                let split = self
                    .state
                    .publish_checked_frontier_split(
                        [(then_facts, then_execution), (else_facts, else_execution)],
                        [then_added, else_added],
                        Vec::new(),
                    )
                    .map_err(|error| self.execution_update_error("proof `if`", error))?;
                let (state, _, ids, _) = split.into_parts_with_facts();
                let successor = Self {
                    site: self.site.clone(),
                    context: self.context.clone(),
                    state,
                    node: Arc::new(ProofNode {
                        parent: Some(self.node.clone()),
                        step: None,
                        focused_branch: self.focused_branch_id(),
                        depth: self.node.depth,
                    }),
                };
                Ok((successor, [Some(ids[0]), Some(ids[1])]))
            }
            [then_arm, else_arm] => {
                let (value, (facts, execution, added)) = if let Some(arm) = then_arm {
                    (true, arm)
                } else if let Some(arm) = else_arm {
                    (false, arm)
                } else {
                    return Err(self.step_error(
                        "no feasible arm exists for this preservation `if` condition",
                    ));
                };
                let state = self
                    .state
                    .publish_checked_frontier_transition(facts, execution, added, Vec::new())
                    .map_err(|error| self.execution_update_error("proof `if`", error))?;
                let successor = Self {
                    site: self.site.clone(),
                    context: self.context.clone(),
                    state,
                    node: self.node.clone(),
                };
                let mut ids = [None, None];
                ids[usize::from(!value)] = Some(successor.focused_branch_id());
                Ok((successor, ids))
            }
        }
    }

    /// The planner fallback for a preservation smart `step`: a scratch
    /// planning pass constructs the explicit checked operations for the
    /// current statement, and this Proof applies exactly those operations.
    /// Mirrors the checked smart-step law, including its failure wording.
    pub(in crate::surface::proof) fn apply_planned_smart_step(
        &self,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("smart `step` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`step`")?;
        let execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let claim_label = context.claim_label;
        let mut planning = execution.clone();
        planning.planned_statement_transitions.clear();
        let facts_vec = self.facts().to_vec();
        planning.surface_record.certificate_facts = ProofFactStore::from_ordered(facts_vec.clone());
        let mut sink = ProofCertificateBuilder {
            last_step_entry: execution
                .presentation
                .surface_record
                .last_step_entry
                .clone(),
            ..ProofCertificateBuilder::default()
        };
        let mut planning_facts = facts_vec;
        let assumptions = assumptions_from_propositions(&planning_facts);
        execute_step_from_frontier_position(
            &mut planning,
            &tactic_context,
            &mut planning_facts,
            &assumptions,
            "step",
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
            Some(Construction {
                environments: ConstructionEnvironments {
                    predicate_environment: context.predicate_environment,
                    click_function_environment: context.click_function_environment,
                },
                sink: &mut sink,
            }),
        )?;
        let construction = sink;
        if construction.blocker.is_none()
            && !construction.steps.is_empty()
            && construction.steps.iter().all(|step| {
                matches!(
                    step,
                    ProofStep::Have { .. }
                        | ProofStep::UnfoldPredicate(_)
                        | ProofStep::UnfoldFunction(_)
                        | ProofStep::TransportUsing { .. }
                        | ProofStep::Step
                )
            })
            && construction
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Step))
        {
            let mut proof = self.clone();
            for step in &construction.steps {
                proof = proof.apply_step(step.clone())?;
            }
            let (proof, ()) = proof.edit_execution_presentation(|presentation| {
                presentation.surface_record.last_step_entry = construction.last_step_entry;
            })?;
            return Ok(proof);
        }
        if let Some(blocker) = construction.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart `step` could not construct checked Proof operations: {blocker}"
            )));
        }
        Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart `step` found no checked Proof candidate"
        )))
    }

    /// The planner fallback for a smart `execute`: a scratch planning pass
    /// constructs the explicit checked operations for the remaining
    /// execution (a linear sequence, or a planned `if` tree for
    /// whole-function branches), and this Proof applies exactly those
    /// operations. This is the one smart-execute planner law: the source
    /// interpreter reports its errors directly, while the direct driver
    /// treats any error as a decline.
    /// The one mid-execution `transport` premise law, shared by the drivers:
    /// the source and target are lowered at the frontier, the premise
    /// planner names the premises, and this Proof applies the explicit
    /// `transport using` transition. The planner's failure is the answer,
    /// with its diagnostic.
    pub(in crate::surface::proof) fn apply_planned_fact_transport(
        &self,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`transport` requires an execution-frontier proof"));
        };
        let claim_label = context.claim_label;
        let premises = {
            let view = self.execution_view()?;
            let (state, frontier, facts) = (view.state, view.frontier, &view.facts);
            if frontier.is_at_function_entry() || frontier.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one completed execution step"
                )));
            }
            let assumptions = assumptions_from_propositions(facts);
            let pre_state = view.context.old_reference_state(frontier, state);
            let source = lower_fixed_state_proposition(
                surface_source,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                state,
                None,
                &view.execution.presentation.recorded_snapshots,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if assumptions.derive_proposition(&source).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        facts,
                        state.resources().facts(),
                        context.parsed_function.parameters(),
                        context.arguments,
                        &view.execution.core.effect_facts,
                    )
                )));
            }
            let target = lower_fixed_state_proposition(
                surface_target,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                state,
                None,
                &view.execution.presentation.recorded_snapshots,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = super::super::cursor_execution::fact_transport_transition_facts(
                &view.execution.core.effect_facts,
                &source,
            );
            plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                facts,
                &transition_facts,
                context.parsed_function.parameters(),
                context.arguments,
                view.execution.view(view.context),
                state,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: {}",
                    fact_transport_planning_failure(
                        surface_source,
                        surface_target,
                        view.unfolded_predicates,
                        &error,
                    )
                ))
            })?
        };
        self.apply_step(ProofStep::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        })
    }

    /// The one `execute_until` planner law, shared by the drivers: the
    /// planner constructs the explicit checked operations from a scratch
    /// copy of the frontier, and this Proof applies exactly those operations,
    /// recording them as the tactic's surface. The planner's failure is the
    /// answer.
    pub(in crate::surface::proof) fn apply_planned_execute_until(
        &self,
        region_ref: &CodeRegionRef,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`execute_until` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        let claim_label = context.claim_label;
        let code_region = super::super::structural::resolve_code_region_ref(
            context.function_block,
            region_ref,
            claim_label,
            tactic_index,
        )?;
        let CodeRegion::Statement(target_statement_index) = code_region else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until` expects a statement region"
            )));
        };
        let (mut planning, mut planning_facts, mut sink) = {
            let view = self.execution_view()?;
            let mut planning = self.execution().cloned().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
            planning.planned_statement_transitions.clear();
            planning.surface_record.certificate_facts =
                ProofFactStore::from_ordered(view.facts.clone());
            let sink = ProofCertificateBuilder {
                last_step_entry: view
                    .execution
                    .presentation
                    .surface_record
                    .last_step_entry
                    .clone(),
                ..ProofCertificateBuilder::default()
            };
            (planning, view.facts, sink)
        };
        super::super::cursor_execution::execute_until_statement(
            &mut planning,
            &tactic_context,
            &mut planning_facts,
            target_statement_index,
            StatementPrerequisitePolicy::Planning,
            Some(Construction {
                environments: ConstructionEnvironments {
                    predicate_environment: context.predicate_environment,
                    click_function_environment: context.click_function_environment,
                },
                sink: &mut sink,
            }),
        )?;
        let construction = sink;
        if construction.blocker.is_none()
            && !construction.steps.is_empty()
            && construction.steps.iter().all(|step| {
                matches!(
                    step,
                    ProofStep::Have { .. }
                        | ProofStep::UnfoldPredicate(_)
                        | ProofStep::UnfoldFunction(_)
                        | ProofStep::TransportUsing { .. }
                        | ProofStep::Step
                )
            })
            && construction
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Step))
        {
            let mut executed = self.clone();
            for step in &construction.steps {
                executed = executed.apply_step(step.clone())?;
            }
            let (recorded, ()) = executed.edit_execution_presentation(|presentation| {
                presentation.surface_record.last_step_entry = construction.last_step_entry;
            })?;
            Ok(recorded)
        } else if let Some(blocker) = construction.blocker {
            Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until` could not construct checked Proof operations: {blocker}"
            )))
        } else {
            Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until` found no checked Proof candidate"
            )))
        }
    }

    pub(in crate::surface::proof) fn apply_planned_smart_execute(
        &self,
        force_all_paths: bool,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("smart `execute` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        let claim_label = context.claim_label;
        self.require_execution_frontier("`execute`")?;
        let execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let facts_vec = self.facts().to_vec();
        let planning_sink = || ProofCertificateBuilder {
            last_step_entry: execution
                .presentation
                .surface_record
                .last_step_entry
                .clone(),
            ..ProofCertificateBuilder::default()
        };
        let construction_environments = ConstructionEnvironments {
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
        };
        let mut planning = execution.clone();
        planning.planned_statement_transitions.clear();
        planning.surface_record.certificate_facts = ProofFactStore::from_ordered(facts_vec.clone());
        let mut sink = planning_sink();
        let mut planning_facts = facts_vec.clone();
        let direct_result = (!force_all_paths).then(|| {
            execute_rest_from_frontier_position(
                &mut planning,
                &tactic_context,
                &mut planning_facts,
                Some(Construction {
                    environments: construction_environments,
                    sink: &mut sink,
                }),
            )
        });
        // A direct run may reach a verified loop summary successfully while
        // still discovering that the summary has no standalone surface form.
        // In that case the semantic plan is valid, but it cannot be retained
        // as the certificate for an explicit `execute()`.  Retry through the
        // bounded path planner, which records the loop body and its nested
        // branches as ordinary checked operations instead of emitting a
        // detached loop-summary certificate.
        if direct_result.is_none_or(|result| result.is_err()) || sink.blocker.is_some() {
            planning = execution.clone();
            planning.planned_statement_transitions.clear();
            planning.surface_record.certificate_facts =
                ProofFactStore::from_ordered(facts_vec.clone());
            sink = planning_sink();
            planning_facts = facts_vec.clone();
            bounded_execute_from_frontier_position(
                &mut planning,
                &tactic_context,
                &mut planning_facts,
                StatementPrerequisitePolicy::Planning,
                Some(Construction {
                    environments: construction_environments,
                    sink: &mut sink,
                }),
            )?;
        }
        let construction = sink;
        if let Some(blocker) = &construction.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart `execute` could not construct checked Proof operations: {blocker}"
            )));
        }
        let no_candidate = || {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart `execute` found no checked Proof candidate"
            ))
        };
        if construction.steps.is_empty() {
            return Err(no_candidate());
        }
        let linear_supported = construction.steps.iter().all(|step| {
            matches!(
                step,
                ProofStep::Have { .. }
                    | ProofStep::UnfoldPredicate(_)
                    | ProofStep::UnfoldFunction(_)
                    | ProofStep::TransportUsing { .. }
                    | ProofStep::Step
            )
        }) && construction
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Step));
        let applied = if linear_supported {
            let mut proof = self.clone();
            for step in &construction.steps {
                proof = proof.apply_step(step.clone())?;
            }
            Some(proof)
        } else if construction
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::If { .. }))
        {
            self.try_planned_execution_steps(&construction.steps)?
        } else {
            None
        };
        let Some(proof) = applied else {
            return Err(no_candidate());
        };
        let (proof, ()) = proof.edit_execution_presentation(|presentation| {
            presentation.surface_record.last_step_entry = construction.last_step_entry;
        })?;
        Ok(proof)
    }

    /// The mid-execution `have` for a bounded region path, applied through
    /// the one shared have law when the Proof-native nested scope declines.
    /// The law records its own surface certificate and lowerings.
    pub(in crate::surface::proof) fn apply_mid_execution_have(
        &self,
        expansion_capture: Option<&mut ExpansionCapture>,
        have: &ProofHave,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let mut expansion_capture = expansion_capture;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`have` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`have`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let mut facts = self.facts().to_vec();
        let base_facts = facts.len();
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.presentation.expansion,
            context.constants.proof_site.as_ref(),
        );
        let smart_certificate =
            check_mid_execution_have(have, &mut execution, &tactic_context, &mut facts)?;
        if capture_this_tactic {
            // The tactic's expansion is the law's own surface certificate.
            let expansion = ProofCertificateBuilder {
                steps: smart_certificate.steps().to_vec(),
                ..ProofCertificateBuilder::default()
            };
            finish_tactic_expansion_capture(expansion_capture, &expansion, false);
        }
        let added = facts[base_facts..].to_vec();
        let mut proof_facts = self.facts().clone();
        for fact in &added {
            proof_facts = proof_facts.with_kernel_checked_fact(fact.clone());
        }
        // Retain the checked `have` as provenance: a smart body keeps the
        // law's selected surface operations; an explicit body keeps its own
        // script. Expansion serializes this node, never the aftermath.
        let have_step = match smart_certificate.steps() {
            // The law's surface certificate is already the complete checked
            // form, including the `have` wrapper when it selected one.
            [step @ ProofStep::Have { .. }] => step.clone(),
            _ => ProofStep::Have {
                proposition: have.proposition.clone(),
                proof: Box::new(smart_certificate),
            },
        };
        let state = self
            .state
            .publish_checked_frontier_transition(proof_facts, execution, added, Vec::new())
            .map_err(|error| self.execution_update_error("`have`", error))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(have_step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        })
    }

    /// Records where the checked `close_invariants` tactic sat, so the
    /// kernel re-derivation its caller performs at the bundle check can be
    /// timed against that tactic's identity. Cursor metadata only.
    pub(in crate::surface::proof) fn record_invariant_closer(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`close_invariants`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let statement_index = execution.core.frontier.next_statement_index;
        let (proof, ()) = self.clone().edit_execution_presentation(|presentation| {
            presentation.invariant_closer_step = Some(InvariantCloserStep {
                tactic_index,
                source_index,
                statement_index,
            });
        })?;
        let state = proof.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(proof.with_kernel_state(state))
    }

    /// Records a region-level `simp` for the loop-invariant bundle. The
    /// tactic's semantic content is the bundle closer certified at the
    /// typed boundary, so only its identity is recorded here — cursor
    /// metadata for expansion capture and timing attribution, never a
    /// semantic transition.
    pub(in crate::surface::proof) fn defer_region_simp(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`simp`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("a region `simp` is only available in a loop-region proof"));
        }
        let (proof, ()) = self.clone().edit_execution_presentation(|presentation| {
            presentation.region_simp = Some((tactic_index, source_index));
        })?;
        let state = proof.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(proof.with_kernel_state(state))
    }

    /// Applies a frontier-local `loop` tactic as one checked operation on
    /// the focused branch execution frontier: the loop's phases verify through the
    /// shared loop-planning machinery, the certified loop rule replaces the
    /// `while` statement in the frontier's own statement tree, and the
    /// derived exit facts join this goal's context. The surface record and
    /// expansion capture ride the transitional cursor exactly as the
    /// checked form recorded them.
    pub(in crate::surface::proof) fn apply_frontier_local_loop(
        &self,
        mut expansion_capture: Option<&mut ExpansionCapture>,
        loop_clause: &StructuralClause,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`loop` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`loop`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let mut facts = self.facts().to_vec();
        let base_facts = facts.len();
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.presentation.expansion,
            context.constants.proof_site.as_ref(),
        );
        let _timing = TacticTiming::new(
            context.claim_label,
            tactic_index,
            source_index,
            &ProofTactic::Loop(loop_clause.clone()),
            execution.core.frontier.next_statement_index,
        );
        let expanded_loop = execute_frontier_local_loop(
            expansion_capture.as_deref_mut(),
            loop_clause,
            &mut execution,
            &tactic_context,
            &mut facts,
            source_index,
        )?;
        if capture_this_tactic {
            // The tactic's expansion is the expanded loop itself.
            let expansion = ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(std::slice::from_ref(
                    &ProofTactic::Loop(expanded_loop.clone()),
                ))
                .expect("an expanded loop is one proof step")
                .steps()
                .to_vec(),
                ..ProofCertificateBuilder::default()
            };
            finish_tactic_expansion_capture(expansion_capture, &expansion, false);
        }
        debug_assert!(facts.len() >= base_facts);
        let added = facts[base_facts..].to_vec();
        let mut proof_facts = self.facts().clone();
        for fact in &added {
            proof_facts = proof_facts.with_kernel_checked_fact(fact.clone());
        }
        // Retain the expanded loop clause as checked provenance so
        // whole-claim expansion serializes it without consulting the
        // transitional builder record.
        let loop_step = ProofCertificate::from_proof_tactics(std::slice::from_ref(
            &ProofTactic::Loop(expanded_loop),
        ))
        .map_err(|error| {
            self.step_error(format!(
                "`loop` produced an invalid expanded clause: {error:?}"
            ))
        })?
        .steps()[0]
            .clone();
        let state = self
            .state
            .publish_checked_frontier_transition(proof_facts, execution, added, Vec::new())
            .map_err(|error| self.execution_update_error("`loop`", error))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(loop_step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        })
    }
}
