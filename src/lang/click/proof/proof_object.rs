use super::pure_theorems::{PureTheoremContext, lower_pure_theorem_proposition};
use super::*;

use std::cmp::Ordering;
use std::sync::Arc;

/// Immutable checked proof state exposed to smart tactics.
///
/// This first vertical slice supports linear pure goals. The representation is
/// deliberately already persistent: cloning a `Proof` shares its semantic
/// state and derivation prefix, and applying a step copies only logarithmically
/// many fact-index nodes plus the step's own semantic delta.
#[derive(Clone)]
pub(super) struct Proof<'a> {
    context: Arc<ProofContext<'a>>,
    state: Arc<ProofState>,
    node: Arc<ProofNode>,
}

enum ProofContext<'a> {
    Pure(PureProofContext<'a>),
    Point(PointProofContext<'a>),
    Execution(ExecutionProofContext<'a>),
}

struct PureProofContext<'a> {
    claim_label: &'a str,
    theorem_context: &'a PureTheoremContext,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
}

struct PointProofContext<'a> {
    claim_label: &'a str,
    tactic_index: usize,
    parameters: &'a [syntax::C0Parameter],
    arguments: &'a [CExpression],
    pre_state: &'a CState,
    state: &'a CState,
    program_point_states: &'a ProgramPointStates,
    surface_propositions: &'a SurfacePropositionMap,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    unfolded_predicates: &'a [String],
    available: &'a [Proposition],
    effect_facts: &'a [ExecutionPureFact],
    lowering_context: Arc<Vec<Proposition>>,
}

struct ExecutionProofContext<'a> {
    claim_label: &'a str,
    tactic_index: usize,
    function_block: &'a FunctionBlock,
    function: &'a CFunction,
    parsed_function: &'a syntax::C0Function,
    arguments: &'a [CExpression],
    function_environment: &'a CExecutionEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
}

struct ProofState {
    facts: PersistentFactIndex,
    goal: Goal,
    complete: bool,
    added_facts: Arc<Vec<Proposition>>,
    checked_facts: Arc<Vec<Proposition>>,
    execution: Option<ProofReplayContext>,
}

/// One unresolved judgment owned by a `Proof`.
///
/// A proposition goal can be discharged locally. An execution-frontier goal
/// remains open while fact-producing point steps advance the enclosing C
/// proof; later slices will add the frontier transition steps themselves.
#[derive(Clone)]
enum Goal {
    Proposition(Arc<Proposition>),
    ExecutionFrontier,
}

/// Private persistent provenance node. Smart tactics can retain a `Proof`,
/// but cannot manufacture one of these or detach semantic state from the step
/// that produced it.
struct ProofNode {
    parent: Option<Arc<ProofNode>>,
    step: Option<Arc<SimpleProofStep>>,
    depth: usize,
}

#[derive(Clone, Default)]
struct PersistentFactIndex {
    root: Option<Arc<FactNode>>,
}

struct FactNode {
    fact: Arc<Proposition>,
    left: Option<Arc<FactNode>>,
    right: Option<Arc<FactNode>>,
    height: u16,
}

impl<'a> Proof<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_pure_goal(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        theorem_context: &'a PureTheoremContext,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let mut facts = PersistentFactIndex::default();
        for fact in requires {
            facts = facts.with_fact(fact.clone());
        }
        Self {
            context: Arc::new(ProofContext::Pure(PureProofContext {
                claim_label,
                theorem_context,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            })),
            state: Arc::new(ProofState {
                facts,
                goal: Goal::Proposition(Arc::new(goal)),
                complete: false,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
                execution: None,
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_point_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_point(
            claim_label,
            tactic_index,
            available,
            Goal::Proposition(Arc::new(goal)),
            parameters,
            arguments,
            pre_state,
            state,
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_point_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_point(
            claim_label,
            tactic_index,
            available,
            Goal::ExecutionFrontier,
            parameters,
            arguments,
            pre_state,
            state,
            program_point_states,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn for_point(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Goal,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        let mut facts = PersistentFactIndex::default();
        for fact in available {
            facts = facts.with_fact(fact.clone());
        }
        let mut lowering_context = available.to_vec();
        append_resource_context_observable_facts(state.resources(), &mut lowering_context);
        Self {
            context: Arc::new(ProofContext::Point(PointProofContext {
                claim_label,
                tactic_index,
                parameters,
                arguments,
                pre_state,
                state,
                program_point_states,
                surface_propositions,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                unfolded_predicates,
                available,
                effect_facts,
                lowering_context: Arc::new(lowering_context),
            })),
            state: Arc::new(ProofState {
                facts,
                goal,
                complete: false,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
                execution: None,
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
        }
    }

    /// Creates a uniquely owned execution-frontier proof without cloning the
    /// mutable replay history. The accepted linear statement step consumes
    /// this root and returns its owned successor; cheap forkable execution
    /// state will arrive with the branch representation.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_execution_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        execution: ProofReplayContext,
        function_block: &'a FunctionBlock,
        function: &'a CFunction,
        parsed_function: &'a syntax::C0Function,
        arguments: &'a [CExpression],
        function_environment: &'a CExecutionEnvironment,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
    ) -> Self {
        Self {
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label,
                tactic_index,
                function_block,
                function,
                parsed_function,
                arguments,
                function_environment,
                predicate_environment,
                click_function_environment,
            })),
            state: Arc::new(ProofState {
                facts: PersistentFactIndex::default(),
                goal: Goal::ExecutionFrontier,
                complete: false,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
                execution: Some(execution),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
        }
    }

    pub(super) fn goal(&self) -> Option<&Proposition> {
        match &self.state.goal {
            Goal::Proposition(goal) => Some(goal),
            Goal::ExecutionFrontier => None,
        }
    }

    pub(super) fn is_complete(&self) -> bool {
        self.state.complete
    }

    /// Checks one explicit simple step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(super) fn apply_step(&self, step: SimpleProofStep) -> Result<Self, ClickError> {
        if self.state.complete {
            return Err(self.step_error("a tactic follows a goal-closing step"));
        }

        let next_state = match &step {
            SimpleProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises)?,
            SimpleProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises)?,
            SimpleProofStep::Assumption => {
                let goal = self.proposition_goal("`assumption` requires a proposition goal")?;
                if !self.state.facts.contains(goal) {
                    return Err(self.step_error(format!(
                        "`assumption` requires the exact current goal as an available fact: {:?}",
                        goal
                    )));
                }
                ProofState {
                    facts: self.state.facts.clone(),
                    goal: self.state.goal.clone(),
                    complete: true,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                    execution: None,
                }
            }
            SimpleProofStep::Normalize => {
                let goal = self.proposition_goal("`normalize` requires a proposition goal")?;
                if !normalizes_context_free(goal) {
                    return Err(self.step_error(format!(
                        "`normalize` requires a context-free true goal: {:?}",
                        goal
                    )));
                }
                ProofState {
                    facts: self.state.facts.clone(),
                    goal: self.state.goal.clone(),
                    complete: true,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                    execution: None,
                }
            }
            SimpleProofStep::Intro => {
                let goal = self
                    .proposition_goal("`intro` requires a proposition goal")?
                    .clone();
                let (goal, introduced) = match goal {
                    Proposition::Implies(antecedent, consequent) => {
                        (*consequent, Some(*antecedent))
                    }
                    Proposition::ForAll { body, .. } => (*body, None),
                    Proposition::Not(body) => (
                        Proposition::ConditionIs(ConditionTerm::Constant(false), true),
                        Some(*body),
                    ),
                    other => {
                        return Err(self.step_error(format!(
                            "`intro` requires an implication, negation, or universal goal, got {other:?}"
                        )));
                    }
                };
                let mut facts = self.state.facts.clone();
                let added_facts = introduced.into_iter().collect::<Vec<_>>();
                for fact in &added_facts {
                    facts = facts.with_fact(fact.clone());
                }
                ProofState {
                    facts,
                    goal: Goal::Proposition(Arc::new(goal)),
                    complete: false,
                    checked_facts: Arc::new(added_facts.clone()),
                    added_facts: Arc::new(added_facts),
                    execution: None,
                }
            }
            SimpleProofStep::Split => {
                let goal = self.proposition_goal("`split` requires a proposition goal")?;
                let Proposition::And(left, right) = goal else {
                    return Err(self
                        .step_error(format!("`split` requires a conjunction goal, got {goal:?}")));
                };
                if !self.state.facts.contains(left) || !self.state.facts.contains(right) {
                    return Err(self.step_error(format!(
                        "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
                    )));
                }
                self.closed_state()
            }
            SimpleProofStep::Left => {
                let goal = self.proposition_goal("`left` requires a proposition goal")?;
                let Proposition::Or(left, _) = goal else {
                    return Err(self
                        .step_error(format!("`left` requires a disjunction goal, got {goal:?}")));
                };
                if !self.state.facts.contains(left) {
                    return Err(self.step_error(format!(
                        "`left` requires its selected disjunct as an exact fact: {left:?}"
                    )));
                }
                self.closed_state()
            }
            SimpleProofStep::Right => {
                let goal = self.proposition_goal("`right` requires a proposition goal")?;
                let Proposition::Or(_, right) = goal else {
                    return Err(self
                        .step_error(format!("`right` requires a disjunction goal, got {goal:?}")));
                };
                if !self.state.facts.contains(right) {
                    return Err(self.step_error(format!(
                        "`right` requires its selected disjunct as an exact fact: {right:?}"
                    )));
                }
                self.closed_state()
            }
            SimpleProofStep::Enumerate => {
                let goal = self.proposition_goal("`enumerate` requires a proposition goal")?;
                let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
                    return Err(self.step_error(format!(
                        "`enumerate` requires a constant-bounded universal goal, got {goal:?}"
                    )));
                };
                for (_, instance) in instances {
                    if !normalizes_context_free(&instance) && !self.state.facts.contains(&instance)
                    {
                        return Err(self.step_error(format!(
                            "`enumerate` requires an unavailable exact instance: {instance:?}"
                        )));
                    }
                }
                self.closed_state()
            }
            SimpleProofStep::Contradiction(surface) => self.apply_contradiction(surface)?,
            _ => {
                return Err(self.step_error(
                    "this simple step has not yet migrated to the checked `Proof` API",
                ));
            }
        };

        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(next_state),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                depth: self.node.depth + 1,
            }),
        })
    }

    pub(super) fn certificate(&self) -> ProofCertificate {
        let mut steps = Vec::with_capacity(self.node.depth);
        let mut node = Some(self.node.as_ref());
        while let Some(current) = node {
            if let Some(step) = &current.step {
                steps.push(step.as_ref().clone());
            }
            node = current.parent.as_deref();
        }
        steps.reverse();
        ProofCertificate::from_steps(steps)
    }

    /// Applies one selected execution step by consuming the uniquely owned
    /// frontier state. This is deliberately separate from forkable local
    /// proposition steps until execution replay state itself is persistent.
    pub(super) fn apply_owned_execution_step(
        self,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        let Proof {
            context: proof_context,
            state: proof_state,
            node,
        } = self;
        let ProofContext::Execution(context) = proof_context.as_ref() else {
            return Err(ClickError::new(
                "`step using` requires an execution-frontier proof",
            ));
        };
        let step_error = |message: &str| {
            ClickError::new(format!(
                "`{}` proof step {}: {message}",
                context.claim_label, node.depth
            ))
        };
        if proof_state.complete {
            return Err(step_error(
                "a tactic follows a completed execution frontier",
            ));
        }
        if !matches!(
            step,
            SimpleProofStep::StepUsing(_) | SimpleProofStep::TransportUsing { .. }
        ) {
            return Err(step_error(
                "owned execution proof currently accepts only `transport using` and `step using`",
            ));
        }
        let mut state = Arc::try_unwrap(proof_state).map_err(|_| {
            step_error(
                "execution-frontier state was forked before its persistent representation exists",
            )
        })?;
        let mut execution = state
            .execution
            .take()
            .ok_or_else(|| step_error("execution-frontier proof lost its owned semantic state"))?;
        match &step {
            SimpleProofStep::StepUsing(premises) => check_step_using(
                &mut execution.replay,
                &mut execution.state,
                &mut execution.pure_facts,
                premises,
                context.function_block,
                context.function,
                context.parsed_function,
                context.arguments,
                context.function_environment,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                context.tactic_index,
            )?,
            SimpleProofStep::TransportUsing {
                source,
                target,
                premises,
            } => {
                let pre_state = execution
                    .replay
                    .old_reference_state(&execution.state)
                    .clone();
                let checked = check_point_fact_transport_using(
                    source,
                    target,
                    premises,
                    context.claim_label,
                    context.tactic_index,
                    &execution.pure_facts,
                    &execution.replay.effect_facts,
                    context.parsed_function.parameters(),
                    context.arguments,
                    &pre_state,
                    &execution.state,
                    &execution.replay.program_point_states,
                    &execution.replay.surface_propositions,
                    context.predicate_environment,
                    context.click_function_environment,
                )?;
                execution
                    .replay
                    .surface_propositions
                    .record_lowering(source, &checked.source)?;
                execution
                    .replay
                    .surface_propositions
                    .record_lowering(target, &checked.target)?;
                if !execution.pure_facts.contains(&checked.target) {
                    execution.pure_facts.push(checked.target);
                }
            }
            _ => unreachable!("checked above"),
        }
        state.execution = Some(execution);
        state.added_facts = Arc::new(Vec::new());
        state.checked_facts = Arc::new(Vec::new());
        Ok(Self {
            context: proof_context,
            state: Arc::new(state),
            node: Arc::new(ProofNode {
                parent: Some(node.clone()),
                step: Some(Arc::new(step)),
                depth: node.depth + 1,
            }),
        })
    }

    pub(super) fn into_execution_context(self) -> Result<ProofReplayContext, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("proof does not own an execution frontier"));
        }
        let error = format!(
            "`{}` proof step {}: execution-frontier successor is still shared",
            self.context.claim_label(),
            self.node.depth
        );
        let missing = format!(
            "`{}` proof step {}: execution-frontier successor lost its semantic state",
            self.context.claim_label(),
            self.node.depth
        );
        let mut state = Arc::try_unwrap(self.state).map_err(|_| ClickError::new(error))?;
        state
            .execution
            .take()
            .ok_or_else(|| ClickError::new(missing))
    }

    /// Semantic facts introduced by the most recently accepted step.
    /// Enclosing proof infrastructure can incorporate this output-sensitive
    /// delta without traversing or cloning the proof's complete fact set.
    pub(super) fn added_facts(&self) -> &[Proposition] {
        self.state.added_facts.as_ref()
    }

    /// Exact semantic facts selected or established by the latest step, in
    /// step-defined order. This lets enclosing surface bookkeeping record the
    /// checker-owned spellings without re-lowering them.
    pub(super) fn checked_facts(&self) -> &[Proposition] {
        self.state.checked_facts.as_ref()
    }

    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// sole nonterminal move and strictly removes one outer goal connective.
    pub(super) fn try_direct_logical_closure(&self) -> Option<Self> {
        let mut proof = self.clone();
        loop {
            for closer in [
                SimpleProofStep::Assumption,
                SimpleProofStep::Normalize,
                SimpleProofStep::Split,
                SimpleProofStep::Left,
                SimpleProofStep::Right,
                SimpleProofStep::Enumerate,
            ] {
                if let Ok(closed) = proof.apply_step(closer) {
                    return Some(closed);
                }
            }
            proof = proof.apply_step(SimpleProofStep::Intro).ok()?;
        }
    }

    fn apply_theorem_using(
        &self,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                self.apply_pure_theorem_using(context, application, surface_premises)
            }
            ProofContext::Point(context) => {
                self.apply_point_theorem_using(context, application, surface_premises)
            }
            ProofContext::Execution(_) => {
                Err(self.step_error("`apply using` requires a proposition or point proof"))
            }
        }
    }

    fn apply_pure_theorem_using(
        &self,
        context: &PureProofContext<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| {
                lower_pure_theorem_proposition(
                    context.claim_label,
                    premise,
                    &context.theorem_context.values,
                    &context.theorem_context.array_refs,
                    &context.theorem_context.memory,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower `apply using` premise: {message}"))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        for premise in &explicit_premises {
            if !self.state.facts.contains(premise) {
                return Err(self.step_error(format!(
                    "`apply using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        // The checker receives exactly the named premises, not the ambient
        // context. Its work is therefore independent of unrelated facts, and
        // it cannot silently search for an omitted theorem requirement.
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let program_point_states = ProgramPointStates::new();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            pre_state: &state,
            post_state: &state,
            result: None,
            program_point_states: &program_point_states,
        };
        let applied = apply_theorem_applications_to_available(
            context.theorem_environment,
            &[(self.node.depth, application.clone())],
            context.claim_label,
            None,
            explicit_premises,
            &application_context,
            context.predicate_environment,
            context.click_function_environment,
            &[],
        )?;

        let mut facts = self.state.facts.clone();
        let mut added_facts = Vec::new();
        for fact in applied {
            if !facts.contains(&fact) {
                added_facts.push(fact.clone());
            }
            facts = facts.with_fact(fact);
        }
        Ok(ProofState {
            facts,
            goal: self.state.goal.clone(),
            complete: false,
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
            execution: None,
        })
    }

    fn apply_point_theorem_using(
        &self,
        context: &PointProofContext<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        // The first point-proof migration is intentionally linear: a single
        // theorem application that closes the selected goal. This prevents
        // an accidental partial API from becoming a second mutable point
        // prover while later point steps move over one by one.
        if self.node.depth != 0 {
            return Err(self.step_error("point `apply using` currently requires the root proof"));
        }
        let explicit_premises = surface_premises
            .iter()
            .map(|surface| {
                if let Some(recorded) = context
                    .surface_propositions
                    .available_kernel(surface, context.lowering_context.as_ref())
                {
                    return Ok(recorded.clone());
                }
                lower_point_proposition(
                    surface,
                    context.lowering_context.as_ref(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    None,
                    context.program_point_states,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!(
                        "could not lower `apply using` premise `{}`: {message}",
                        describe_click_proposition(surface)
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        for premise in &explicit_premises {
            if !self.state.facts.contains(premise) {
                return Err(self.step_error(format!(
                    "`apply using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }
        let applied = apply_theorem_at_current_point(
            context.theorem_environment,
            application,
            context.claim_label,
            context.tactic_index,
            explicit_premises,
            context.parameters,
            context.arguments,
            context.pre_state,
            context.state,
            context.program_point_states,
            context.predicate_environment,
            context.click_function_environment,
            context.unfolded_predicates,
            Some(context.lowering_context.as_ref()),
        )?;
        let mut facts = self.state.facts.clone();
        let mut added_facts = Vec::new();
        for fact in applied {
            if !facts.contains(&fact) {
                added_facts.push(fact.clone());
            }
            facts = facts.with_fact(fact);
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            facts,
            goal: self.state.goal.clone(),
            complete,
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
            execution: None,
        })
    }

    fn apply_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("`transport using` requires a point proof"));
        };
        if self.node.depth != 0 {
            return Err(
                self.step_error("point `transport using` currently requires the root proof")
            );
        }
        let checked = check_point_fact_transport_using(
            source,
            target,
            premises,
            context.claim_label,
            context.tactic_index,
            context.available,
            context.effect_facts,
            context.parameters,
            context.arguments,
            context.pre_state,
            context.state,
            context.program_point_states,
            context.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
        )?;
        let mut facts = self.state.facts.clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        let checked_facts = vec![checked.source, checked.target.clone()];
        facts = facts.with_fact(checked.target);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            facts,
            goal: self.state.goal.clone(),
            complete,
            added_facts: Arc::new(added_facts),
            checked_facts: Arc::new(checked_facts),
            execution: None,
        })
    }

    fn apply_contradiction(&self, surface: &ClickProposition) -> Result<ProofState, ClickError> {
        let fact = match self.context.as_ref() {
            ProofContext::Pure(context) => lower_pure_theorem_proposition(
                context.claim_label,
                surface,
                &context.theorem_context.values,
                &context.theorem_context.array_refs,
                &context.theorem_context.memory,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                self.step_error(format!("could not lower `contradiction` fact: {message}"))
            })?,
            ProofContext::Point(context) => {
                if let Some(recorded) = context
                    .surface_propositions
                    .available_kernel(surface, context.lowering_context.as_ref())
                {
                    recorded.clone()
                } else {
                    lower_point_proposition(
                        surface,
                        context.lowering_context.as_ref(),
                        context.parameters,
                        context.arguments,
                        context.pre_state,
                        context.state,
                        None,
                        context.program_point_states,
                        context.predicate_environment,
                        context.click_function_environment,
                    )
                    .map_err(|message| {
                        self.step_error(format!("could not lower `contradiction` fact: {message}"))
                    })?
                }
            }
            ProofContext::Execution(_) => {
                return Err(self.step_error("`contradiction` requires a proposition goal"));
            }
        };
        let negated = Proposition::Not(Box::new(fact.clone()));
        let opposite_condition = match &fact {
            Proposition::ConditionIs(condition, value) => {
                Some(Proposition::ConditionIs(condition.clone(), !value))
            }
            _ => None,
        };
        if !self.state.facts.contains(&fact)
            || (!self.state.facts.contains(&negated)
                && !opposite_condition
                    .as_ref()
                    .is_some_and(|opposite| self.state.facts.contains(opposite)))
        {
            return Err(self.step_error(format!(
                "`contradiction` requires an exact fact and its exact negation or opposite condition polarity: {fact:?}"
            )));
        }
        Ok(self.closed_state())
    }

    fn proposition_goal(&self, message: &str) -> Result<&Proposition, ClickError> {
        self.goal().ok_or_else(|| self.step_error(message))
    }

    fn closed_state(&self) -> ProofState {
        ProofState {
            facts: self.state.facts.clone(),
            goal: self.state.goal.clone(),
            complete: true,
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
            execution: None,
        }
    }

    fn step_error(&self, message: impl Into<String>) -> ClickError {
        ClickError::new(format!(
            "`{}` proof step {}: {}",
            self.context.claim_label(),
            self.node.depth,
            message.into()
        ))
    }

    #[cfg(test)]
    fn fact_lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.state.facts.lookup_comparisons(fact)
    }
}

impl ProofContext<'_> {
    fn claim_label(&self) -> &str {
        match self {
            Self::Pure(context) => context.claim_label,
            Self::Point(context) => context.claim_label,
            Self::Execution(context) => context.claim_label,
        }
    }
}

impl PersistentFactIndex {
    fn with_fact(&self, fact: Proposition) -> Self {
        let mut next = self.clone();
        if matches!(fact, Proposition::And(_, _)) {
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                next.root = insert_fact_node(next.root.as_ref(), Arc::new(conjunct));
            }
        }
        next.root = insert_fact_node(next.root.as_ref(), Arc::new(fact));
        next
    }

    fn contains(&self, fact: &Proposition) -> bool {
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            match fact.cmp(current.fact.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return true,
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        false
    }

    #[cfg(test)]
    fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        let mut comparisons = 0;
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            comparisons += 1;
            match fact.cmp(current.fact.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return comparisons,
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        comparisons
    }
}

fn collect_owned_atomic_conjuncts(fact: &Proposition, output: &mut Vec<Proposition>) {
    match fact {
        Proposition::And(left, right) => {
            collect_owned_atomic_conjuncts(left, output);
            collect_owned_atomic_conjuncts(right, output);
        }
        _ => output.push(fact.clone()),
    }
}

fn fact_node_height(node: Option<&Arc<FactNode>>) -> u16 {
    node.map_or(0, |node| node.height)
}

fn make_fact_node(
    fact: Arc<Proposition>,
    left: Option<Arc<FactNode>>,
    right: Option<Arc<FactNode>>,
) -> Arc<FactNode> {
    Arc::new(FactNode {
        fact,
        height: 1 + fact_node_height(left.as_ref()).max(fact_node_height(right.as_ref())),
        left,
        right,
    })
}

fn balance_fact_node(
    fact: Arc<Proposition>,
    left: Option<Arc<FactNode>>,
    right: Option<Arc<FactNode>>,
) -> Arc<FactNode> {
    let left_height = fact_node_height(left.as_ref());
    let right_height = fact_node_height(right.as_ref());
    if left_height > right_height + 1 {
        let left_node = left.as_ref().expect("left-heavy node has a left child");
        if fact_node_height(left_node.left.as_ref()) >= fact_node_height(left_node.right.as_ref()) {
            let new_right = make_fact_node(fact, left_node.right.clone(), right);
            return make_fact_node(
                left_node.fact.clone(),
                left_node.left.clone(),
                Some(new_right),
            );
        }
        let middle = left_node
            .right
            .as_ref()
            .expect("left-right-heavy node has a middle child");
        let new_left = make_fact_node(
            left_node.fact.clone(),
            left_node.left.clone(),
            middle.left.clone(),
        );
        let new_right = make_fact_node(fact, middle.right.clone(), right);
        return make_fact_node(middle.fact.clone(), Some(new_left), Some(new_right));
    }
    if right_height > left_height + 1 {
        let right_node = right.as_ref().expect("right-heavy node has a right child");
        if fact_node_height(right_node.right.as_ref()) >= fact_node_height(right_node.left.as_ref())
        {
            let new_left = make_fact_node(fact, left, right_node.left.clone());
            return make_fact_node(
                right_node.fact.clone(),
                Some(new_left),
                right_node.right.clone(),
            );
        }
        let middle = right_node
            .left
            .as_ref()
            .expect("right-left-heavy node has a middle child");
        let new_left = make_fact_node(fact, left, middle.left.clone());
        let new_right = make_fact_node(
            right_node.fact.clone(),
            middle.right.clone(),
            right_node.right.clone(),
        );
        return make_fact_node(middle.fact.clone(), Some(new_left), Some(new_right));
    }
    make_fact_node(fact, left, right)
}

fn insert_fact_node(node: Option<&Arc<FactNode>>, fact: Arc<Proposition>) -> Option<Arc<FactNode>> {
    let Some(node) = node else {
        return Some(make_fact_node(fact, None, None));
    };
    Some(match fact.as_ref().cmp(node.fact.as_ref()) {
        Ordering::Less => balance_fact_node(
            node.fact.clone(),
            insert_fact_node(node.left.as_ref(), fact),
            node.right.clone(),
        ),
        Ordering::Equal => node.clone(),
        Ordering::Greater => balance_fact_node(
            node.fact.clone(),
            node.left.clone(),
            insert_fact_node(node.right.as_ref(), fact),
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn indexed_fact(index: u32) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(0))),
                Box::new(Bitvector32Term::Constant(index)),
            ),
            true,
        )
    }

    #[test]
    fn proof_failure_preserves_ancestor_and_selected_provenance() {
        let goal = indexed_fact(7);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: vec![goal.clone()],
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "transactional",
            &theorem_context.requires,
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let fork = root.clone();
        assert!(Arc::ptr_eq(&root.state, &fork.state));
        assert!(Arc::ptr_eq(&root.node, &fork.node));

        assert!(
            fork.apply_step(SimpleProofStep::Normalize).is_err(),
            "a symbolic comparison must not normalize to true"
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());

        let complete = root
            .apply_step(SimpleProofStep::Assumption)
            .expect("the exact root fact should close the goal");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[SimpleProofStep::Assumption]
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn persistent_fact_lookup_scales_logarithmically() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        for size in [16_u32, 64, 256, 1024, 4096] {
            let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let goal = indexed_fact(size - 1);
            let theorem_context = PureTheoremContext {
                memory: CMemory::new(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires,
            };
            let proof = Proof::for_pure_goal(
                "scaling",
                &theorem_context.requires,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let shared = proof.clone();
            assert!(Arc::ptr_eq(&proof.state, &shared.state));
            assert!(Arc::ptr_eq(&proof.node, &shared.node));

            let comparisons = proof.fact_lookup_comparisons(&goal);
            let logarithmic_bound = 2 * (u32::BITS - size.leading_zeros()) as usize + 2;
            assert!(
                comparisons <= logarithmic_bound,
                "size {size} lookup took {comparisons} comparisons (bound {logarithmic_bound})"
            );

            let complete = shared
                .apply_step(SimpleProofStep::Assumption)
                .expect("fixed local step should succeed");
            assert!(complete.is_complete());
            assert!(Arc::ptr_eq(
                complete
                    .node
                    .parent
                    .as_ref()
                    .expect("successor has a parent"),
                &proof.node
            ));
            assert!(proof.certificate().steps().is_empty());
            assert_eq!(complete.certificate().steps().len(), 1);
        }
    }

    #[test]
    fn execution_frontier_rejects_proposition_closers_transactionally() {
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_point_frontier(
            "frontier",
            0,
            &[],
            &[],
            &[],
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let fork = root.clone();
        assert!(root.goal().is_none());
        assert!(Arc::ptr_eq(&root.state, &fork.state));
        assert!(Arc::ptr_eq(&root.node, &fork.node));
        for closer in [SimpleProofStep::Assumption, SimpleProofStep::Normalize] {
            let error = fork
                .apply_step(closer)
                .err()
                .expect("a proposition closer cannot close an execution frontier");
            assert!(error.message().contains("proposition goal"), "{error:?}");
        }
        assert!(!root.is_complete());
        assert!(root.added_facts().is_empty());
        assert!(root.certificate().steps().is_empty());
    }
}
