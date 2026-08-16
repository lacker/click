use super::pure_theorems::{PureTheoremContext, lower_pure_theorem_proposition};
use super::*;
use crate::persistent::{PersistentMap, PersistentSet};

#[cfg(test)]
use crate::persistent::persistent_node_allocations;

use std::sync::Arc;

/// Immutable checked proof state exposed to smart tactics.
///
/// Cloning a `Proof` shares its semantic state and derivation prefix. Applying
/// a step copies only persistent index paths and the step's own semantic delta;
/// proposition, point, and execution-frontier goals use the same boundary.
#[derive(Clone)]
pub(super) struct Proof<'a> {
    context: Arc<ProofContext<'a>>,
    state: Arc<ProofState>,
    node: Arc<ProofNode>,
}

/// An opaque position in one `Proof` derivation.
///
/// This retains no semantic state. Structured joins use it to extract only the
/// already-checked descendant steps for an arm.
#[derive(Clone)]
pub(super) struct ProofCheckpoint<'a> {
    context: Arc<ProofContext<'a>>,
    node: Arc<ProofNode>,
}

/// Two open proposition branches owned by one audited structural operation.
///
/// Branch-local assumptions exist only inside this container. The enclosing
/// `Proof` advances when both arms are complete and `join` records their exact
/// retained certificates in one structured simple step.
#[derive(Clone)]
pub(super) struct ProofBranches<'a> {
    root: Proof<'a>,
    root_checkpoint: ProofCheckpoint<'a>,
    structure: ProofBranchStructure,
    arms: [Proof<'a>; 2],
}

/// Feasible arms of one checked C `if` frontier.
///
/// Entering the container performs the audited condition transition and C
/// frontier movement once. Arm bodies then extend the retained `Proof`
/// descendants; a join owns the corresponding structured certificate node.
pub(super) struct ExecutionProofBranches<'a> {
    root: Proof<'a>,
    root_checkpoint: ProofCheckpoint<'a>,
    statement_index: usize,
    continuation_index: usize,
    continuation_remaining: Option<Arc<CStatement>>,
    execution_start_state: CState,
    initial_continuation_depth: usize,
    arms: [Option<ExecutionProofArm<'a>>; 2],
}

struct ExecutionProofArm<'a> {
    proof: Proof<'a>,
    introduced_facts: PersistentOrderedSet<Proposition>,
    introduced_effect_facts: Vec<ExecutionPureFact>,
    introduced_function_entry_prerequisites: PersistentOrderedSet<Proposition>,
    introduced_function_entry_derivations: PersistentOrderedSet<Theorem>,
    introduced_unfolded_predicates: PersistentOrderedSet<String>,
    condition_theorem: Theorem,
}

/// One nested proposition proof owned by an audited scope operation.
#[derive(Clone)]
pub(super) struct ProofScope<'a> {
    root: Proof<'a>,
    structure: ProofScopeStructure,
    body: Proof<'a>,
}

#[derive(Clone)]
enum ProofScopeStructure {
    Have {
        proposition: ClickProposition,
        kernel: Proposition,
    },
}

#[derive(Clone)]
enum ProofBranchStructure {
    Cases { disjunction: ClickProposition },
    If { condition: ClickProposition },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ProofArm {
    Left,
    Right,
}

impl ProofArm {
    fn index(self) -> usize {
        match self {
            Self::Left => 0,
            Self::Right => 1,
        }
    }
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
    theorem_environment: &'a TheoremEnvironment,
}

#[derive(Clone)]
struct ProofState {
    facts: ProofFacts,
    goal: Goal,
    complete: bool,
    added_facts: Arc<Vec<Proposition>>,
    checked_facts: Arc<Vec<Proposition>>,
    execution: Option<ExecutionProofState>,
}

/// Execution data whose unchanged pieces can be shared by checked `Proof`
/// successors. Pure facts live in `ProofState::facts`; this contains only the
/// frontier state, legacy replay metadata, and persistent branch provenance.
#[derive(Clone)]
struct ExecutionProofState {
    state: SharedValue<CState>,
    replay: TacticReplayState,
    branch_path: PersistentSequence<String>,
    last_step_delta: ExecutionProofStepDelta,
}

#[derive(Clone, Default)]
struct ExecutionProofStepDelta {
    function_entry_prerequisites: Vec<Proposition>,
    function_entry_derivations: Vec<Theorem>,
    unfolded_predicates: Vec<String>,
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

/// Persistent semantic fact state shared by every `Proof` kind.
///
/// The exact index serves local simple-step queries and `assumptions` retains
/// the kernel's incrementally updated reasoning context. Forking shares both;
/// adding one fact copies only logarithmic index/context paths.
#[derive(Clone, Default)]
pub(super) struct ProofFacts {
    ordered: PersistentSequence<Proposition>,
    prioritized: Option<Arc<PrioritizedProofFacts>>,
    top_level_exact: PersistentSet<Proposition>,
    exact: PersistentSet<Proposition>,
    /// Every strict subtree of an available top-level conjunction. This is
    /// the exact structural authority for `extract`; top-level facts are not
    /// included merely because they are independently available.
    proper_conjuncts: PersistentSet<Proposition>,
    /// Atomic exact facts after the same direct-load normalization used by
    /// condition replay. This lets a branch reject its opposite path with an
    /// indexed lookup instead of scanning every unrelated fact.
    normalized_exact: PersistentSet<Proposition>,
    by_snapshot_blind: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>>,
    by_quantified_replay: PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>>,
    implications_by_consequent:
        PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    assumptions: PureFactContext,
    implicit_transport_assumptions: PureFactContext,
    direct_lowering_assumptions: PureFactContext,
    by_predicate: PersistentMap<String, PersistentSequence<Proposition>>,
}

/// A statement transition places its explicitly transported successor facts
/// before the ambient facts retained at their original snapshots. Prefix
/// batches preserve that semantic order without copying the ambient sequence.
struct PrioritizedProofFacts {
    parent: Option<Arc<PrioritizedProofFacts>>,
    facts: Arc<Vec<Proposition>>,
}

/// One indexed prefix of an available implication chain. The consequent key
/// selects this small candidate; checking still validates every antecedent
/// and the exact/snapshot-equivalent consequent against the current facts.
#[derive(Clone)]
struct ImplicationCandidate {
    antecedents: PersistentSequence<Proposition>,
    consequent: Proposition,
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
        let facts = ProofFacts::from_ordered(requires);
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
        let facts = ProofFacts::from_ordered(available);
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

    /// Creates an execution-frontier proof whose C state, replay metadata,
    /// facts, and provenance are structurally shared by checked descendants.
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
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path,
        } = execution;
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
                theorem_environment,
            })),
            state: Arc::new(ProofState {
                facts: ProofFacts::from_ordered(&pure_facts),
                goal: Goal::ExecutionFrontier,
                complete: false,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
                execution: Some(ExecutionProofState {
                    state: state.into(),
                    replay,
                    branch_path,
                    last_step_delta: ExecutionProofStepDelta::default(),
                }),
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
            SimpleProofStep::Mark(name) => self.apply_execution_mark(name),
            SimpleProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            SimpleProofStep::StepUsing(premises) => self.apply_execution_statement_using(premises),
            SimpleProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            SimpleProofStep::UnfoldPredicate(name) => self.apply_execution_unfold(name),
            SimpleProofStep::Witness(witness) => self.apply_point_witness(witness),
            SimpleProofStep::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => self.apply_point_instantiate_using(quantified, argument, premises),
            SimpleProofStep::Extract(proposition) => self.apply_extract(proposition),
            SimpleProofStep::Rewrite(equality) => self.apply_rewrite(equality),
            SimpleProofStep::Assumption => self.apply_assumption(),
            SimpleProofStep::Normalize => self.apply_normalize(),
            SimpleProofStep::Intro => self.apply_intro(),
            SimpleProofStep::Split => self.apply_split(),
            SimpleProofStep::Left => self.apply_left(),
            SimpleProofStep::Right => self.apply_right(),
            SimpleProofStep::Enumerate => self.apply_enumerate(),
            SimpleProofStep::Contradiction(surface) => self.apply_contradiction(surface),
            SimpleProofStep::CloseInvariants => self.apply_close_invariants(),
            _ => {
                Err(self
                    .step_error("this simple step has not yet migrated to the checked `Proof` API"))
            }
        }?;

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

    #[inline(never)]
    fn apply_assumption(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`assumption` requires a proposition goal")?;
        if !self.state.facts.contains(goal) {
            return Err(self.step_error(format!(
                "`assumption` requires the exact current goal as an available fact: {:?}",
                goal
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_normalize(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`normalize` requires a proposition goal")?;
        if !normalizes_context_free(goal) {
            return Err(self.step_error(format!(
                "`normalize` requires a context-free true goal: {:?}",
                goal
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_intro(&self) -> Result<ProofState, ClickError> {
        let goal = self
            .proposition_goal("`intro` requires a proposition goal")?
            .clone();
        let (goal, introduced) = match goal {
            Proposition::Implies(antecedent, consequent) => (*consequent, Some(*antecedent)),
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
        Ok(ProofState {
            facts,
            goal: Goal::Proposition(Arc::new(goal)),
            complete: false,
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
            execution: None,
        })
    }

    #[inline(never)]
    fn apply_split(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`split` requires a proposition goal")?;
        let Proposition::And(left, right) = goal else {
            return Err(
                self.step_error(format!("`split` requires a conjunction goal, got {goal:?}"))
            );
        };
        if !self.state.facts.contains(left) || !self.state.facts.contains(right) {
            return Err(self.step_error(format!(
                "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_left(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`left` requires a proposition goal")?;
        let Proposition::Or(left, _) = goal else {
            return Err(
                self.step_error(format!("`left` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.state.facts.contains(left) {
            return Err(self.step_error(format!(
                "`left` requires its selected disjunct as an exact fact: {left:?}"
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_right(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`right` requires a proposition goal")?;
        let Proposition::Or(_, right) = goal else {
            return Err(
                self.step_error(format!("`right` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.state.facts.contains(right) {
            return Err(self.step_error(format!(
                "`right` requires its selected disjunct as an exact fact: {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_enumerate(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`enumerate` requires a proposition goal")?;
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Err(self.step_error(format!(
                "`enumerate` requires a constant-bounded universal goal, got {goal:?}"
            )));
        };
        for (_, instance) in instances {
            if !normalizes_context_free(&instance) && !self.state.facts.contains(&instance) {
                return Err(self.step_error(format!(
                    "`enumerate` requires an unavailable exact instance: {instance:?}"
                )));
            }
        }
        Ok(self.closed_state())
    }

    pub(super) fn certificate(&self) -> ProofCertificate {
        self.certificate_after_node(None)
            .expect("a complete proof derivation reaches its own root")
    }

    /// Retains an output-sensitive certificate suffix from an exact ancestor.
    ///
    /// Pointer identity, rather than structural equality, proves ancestry.
    /// A similarly shaped proof from another root or checking context cannot
    /// be spliced into this derivation.
    pub(super) fn certificate_since(
        &self,
        checkpoint: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        if !Arc::ptr_eq(&self.context, &checkpoint.context) {
            return Err(
                self.step_error("certificate checkpoint belongs to a different proof context")
            );
        }
        self.certificate_after_node(Some(&checkpoint.node))
    }

    /// Captures the current provenance position without sharing semantic
    /// execution state.
    pub(super) fn checkpoint(&self) -> ProofCheckpoint<'a> {
        ProofCheckpoint {
            context: self.context.clone(),
            node: self.node.clone(),
        }
    }

    /// Opens an exact disjunction into two immutable proof branches.
    ///
    /// This is a structural kernel operation, not a smart tactic: it accepts
    /// no derived or ambiently provable disjunction. Each arm receives only
    /// its corresponding exact disjunct in addition to the shared facts.
    pub(super) fn begin_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<ProofBranches<'a>, ClickError> {
        if self.state.complete {
            return Err(self.step_error("`cases` follows a completed proof"));
        }
        self.proposition_goal("`cases` requires a proposition goal")?;
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        if !self.state.facts.contains(&kernel) {
            return Err(self.step_error(format!(
                "`cases` requires its exact disjunction as an available fact: {kernel:?}"
            )));
        }
        let Proposition::Or(left, right) = kernel else {
            return Err(self.step_error(format!("`cases` requires a disjunction, got {kernel:?}")));
        };
        let root_checkpoint = self.checkpoint();
        Ok(ProofBranches {
            root: self.clone(),
            root_checkpoint,
            structure: ProofBranchStructure::Cases { disjunction },
            arms: [self.with_branch_fact(*left), self.with_branch_fact(*right)],
        })
    }

    /// Opens a proposition proof under a condition and its exact surface
    /// negation. Unlike `cases`, proof `if` is an audited logical split and
    /// does not require the condition to be an available fact beforehand.
    pub(super) fn begin_if(
        &self,
        condition: ClickProposition,
    ) -> Result<ProofBranches<'a>, ClickError> {
        if self.state.complete {
            return Err(self.step_error("`if` follows a completed proof"));
        }
        self.proposition_goal("proof `if` requires a proposition goal")?;
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let root_checkpoint = self.checkpoint();
        Ok(ProofBranches {
            root: self.clone(),
            root_checkpoint,
            structure: ProofBranchStructure::If { condition },
            arms: [
                self.with_branch_fact(then_fact),
                self.with_branch_fact(else_fact),
            ],
        })
    }

    /// Opens a nested proof for one surface proposition. The body has a fresh
    /// provenance root but shares the persistent semantic fact index and
    /// immutable checking context with its enclosing proof.
    pub(super) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        if self.state.complete {
            return Err(self.step_error("`have` follows a completed proof"));
        }
        self.proposition_goal("`have` requires a proposition proof context")?;
        let kernel = self.lower_surface_proposition(&proposition, "`have` proposition")?;
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                facts: self.state.facts.clone(),
                goal: Goal::Proposition(Arc::new(kernel.clone())),
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
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: ProofScopeStructure::Have {
                proposition,
                kernel,
            },
            body,
        })
    }

    /// Opens the C `if` at an execution frontier into its kernel-feasible
    /// checked arms.
    ///
    /// This is a structural operation rather than a surface `Step`: branch
    /// entry owns condition certification, path-fact admission, and movement
    /// to each selected arm. The enclosing `Branch` certificate is recorded
    /// only when those descendants join.
    pub(super) fn begin_execution_branch(&self) -> Result<ExecutionProofBranches<'a>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`branch` requires an execution-frontier proof"));
        };
        if self.state.complete || !matches!(self.state.goal, Goal::ExecutionFrontier) {
            return Err(self.step_error("`branch` requires an open execution frontier"));
        }
        let execution =
            self.state.execution.as_ref().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        let statement_index = execution.replay.frontier.next_statement_index;
        let source_region = execution
            .replay
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`branch` could not resolve source statement({statement_index})"
                ))
            })?;
        let SourceStatementKind::If {
            then_statement_index,
            else_statement_index,
        } = source_region.kind
        else {
            return Err(self.step_error(format!(
                "`branch` requires a C `if` at the execution frontier, but statement({statement_index}) is not an `if`"
            )));
        };
        let initial_continuation_depth = execution.replay.frontier.continuations.len();
        let (execution_start_state, current_state, statement, remaining) =
            next_top_level_statement_from_execution_point(
                &execution.replay,
                &execution.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(self.step_error("`branch` source region did not contain a C `if`"));
        };
        let transitions = certified_proof_condition_transitions(
            &current_state,
            &self.state.facts,
            &condition,
            &format!(
                "`{}` tactic {}: `branch`",
                context.claim_label, context.tactic_index
            ),
        )?;
        let mut arms: [Option<ExecutionProofArm<'a>>; 2] = [None, None];
        for transition in transitions {
            let take_then = transition.is_true;
            let selected_branch = if take_then {
                then_branch.as_ref()
            } else {
                else_branch.as_ref()
            };
            let mut arm_execution = execution.clone();
            arm_execution.replay.completed_branch_regions.clear();
            record_statement_program_point_state(
                &mut arm_execution.replay,
                context.function_block,
                statement_index,
                ProgramPointKind::Entry,
                current_state.clone(),
            );
            let resolved_state = crate::kernel::resolve_pending_heap_allocations(
                &current_state,
                transition.pure_facts.assumptions(),
            );
            arm_execution
                .replay
                .frontier
                .continuations
                .push(ProofExecutionContinuation {
                    remaining: remaining.clone().map(Arc::new),
                    next_statement_index: source_region.continuation_node,
                    kind: ProofExecutionContinuationKind::Branch { statement_index },
                });
            arm_execution.replay.frontier.next_statement_index = if take_then {
                then_statement_index
            } else {
                else_statement_index
            };
            arm_execution.replay.frontier.execution_start_state =
                Some(execution_start_state.clone());
            arm_execution.state = resolved_state.into();
            if matches!(selected_branch, CStatement::Skip) {
                let Some(remaining) = resume_after_completed_region(
                    &mut arm_execution.replay,
                    context.function_block,
                    &arm_execution.state,
                ) else {
                    return Err(self.step_error("`branch` reached function end without a return"));
                };
                arm_execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
                    remaining: remaining.into(),
                };
            } else {
                arm_execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
                    remaining: Arc::new(selected_branch.clone()),
                };
            }
            record_current_statement_entry(
                &mut arm_execution.replay,
                &arm_execution.state,
                context.function_block,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )?;
            arm_execution.replay.has_structured_branch_history = true;
            arm_execution.branch_path.push(format!(
                "{} arm of C `if` at statement({statement_index})",
                if take_then { "then" } else { "else" }
            ));
            let mut introduced_facts = PersistentOrderedSet::default();
            for fact in &transition.path_facts {
                introduced_facts.insert(fact.clone());
            }
            let arm = ExecutionProofArm {
                proof: Proof {
                    context: self.context.clone(),
                    state: Arc::new(ProofState {
                        facts: transition.pure_facts,
                        goal: Goal::ExecutionFrontier,
                        complete: false,
                        added_facts: Arc::new(transition.path_facts.clone()),
                        checked_facts: Arc::new(transition.path_facts.clone()),
                        execution: Some(arm_execution),
                    }),
                    // The structural certificate is owned by the container
                    // and installed atomically by the checked join.
                    node: self.node.clone(),
                },
                introduced_facts,
                introduced_effect_facts: Vec::new(),
                introduced_function_entry_prerequisites: PersistentOrderedSet::default(),
                introduced_function_entry_derivations: PersistentOrderedSet::default(),
                introduced_unfolded_predicates: PersistentOrderedSet::default(),
                condition_theorem: transition.theorem,
            };
            arms[usize::from(!take_then)] = Some(arm);
        }
        if arms.iter().all(Option::is_none) {
            return Err(self.step_error("`branch` found no feasible C `if` arm"));
        }
        Ok(ExecutionProofBranches {
            root: self.clone(),
            root_checkpoint: self.checkpoint(),
            statement_index,
            continuation_index: source_region.continuation_node,
            continuation_remaining: remaining.map(Arc::new),
            execution_start_state,
            initial_continuation_depth,
            arms,
        })
    }

    /// Independently checks an already-serialized simple certificate.
    ///
    /// This is for explicit source verification and expansion/audit, where
    /// replay is intentional. Smart tactics instead search with `apply_step`
    /// and the structural branch operations directly.
    pub(super) fn check_certificate(
        &self,
        certificate: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        enum CheckFrame<'certificate, 'proof> {
            Continue {
                steps: &'certificate [SimpleProofStep],
                next: usize,
            },
            BranchLeft {
                branches: ProofBranches<'proof>,
                right: &'certificate ProofCertificate,
            },
            BranchRight {
                branches: ProofBranches<'proof>,
            },
            Have {
                scope: ProofScope<'proof>,
            },
        }

        let mut proof = self.clone();
        let mut steps = certificate.steps();
        let mut next = 0;
        let mut frames = Vec::new();
        loop {
            if let Some(step) = steps.get(next) {
                next += 1;
                match step {
                    SimpleProofStep::Cases {
                        disjunction,
                        left_proof,
                        right_proof,
                    } => {
                        let branches = proof.begin_cases(disjunction.clone())?;
                        proof = branches.arms[ProofArm::Left.index()].clone();
                        frames.push(CheckFrame::Continue { steps, next });
                        frames.push(CheckFrame::BranchLeft {
                            branches,
                            right: right_proof,
                        });
                        steps = left_proof.steps();
                        next = 0;
                    }
                    SimpleProofStep::If {
                        condition,
                        then_proof,
                        else_proof,
                    } => {
                        let branches = proof.begin_if(condition.clone())?;
                        proof = branches.arms[ProofArm::Left.index()].clone();
                        frames.push(CheckFrame::Continue { steps, next });
                        frames.push(CheckFrame::BranchLeft {
                            branches,
                            right: else_proof,
                        });
                        steps = then_proof.steps();
                        next = 0;
                    }
                    SimpleProofStep::Have {
                        proposition,
                        proof: body,
                    } => {
                        let scope = proof.begin_have(proposition.clone())?;
                        proof = scope.body.clone();
                        frames.push(CheckFrame::Continue { steps, next });
                        frames.push(CheckFrame::Have { scope });
                        steps = body.steps();
                        next = 0;
                    }
                    _ => proof = proof.apply_step(step.clone())?,
                }
                continue;
            }

            let Some(frame) = frames.pop() else {
                return Ok(proof);
            };
            match frame {
                CheckFrame::Continue {
                    steps: continuation,
                    next: continuation_next,
                } => {
                    steps = continuation;
                    next = continuation_next;
                }
                CheckFrame::BranchLeft {
                    mut branches,
                    right,
                } => {
                    branches.arms[ProofArm::Left.index()] = proof;
                    proof = branches.arms[ProofArm::Right.index()].clone();
                    frames.push(CheckFrame::BranchRight { branches });
                    steps = right.steps();
                    next = 0;
                }
                CheckFrame::BranchRight { mut branches } => {
                    branches.arms[ProofArm::Right.index()] = proof;
                    proof = branches.join()?;
                    steps = &[];
                    next = 0;
                }
                CheckFrame::Have { mut scope } => {
                    scope.body = proof;
                    proof = scope.join()?;
                    steps = &[];
                    next = 0;
                }
            }
        }
    }

    fn certificate_after_node(
        &self,
        ancestor: Option<&Arc<ProofNode>>,
    ) -> Result<ProofCertificate, ClickError> {
        let expected_depth = ancestor.map_or(0, |node| node.depth);
        let mut steps = Vec::with_capacity(self.node.depth.saturating_sub(expected_depth));
        let mut node = Some(self.node.clone());
        while let Some(current) = node {
            if ancestor.is_some_and(|ancestor| Arc::ptr_eq(ancestor, &current)) {
                steps.reverse();
                return Ok(ProofCertificate::from_steps(steps));
            }
            if let Some(step) = &current.step {
                steps.push(step.as_ref().clone());
            }
            node = current.parent.clone();
        }
        if ancestor.is_some() {
            return Err(self.step_error("certificate checkpoint is not an ancestor of this proof"));
        }
        steps.reverse();
        Ok(ProofCertificate::from_steps(steps))
    }

    fn with_branch_fact(&self, fact: Proposition) -> Self {
        let mut facts = self.state.facts.clone();
        facts = facts.with_fact(fact.clone());
        Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                facts,
                goal: self.state.goal.clone(),
                complete: false,
                added_facts: Arc::new(vec![fact.clone()]),
                checked_facts: Arc::new(vec![fact]),
                execution: None,
            }),
            // The structural step is retained once at join. Arm certificates
            // begin after the shared root and contain only their checked body.
            node: self.node.clone(),
        }
    }

    fn lower_surface_proposition(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
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
                self.step_error(format!("could not lower {description}: {message}"))
            }),
            ProofContext::Point(context) => {
                if let Some(recorded) = context
                    .surface_propositions
                    .available_kernel(surface, context.lowering_context.as_ref())
                {
                    return Ok(recorded.clone());
                }
                lower_point_proposition_with_assumptions(
                    surface,
                    self.state.facts.assumptions(),
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
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::Execution(_) => Err(self.step_error(format!(
                "{description} is not an execution-frontier proposition"
            ))),
        }
    }

    fn apply_execution_unfold(&self, name: &String) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`unfold` requires an execution-frontier proof"));
        };
        let mut execution =
            self.state.execution.clone().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        let checked = check_unfold_predicate_facts(
            &mut execution.replay,
            &execution.state,
            &self.state.facts,
            name,
            context.function,
            context.arguments,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_function_entry_prerequisites,
            function_entry_derivations: checked.added_function_entry_derivations,
            unfolded_predicates: checked.added_unfolded_predicates,
        };
        Ok(ProofState {
            facts: checked.facts,
            goal: self.state.goal.clone(),
            complete: false,
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
            execution: Some(execution),
        })
    }

    pub(super) fn into_execution_context(self) -> Result<ProofReplayContext, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("proof does not own an execution frontier"));
        }
        let missing = format!(
            "`{}` proof step {}: execution-frontier successor lost its semantic state",
            self.context.claim_label(),
            self.node.depth
        );
        // This is a legacy compatibility/export boundary, not a semantic
        // transition. A smart tactic may legitimately retain any ancestor or
        // successor; materializing the selected checked state must therefore
        // not require unique ownership of the Proof.
        let mut state = Arc::unwrap_or_clone(self.state);
        let execution = state
            .execution
            .take()
            .ok_or_else(|| ClickError::new(missing))?;
        Ok(ProofReplayContext {
            state: execution.state.into_value(),
            pure_facts: state.facts.to_vec(),
            replay: execution.replay,
            branch_path: execution.branch_path,
        })
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
            ProofContext::Execution(context) => {
                self.apply_execution_theorem_using(context, application, surface_premises)
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
                lower_point_proposition_with_assumptions(
                    surface,
                    self.state.facts.assumptions(),
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

    fn apply_execution_theorem_using(
        &self,
        context: &ExecutionProofContext<'a>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let mut execution =
            self.state.execution.clone().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        let retain_function_entry_derivation = execution
            .replay
            .frontier
            .execution_start_state
            .as_ref()
            .is_none_or(|start| start == &*execution.state);
        let checked = check_point_theorem_application_using_facts(
            context.theorem_environment,
            application,
            surface_premises,
            context.claim_label,
            context.tactic_index,
            &self.state.facts,
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            &execution.state,
            &execution.replay,
            context.predicate_environment,
            context.click_function_environment,
            retain_function_entry_derivation,
        )?;
        if let Some(prerequisite) = checked.function_entry_prerequisite
            && !execution
                .replay
                .function_entry_execution_prerequisites
                .contains(&prerequisite)
        {
            execution
                .last_step_delta
                .function_entry_prerequisites
                .push(prerequisite.clone());
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(prerequisite);
        }
        if let Some(derivation) = checked.function_entry_derivation
            && !execution
                .replay
                .function_entry_derivations
                .contains(&derivation)
        {
            execution
                .last_step_delta
                .function_entry_derivations
                .push(derivation.clone());
            execution
                .replay
                .function_entry_derivations
                .insert(derivation);
        }
        Ok(ProofState {
            facts: checked.facts,
            goal: self.state.goal.clone(),
            complete: false,
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
            execution: Some(execution),
        })
    }

    fn apply_point_witness(&self, witness: &ProofWitness) -> Result<ProofState, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("`witness` requires a point proposition proof"));
        };
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let goal = unfold_predicates_in_proposition(
            context.predicate_environment,
            context.click_function_environment,
            context.unfolded_predicates,
            &goal,
            self.state.facts.assumptions(),
        )
        .map_err(|message| self.step_error(format!("could not unfold witness goal: {message}")))?;
        let values = parameter_values(context.parameters, context.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs =
            array_refs_for_parameters(context.parameters, &values, context.state.memory());
        let (values, array_refs) =
            contract_environment_at_state(&values, &array_refs, context.state);
        let value = evaluate_witness_tactic_value(
            witness,
            context.claim_label,
            0,
            context.tactic_index,
            &values,
            &array_refs,
            context.pre_state,
            context.state,
            None,
            self.state.facts.assumptions(),
            context.predicate_environment,
            context.click_function_environment,
            context.program_point_states,
        )?;
        let goal = apply_witness_tactic(
            witness,
            value,
            goal,
            context.claim_label,
            0,
            context.tactic_index,
        )?;
        Ok(ProofState {
            facts: self.state.facts.clone(),
            goal: Goal::Proposition(Arc::new(goal)),
            complete: false,
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
            execution: None,
        })
    }

    fn apply_point_instantiate_using(
        &self,
        surface_quantified: &ClickProposition,
        argument: &ContractExpression,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("`instantiate` requires a point proposition proof"));
        };
        self.proposition_goal("`instantiate` requires a proposition goal")?;

        let explicit_premises = surface_premises
            .iter()
            .map(|surface| self.lower_surface_proposition(surface, "`instantiate using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        for premise in &explicit_premises {
            if !self
                .state
                .facts
                .replay_available_across_effects(premise, &[])
            {
                return Err(self.step_error(format!(
                    "`instantiate using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        let lowered_quantified =
            self.lower_surface_proposition(surface_quantified, "`instantiate` quantified fact")?;
        let quantified = if self.state.facts.contains(&lowered_quantified) {
            lowered_quantified
        } else if let Some(available) = self
            .state
            .facts
            .matching_quantified_replay_fact(&lowered_quantified)
        {
            available
        } else {
            return Err(self.step_error(format!(
                "`instantiate` quantified fact is not exactly available: {}",
                describe_click_proposition(surface_quantified)
            )));
        };

        let parameter_values = parameter_values(context.parameters, context.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            context.parameters,
            &parameter_values,
            context.state.memory(),
        );
        let (values, array_refs) =
            contract_environment_at_state(&parameter_values, &array_refs, context.state);
        let mut active_functions = BTreeSet::new();
        let value = evaluate_contract_expression_with_environment(
            &values,
            &array_refs,
            context.pre_state,
            context.state,
            None,
            self.state.facts.assumptions(),
            argument,
            context.predicate_environment,
            context.click_function_environment,
            context.program_point_states,
            &mut active_functions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not evaluate `instantiate` argument: {message}"
            ))
        })?;
        let CValue::Int32(argument) = value else {
            return Err(self.step_error("`instantiate` argument did not evaluate to int32"));
        };

        let conclusion =
            check_forall_int32_instantiation(&quantified, argument, &explicit_premises)
                .map_err(|message| self.step_error(format!("`instantiate` failed: {message}")))?;
        let added = !self.state.facts.contains_top_level(&conclusion);
        let facts = self.state.facts.with_fact(conclusion.clone());
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        let added_facts = added.then_some(conclusion).into_iter().collect::<Vec<_>>();
        Ok(ProofState {
            facts,
            goal: self.state.goal.clone(),
            complete,
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
            execution: None,
        })
    }

    fn apply_rewrite(&self, surface_equality: &ClickProposition) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.apply_pure_rewrite(surface_equality),
            ProofContext::Point(context) => self.apply_point_rewrite(context, surface_equality),
            ProofContext::Execution(_) => {
                Err(self.step_error("`rewrite` requires a proposition proof"))
            }
        }
    }

    #[inline(never)]
    fn apply_pure_rewrite(
        &self,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let goal = Box::new(
            self.proposition_goal("`rewrite` requires a proposition goal")?
                .clone(),
        );
        let equality =
            Box::new(self.lower_surface_proposition(surface_equality, "`rewrite` equality")?);
        self.finish_rewrite(goal, equality)
    }

    #[inline(never)]
    fn apply_point_rewrite(
        &self,
        context: &PointProofContext<'_>,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let goal = Box::new(
            unfold_predicates_in_proposition(
                context.predicate_environment,
                context.click_function_environment,
                context.unfolded_predicates,
                self.proposition_goal("`rewrite` requires a proposition goal")?,
                self.state.facts.assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` goal: {message}"))
            })?,
        );
        let recorded = context
            .surface_propositions
            .available_kernel_matching(surface_equality, |kernel| {
                self.state.facts.materialization_available(kernel)
            })
            .map(|kernel| Box::new(kernel.clone()))
            .or_else(|| {
                let reverse = reverse_surface_equality(surface_equality)?;
                let kernel = context
                    .surface_propositions
                    .available_kernel_matching(&reverse, |kernel| {
                        self.state.facts.materialization_available(kernel)
                    })?
                    .clone();
                reverse_kernel_equality(kernel).map(Box::new)
            });
        let equality = match recorded {
            Some(equality) => equality,
            None => Box::new(
                lower_point_proposition_with_assumptions(
                    surface_equality,
                    self.state.facts.assumptions(),
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
                    self.step_error(format!("could not lower `rewrite` equality: {message}"))
                })?,
            ),
        };
        let equality = Box::new(
            unfold_predicates_in_proposition(
                context.predicate_environment,
                context.click_function_environment,
                context.unfolded_predicates,
                &equality,
                self.state.facts.assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` equality: {message}"))
            })?,
        );
        self.finish_rewrite(goal, equality)
    }

    #[inline(never)]
    fn finish_rewrite(
        &self,
        goal: Box<Proposition>,
        equality: Box<Proposition>,
    ) -> Result<ProofState, ClickError> {
        let admitted = self.state.facts.materialization_available(&equality)
            || reverse_kernel_equality(equality.as_ref().clone())
                .as_ref()
                .is_some_and(|reverse| self.state.facts.materialization_available(reverse));
        let available = if admitted {
            std::slice::from_ref(equality.as_ref())
        } else {
            &[]
        };
        let rewritten = rewrite_proposition_by_exact_equality(&goal, &equality, available)
            .map_err(|message| self.step_error(message))?;
        Ok(ProofState {
            facts: self.state.facts.clone(),
            goal: Goal::Proposition(Arc::new(rewritten)),
            complete: false,
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
            execution: None,
        })
    }

    fn apply_extract(&self, surface: &ClickProposition) -> Result<ProofState, ClickError> {
        if matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`extract` requires a proposition proof"));
        }
        let proposition = self.lower_surface_proposition(surface, "`extract` proposition")?;
        if !self.state.facts.contains_proper_conjunct(&proposition)
            && !self
                .state
                .facts
                .contains_discharged_implication_consequent(&proposition)
        {
            return Err(self.step_error(format!(
                "`extract` proposition is not a proper conjunct of an exact available fact or a discharged implication consequent: {}",
                describe_pure_fact(&proposition, &[], &[])
            )));
        }
        let added_facts = (!self.state.facts.contains_top_level(&proposition))
            .then(|| proposition.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = self.state.facts.with_fact(proposition);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            facts,
            goal: self.state.goal.clone(),
            complete,
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
            execution: None,
        })
    }

    fn apply_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Point(context) => {
                self.apply_point_transport_using(source, target, premises, context)
            }
            ProofContext::Execution(context) => {
                self.apply_execution_transport_using(source, target, premises, context)
            }
            ProofContext::Pure(_) => {
                Err(self.step_error("`transport using` requires a point or execution proof"))
            }
        }
    }

    fn apply_point_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        context: &PointProofContext<'a>,
    ) -> Result<ProofState, ClickError> {
        if self.node.depth != 0 {
            return Err(
                self.step_error("point `transport using` currently requires the root proof")
            );
        }
        let checked = check_point_fact_transport_using_facts(
            source,
            target,
            premises,
            context.claim_label,
            context.tactic_index,
            &self.state.facts,
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

    fn apply_execution_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        context: &ExecutionProofContext<'a>,
    ) -> Result<ProofState, ClickError> {
        let mut execution =
            self.state.execution.clone().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        let checked = check_point_fact_transport_using_facts(
            source,
            target,
            premises,
            context.claim_label,
            context.tactic_index,
            &self.state.facts,
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
        let mut facts = self.state.facts.clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        facts = facts.with_fact(checked.target);
        Ok(ProofState {
            facts,
            goal: self.state.goal.clone(),
            complete: false,
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
            execution: Some(execution),
        })
    }

    fn apply_execution_statement_using(
        &self,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step using` requires an execution-frontier proof"));
        };
        let mut execution =
            self.state.execution.clone().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let checked = check_step_using_facts(
            &mut execution.replay,
            &mut execution.state,
            &self.state.facts,
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
        )?;
        Ok(ProofState {
            facts: checked.facts,
            goal: self.state.goal.clone(),
            complete: false,
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
            execution: Some(execution),
        })
    }

    fn apply_execution_mark(&self, name: &str) -> Result<ProofState, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        let mut execution =
            self.state.execution.clone().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        let point = ProgramPointRef {
            region: CodeRegionRef::Mark(name.to_string()),
            kind: ProgramPointKind::Entry,
        };
        if execution.replay.program_point_states.contains_key(&point) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        execution
            .replay
            .program_point_states
            .insert(point, (*execution.state).clone());
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            facts: self.state.facts.clone(),
            goal: self.state.goal.clone(),
            complete: false,
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
            execution: Some(execution),
        })
    }

    fn apply_close_invariants(&self) -> Result<ProofState, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`close_invariants` requires an execution-frontier proof"));
        }
        let mut execution =
            self.state.execution.clone().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
        if !execution.replay.loop_invariant_region {
            return Err(
                self.step_error("`close_invariants` is only available in a loop-region proof")
            );
        }
        if execution.replay.region_invariants_closed {
            return Err(
                self.step_error("the invariant bundle was closed more than once on one path")
            );
        }
        execution.replay.region_invariants_closed = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            facts: self.state.facts.clone(),
            goal: self.state.goal.clone(),
            complete: false,
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
            execution: Some(execution),
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

impl<'a> ProofBranches<'a> {
    #[cfg(test)]
    pub(super) fn arm(&self, arm: ProofArm) -> &Proof<'a> {
        &self.arms[arm.index()]
    }

    /// Applies one ordinary checked step inside one arm while preserving the
    /// other arm and the shared root. Failed candidates leave `self` intact.
    #[allow(dead_code)]
    pub(super) fn apply_step(
        &self,
        arm: ProofArm,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.arms[arm.index()] = self.arms[arm.index()].apply_step(step)?;
        Ok(next)
    }

    /// Runs the shared direct smart closure search in one arm. The selected
    /// descendant is retained in the branch container; the other arm and the
    /// common root remain shared.
    pub(super) fn try_direct_logical_closure(&self, arm: ProofArm) -> Option<Self> {
        let mut next = self.clone();
        next.arms[arm.index()] = self.arms[arm.index()].try_direct_logical_closure()?;
        Some(next)
    }

    /// Joins two completed arms and records their retained bodies as one
    /// structured simple step on the shared root.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
        for (name, arm) in [("left", &self.arms[0]), ("right", &self.arms[1])] {
            if !arm.is_complete() {
                return Err(self
                    .root
                    .step_error(format!("cannot join `cases`: {name} arm is incomplete")));
            }
        }
        let left_proof = self.arms[0].certificate_since(&self.root_checkpoint)?;
        let right_proof = self.arms[1].certificate_since(&self.root_checkpoint)?;
        let step = match self.structure {
            ProofBranchStructure::Cases { disjunction } => SimpleProofStep::Cases {
                disjunction,
                left_proof: Box::new(left_proof),
                right_proof: Box::new(right_proof),
            },
            ProofBranchStructure::If { condition } => SimpleProofStep::If {
                condition,
                then_proof: Box::new(left_proof),
                else_proof: Box::new(right_proof),
            },
        };
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(self.root.closed_state()),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(step)),
                depth: self.root.node.depth + 1,
            }),
        })
    }
}

impl<'a> ExecutionProofBranches<'a> {
    pub(super) fn has_both_feasible_arms(&self) -> bool {
        self.arms.iter().all(Option::is_some)
    }

    #[cfg(test)]
    fn arm(&self, take_then: bool) -> Option<&Proof<'a>> {
        self.arms[usize::from(!take_then)]
            .as_ref()
            .map(|arm| &arm.proof)
    }

    /// Applies one checked simple step inside the selected C arm and retains
    /// only that step's semantic fact delta for the eventual join.
    pub(super) fn apply_step(
        mut self,
        take_then: bool,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        if !matches!(
            step,
            SimpleProofStep::StepUsing(_)
                | SimpleProofStep::TransportUsing { .. }
                | SimpleProofStep::UnfoldPredicate(_)
                | SimpleProofStep::ApplyTheoremUsing { .. }
        ) {
            return Err(self.root.step_error(
                "execution branch arms currently accept only `step using`, `transport using`, `unfold`, and `apply using`",
            ));
        }
        let arm_index = usize::from(!take_then);
        let mut arm = self.arms[arm_index].take().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot apply a step to the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        let prior_effect_count = arm
            .proof
            .state
            .execution
            .as_ref()
            .ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?
            .replay
            .effect_facts
            .len();
        arm.proof = arm.proof.apply_step(step)?;
        for fact in arm.proof.added_facts() {
            arm.introduced_facts.insert(fact.clone());
        }
        let execution = arm
            .proof
            .state
            .execution
            .as_ref()
            .expect("checked execution step retains semantic state");
        for fact in execution
            .replay
            .effect_facts
            .iter()
            .skip(prior_effect_count)
        {
            if !arm.introduced_effect_facts.contains(fact) {
                arm.introduced_effect_facts.push(fact.clone());
            }
        }
        for fact in &execution.last_step_delta.function_entry_prerequisites {
            arm.introduced_function_entry_prerequisites
                .insert(fact.clone());
        }
        for theorem in &execution.last_step_delta.function_entry_derivations {
            arm.introduced_function_entry_derivations
                .insert(theorem.clone());
        }
        for name in &execution.last_step_delta.unfolded_predicates {
            arm.introduced_unfolded_predicates.insert(name.clone());
        }
        self.arms[arm_index] = Some(arm);
        Ok(self)
    }

    /// Preserves the original empty-arm entry point for callers that require
    /// the branch to contain no body steps.
    pub(super) fn join_empty(self) -> Result<Proof<'a>, ClickError> {
        self.join_checked(true)
    }

    /// Joins two checked non-returning C branch arms at their shared frontier.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
        self.join_checked(false)
    }

    fn join_checked(self, require_empty: bool) -> Result<Proof<'a>, ClickError> {
        let [Some(then_arm), Some(else_arm)] = self.arms else {
            return Err(self.root.step_error(
                "an execution `branch` with one feasible arm is a decided path, not a join",
            ));
        };
        let validate_arm =
            |name: &str, expected: bool, arm: &ExecutionProofArm<'a>| -> Result<(), ClickError> {
                let body = arm.proof.certificate_since(&self.root_checkpoint)?;
                if require_empty && !body.steps().is_empty() {
                    return Err(self.root.step_error(format!(
                        "cannot use the empty execution join for a nonempty {name} arm"
                    )));
                }
                let execution = arm.proof.state.execution.as_ref().ok_or_else(|| {
                    self.root
                        .step_error(format!("{name} branch arm lost its execution state"))
                })?;
                if !execution
                    .replay
                    .completed_branch_regions
                    .contains(&self.statement_index)
                    || execution.replay.frontier.continuations.len()
                        > self.initial_continuation_depth
                    || execution.replay.frontier.next_statement_index != self.continuation_index
                {
                    return Err(self.root.step_error(format!(
                        "{name} branch arm has not reached its shared continuation"
                    )));
                }
                if !matches!(
                    implication_body(arm.condition_theorem.proposition()),
                    Proposition::CConditionEvaluates {
                        outcome: CConditionOutcome::Value(actual),
                        ..
                    } if *actual == expected
                ) {
                    return Err(self
                        .root
                        .step_error(format!("{name} arm retained the wrong condition theorem")));
                }
                Ok(())
            };
        validate_arm("then", true, &then_arm)?;
        validate_arm("else", false, &else_arm)?;
        let then_proof = then_arm.proof.certificate_since(&self.root_checkpoint)?;
        let else_proof = else_arm.proof.certificate_since(&self.root_checkpoint)?;
        let then_state = &then_arm
            .proof
            .state
            .execution
            .as_ref()
            .expect("validated then execution state")
            .state;
        let else_state = &else_arm
            .proof
            .state
            .execution
            .as_ref()
            .expect("validated else execution state")
            .state;
        if **then_state != **else_state {
            return Err(self
                .root
                .step_error("execution `branch` arms reached different C states"));
        }
        let continuation_remaining = self.continuation_remaining.ok_or_else(|| {
            self.root
                .step_error("execution `branch` has no shared continuation statement")
        })?;
        let root_execution = self.root.state.execution.as_ref().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        for (name, arm) in [("then", &then_arm), ("else", &else_arm)] {
            let replay = &arm
                .proof
                .state
                .execution
                .as_ref()
                .expect("validated branch execution state")
                .replay;
            if replay.function_entry_execution_prerequisites.len()
                != root_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .len()
                    + arm.introduced_function_entry_prerequisites.len()
                || replay.function_entry_derivations.len()
                    != root_execution.replay.function_entry_derivations.len()
                        + arm.introduced_function_entry_derivations.len()
                || replay.frontier_loop_clauses.len()
                    != root_execution.replay.frontier_loop_clauses.len()
                || replay.frontier_loop_rules.len()
                    != root_execution.replay.frontier_loop_rules.len()
                || replay.unfolded_predicates.len()
                    != root_execution.replay.unfolded_predicates.len()
                        + arm.introduced_unfolded_predicates.len()
                || replay.planned_statement_transitions.len()
                    != root_execution.replay.planned_statement_transitions.len()
            {
                return Err(self.root.step_error(format!(
                    "{name} execution arm changed replay metadata that the checked join has not migrated"
                )));
            }
        }
        let then_replay = &then_arm
            .proof
            .state
            .execution
            .as_ref()
            .expect("validated then execution state")
            .replay;
        let else_replay = &else_arm
            .proof
            .state
            .execution
            .as_ref()
            .expect("validated else execution state")
            .replay;
        let mut execution = root_execution.clone();
        execution.state = (**then_state).clone().into();
        execution.replay.completed_branch_regions.clear();
        execution
            .replay
            .completed_branch_regions
            .insert(self.statement_index);
        execution.replay.frontier.next_statement_index = self.continuation_index;
        execution.replay.frontier.execution_start_state = Some(self.execution_start_state);
        execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: continuation_remaining,
        };
        execution.replay.has_structured_branch_history = true;
        execution.replay.next_opaque_call = then_replay
            .next_opaque_call
            .max(else_replay.next_opaque_call);
        execution.replay.next_verification_variable = then_replay
            .next_verification_variable
            .max(else_replay.next_verification_variable);
        for effect in then_arm
            .introduced_effect_facts
            .iter()
            .chain(&else_arm.introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in then_arm
            .introduced_function_entry_prerequisites
            .iter()
            .chain(&else_arm.introduced_function_entry_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in then_arm
            .introduced_function_entry_derivations
            .iter()
            .chain(&else_arm.introduced_function_entry_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in then_arm
            .introduced_unfolded_predicates
            .iter()
            .chain(&else_arm.introduced_unfolded_predicates)
        {
            if !execution.replay.unfolded_predicates.contains(name) {
                execution.replay.unfolded_predicates.push(name.clone());
            }
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path.clear();
        execution.replay.case_assumptions.clear();
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_point_state(
            &mut execution.replay,
            context.function_block,
            self.statement_index,
            ProgramPointKind::Exit,
            (**then_state).clone(),
        );
        record_current_statement_entry(
            &mut execution.replay,
            &execution.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "branch",
        )?;

        let mut facts = self.root.state.facts.clone();
        let mut common_added_facts = Vec::new();
        for fact in &then_arm.introduced_facts {
            if else_arm.introduced_facts.contains(fact)
                && then_arm.proof.state.facts.contains(fact)
                && else_arm.proof.state.facts.contains(fact)
                && !facts.contains(fact)
            {
                facts = facts.with_fact(fact.clone());
                common_added_facts.push(fact.clone());
                for surface in then_replay.surface_propositions.surfaces(fact) {
                    if else_replay
                        .surface_propositions
                        .surfaces(fact)
                        .any(|candidate| candidate == surface)
                    {
                        execution
                            .replay
                            .surface_propositions
                            .record_lowering(surface, fact)?;
                    }
                }
            }
        }
        let step = SimpleProofStep::Branch {
            ensuring: None,
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        };
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                facts,
                goal: Goal::ExecutionFrontier,
                complete: false,
                added_facts: Arc::new(common_added_facts.clone()),
                checked_facts: Arc::new(common_added_facts),
                execution: Some(execution),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(step)),
                depth: self.root.node.depth + 1,
            }),
        })
    }
}

impl<'a> ProofScope<'a> {
    #[cfg(test)]
    pub(super) fn body(&self) -> &Proof<'a> {
        &self.body
    }

    /// Applies one ordinary checked step inside the nested body. Failed
    /// candidates leave the enclosing scope value unchanged.
    #[allow(dead_code)]
    pub(super) fn apply_step(&self, step: SimpleProofStep) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.body = self.body.apply_step(step)?;
        Ok(next)
    }

    /// Runs the small shared smart closure search inside the nested proof.
    /// Every accepted candidate still advances through `Proof::apply_step`.
    pub(super) fn try_direct_logical_closure(&self) -> Option<Self> {
        let mut next = self.clone();
        next.body = self.body.try_direct_logical_closure()?;
        Some(next)
    }

    /// Closes a completed nested proof and makes its checked proposition
    /// available in the enclosing proof while retaining the exact body.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
        if !self.body.is_complete() {
            return Err(self
                .root
                .step_error("cannot close `have`: nested proof is incomplete"));
        }
        let body = self.body.certificate();
        let ProofScopeStructure::Have {
            proposition,
            kernel,
        } = self.structure;
        let mut facts = self.root.state.facts.clone();
        facts = facts.with_fact(kernel.clone());
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                facts,
                goal: self.root.state.goal.clone(),
                complete: false,
                added_facts: Arc::new(vec![kernel.clone()]),
                checked_facts: Arc::new(vec![kernel]),
                execution: None,
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::Have {
                    proposition,
                    proof: Box::new(body),
                })),
                depth: self.root.node.depth + 1,
            }),
        })
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

impl ProofFacts {
    pub(super) fn from_ordered(facts: &[Proposition]) -> Self {
        let mut ordered = PersistentSequence::default();
        let mut top_level_exact = PersistentSet::default();
        let mut exact = PersistentSet::default();
        let mut proper_conjuncts = PersistentSet::default();
        let mut normalized_exact = PersistentSet::default();
        let mut by_snapshot_blind = PersistentMap::default();
        let mut by_quantified_replay = PersistentMap::default();
        let mut implications_by_consequent = PersistentMap::default();
        let mut assumptions = PureFactContext::new();
        let mut implicit_transport_assumptions = PureFactContext::new();
        let mut direct_lowering_assumptions = PureFactContext::new();
        let mut by_predicate = PersistentMap::default();
        for fact in facts {
            if top_level_exact.contains(fact) {
                continue;
            }
            ordered.push(fact.clone());
            top_level_exact = top_level_exact.with_value(fact.clone());
            by_quantified_replay = index_quantified_replay_fact(by_quantified_replay, fact);
            implications_by_consequent =
                index_implication_consequents(implications_by_consequent, fact);
            by_predicate = index_predicate_fact(by_predicate, fact);
            if matches!(fact, Proposition::And(_, _)) {
                proper_conjuncts = index_proper_conjuncts(proper_conjuncts, fact);
                let mut conjuncts = Vec::new();
                collect_owned_atomic_conjuncts(fact, &mut conjuncts);
                for conjunct in conjuncts {
                    by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                    let normalized = normalize_direct_atomic_memory_loads(&conjunct);
                    if normalized != conjunct {
                        normalized_exact = normalized_exact.with_value(normalized);
                    }
                    exact = exact.with_value(conjunct);
                }
            } else {
                let normalized = normalize_direct_atomic_memory_loads(fact);
                if normalized != *fact {
                    normalized_exact = normalized_exact.with_value(normalized);
                }
            }
            by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, fact);
            exact = exact.with_value(fact.clone());
            assumptions = assumptions.assume_proposition(fact.clone());
            (implicit_transport_assumptions, direct_lowering_assumptions) =
                index_transport_contexts(
                    implicit_transport_assumptions,
                    direct_lowering_assumptions,
                    fact,
                );
        }
        Self {
            ordered,
            prioritized: None,
            top_level_exact,
            exact,
            proper_conjuncts,
            normalized_exact,
            by_snapshot_blind,
            by_quantified_replay,
            implications_by_consequent,
            assumptions,
            implicit_transport_assumptions,
            direct_lowering_assumptions,
            by_predicate,
        }
    }

    pub(in crate::lang::click::proof) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
    }

    pub(super) fn contains_top_level(&self, fact: &Proposition) -> bool {
        self.top_level_exact.contains(fact)
    }

    pub(super) fn with_fact(&self, fact: Proposition) -> Self {
        if self.top_level_exact.contains(&fact) {
            return self.clone();
        }
        let mut exact = self.exact.clone();
        let mut proper_conjuncts = self.proper_conjuncts.clone();
        let mut normalized_exact = self.normalized_exact.clone();
        let mut by_snapshot_blind = self.by_snapshot_blind.clone();
        let by_quantified_replay =
            index_quantified_replay_fact(self.by_quantified_replay.clone(), &fact);
        let implications_by_consequent =
            index_implication_consequents(self.implications_by_consequent.clone(), &fact);
        if matches!(fact, Proposition::And(_, _)) {
            proper_conjuncts = index_proper_conjuncts(proper_conjuncts, &fact);
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                let normalized = normalize_direct_atomic_memory_loads(&conjunct);
                if normalized != conjunct {
                    normalized_exact = normalized_exact.with_value(normalized);
                }
                exact = exact.with_value(conjunct);
            }
        } else {
            let normalized = normalize_direct_atomic_memory_loads(&fact);
            if normalized != fact {
                normalized_exact = normalized_exact.with_value(normalized);
            }
        }
        by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &fact);
        exact = exact.with_value(fact.clone());
        let mut ordered = self.ordered.clone();
        ordered.push(fact.clone());
        let (implicit_transport_assumptions, direct_lowering_assumptions) =
            index_transport_contexts(
                self.implicit_transport_assumptions.clone(),
                self.direct_lowering_assumptions.clone(),
                &fact,
            );
        Self {
            ordered,
            prioritized: self.prioritized.clone(),
            top_level_exact: self.top_level_exact.with_value(fact.clone()),
            exact,
            proper_conjuncts,
            normalized_exact,
            by_snapshot_blind,
            by_quantified_replay,
            implications_by_consequent,
            assumptions: self.assumptions.clone().assume_proposition(fact.clone()),
            implicit_transport_assumptions,
            direct_lowering_assumptions,
            by_predicate: index_predicate_fact(self.by_predicate.clone(), &fact),
        }
    }

    pub(super) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    /// Exact proper-conjunct membership with the same condition-polarity
    /// equivalence as the legacy structural checker.
    pub(super) fn contains_proper_conjunct(&self, required: &Proposition) -> bool {
        self.proper_conjuncts.contains(required)
            || condition_polarity_spellings(required)
                .iter()
                .any(|spelling| self.proper_conjuncts.contains(spelling))
    }

    /// Exact or direct-load-materialization-equivalent availability used by
    /// the deterministic rewrite rule. Unlike snapshot replay, this does not
    /// admit polarity changes or a semantic bridge beyond normalization.
    pub(super) fn materialization_available(&self, required: &Proposition) -> bool {
        if self.exact.contains(required) {
            return true;
        }
        let normalized = normalize_direct_atomic_memory_loads(required);
        self.exact.contains(&normalized) || self.normalized_exact.contains(&normalized)
    }

    pub(super) fn implicit_transport_assumptions(&self) -> &PureFactContext {
        &self.implicit_transport_assumptions
    }

    pub(super) fn direct_lowering_assumptions(&self) -> &PureFactContext {
        &self.direct_lowering_assumptions
    }

    /// Adds one statement's selected successor context while retaining the
    /// old ambient order by shared prefix. The statement delta is explicit,
    /// so insertion work is proportional only to that delta and index height.
    pub(super) fn with_statement_facts(&self, facts: Vec<Proposition>) -> Self {
        let ordered = self.ordered.clone();
        let parent = self.prioritized.clone();
        let mut successor = self.clone();
        for fact in &facts {
            successor = successor.with_fact(fact.clone());
        }
        successor.ordered = ordered;
        successor.prioritized = Some(Arc::new(PrioritizedProofFacts {
            parent,
            facts: Arc::new(facts),
        }));
        successor
    }

    /// Availability accepted by explicit replay, answered from persistent
    /// indexes. Snapshot-blind buckets only select structurally compatible
    /// candidates; the kernel still proves every cross-snapshot match.
    pub(super) fn replay_available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.exact_available_across_effects(required, framing) {
            return true;
        }

        let normalized = normalize_direct_atomic_memory_loads(required);
        self.exact.contains(&normalized)
            || self.normalized_exact.contains(&normalized)
            || self.quantified_replay_available(required)
    }

    fn matching_quantified_replay_fact(&self, required: &Proposition) -> Option<Proposition> {
        quantified_replay_index_key(required)
            .and_then(|key| self.by_quantified_replay.get(&key))
            .into_iter()
            .flat_map(PersistentSequence::iter)
            .find(|candidate| {
                quantified_binder_equivalent(required, candidate)
                    || quantified_replay_equivalent_available_fact(
                        required,
                        std::slice::from_ref(candidate),
                    )
                    .is_some()
            })
            .cloned()
    }

    fn quantified_replay_available(&self, required: &Proposition) -> bool {
        self.matching_quantified_replay_fact(required).is_some()
    }

    fn contains_discharged_implication_consequent(&self, required: &Proposition) -> bool {
        let normalized = normalize_direct_atomic_memory_loads(required);
        let mut keys = vec![snapshot_blind_proposition_key(required)];
        let normalized_key = snapshot_blind_proposition_key(&normalized);
        if !keys.contains(&normalized_key) {
            keys.push(normalized_key);
        }
        keys.into_iter()
            .filter_map(|key| self.implications_by_consequent.get(&key))
            .flat_map(PersistentSequence::iter)
            .any(|candidate| {
                proposition_candidate_equals_modulo_proven_snapshots(
                    &candidate.consequent,
                    required,
                    &self.assumptions,
                    &[],
                ) && candidate
                    .antecedents
                    .iter()
                    .all(|antecedent| self.replay_available_across_effects(antecedent, &[]))
            })
    }

    pub(super) fn exact_available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.contains(required)
            || condition_polarity_spellings(required)
                .iter()
                .any(|spelling| self.exact.contains(spelling))
        {
            return true;
        }

        let normalized = normalize_direct_atomic_memory_loads(required);
        let keys = [
            snapshot_blind_proposition_key(required),
            snapshot_blind_proposition_key(&normalized),
        ];
        let mut candidates = Vec::new();
        for key in keys {
            if let Some(bucket) = self.by_snapshot_blind.get(&key) {
                for candidate in bucket.iter() {
                    if !candidates.contains(candidate) {
                        candidates.push(candidate.clone());
                    }
                }
            }
        }
        if candidates.is_empty() {
            return false;
        }
        snapshot_bridged_fact_is_available_under(required, &candidates, &self.assumptions, framing)
            || candidates.iter().any(|candidate| {
                proposition_candidate_equals_modulo_proven_snapshots(
                    candidate,
                    required,
                    &self.assumptions,
                    framing,
                )
            })
    }

    pub(super) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        let normalized = normalize_direct_atomic_memory_loads(fact);
        directly_conflicts_with_normalized_index(&self.exact, &normalized)
            || directly_conflicts_with_normalized_index(&self.normalized_exact, &normalized)
    }

    pub(super) fn to_vec(&self) -> Vec<Proposition> {
        let mut ordered = Vec::new();
        let mut seen = BTreeSet::new();
        let mut batch = self.prioritized.as_deref();
        while let Some(current) = batch {
            for fact in current.facts.iter() {
                if seen.insert(fact.clone()) {
                    ordered.push(fact.clone());
                }
            }
            batch = current.parent.as_deref();
        }
        for fact in self.ordered.iter() {
            if seen.insert(fact.clone()) {
                ordered.push(fact.clone());
            }
        }
        ordered
    }

    pub(super) fn mentioning_predicate(&self, name: &String) -> impl Iterator<Item = &Proposition> {
        self.by_predicate
            .get(name)
            .into_iter()
            .flat_map(PersistentSequence::iter)
    }

    #[cfg(test)]
    fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.exact.lookup_comparisons(fact)
    }
}

fn index_snapshot_fact(
    mut by_snapshot_blind: PersistentMap<
        SnapshotBlindPropositionKey,
        PersistentSequence<Proposition>,
    >,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>> {
    let normalized = normalize_direct_atomic_memory_loads(fact);
    for key in [
        snapshot_blind_proposition_key(fact),
        snapshot_blind_proposition_key(&normalized),
    ] {
        if !key.forgets_a_snapshot() {
            continue;
        }
        let mut bucket = by_snapshot_blind.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            by_snapshot_blind = by_snapshot_blind.with_inserted(key, bucket);
        }
    }
    by_snapshot_blind
}

fn index_quantified_replay_fact(
    mut index: PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>> {
    let Some(key) = quantified_replay_index_key(fact) else {
        return index;
    };
    let mut bucket = index.get(&key).cloned().unwrap_or_default();
    if !bucket.iter().any(|candidate| candidate == fact) {
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

fn index_implication_consequents(
    mut index: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>> {
    let mut antecedents = PersistentSequence::default();
    let mut current = fact;
    while let Proposition::Implies(antecedent, consequent) = current {
        antecedents.push(antecedent.as_ref().clone());
        let candidate = ImplicationCandidate {
            antecedents: antecedents.clone(),
            consequent: consequent.as_ref().clone(),
        };
        let normalized = normalize_direct_atomic_memory_loads(consequent);
        let mut keys = vec![snapshot_blind_proposition_key(consequent)];
        let normalized_key = snapshot_blind_proposition_key(&normalized);
        if !keys.contains(&normalized_key) {
            keys.push(normalized_key);
        }
        for key in keys {
            let mut bucket = index.get(&key).cloned().unwrap_or_default();
            bucket.push(candidate.clone());
            index = index.with_inserted(key, bucket);
        }
        current = consequent;
    }
    index
}

fn index_proper_conjuncts(
    mut index: PersistentSet<Proposition>,
    fact: &Proposition,
) -> PersistentSet<Proposition> {
    let Proposition::And(left, right) = fact else {
        return index;
    };
    for conjunct in [left.as_ref(), right.as_ref()] {
        index = index.with_value(conjunct.clone());
        index = index_proper_conjuncts(index, conjunct);
    }
    index
}

fn index_transport_contexts(
    mut implicit: PureFactContext,
    mut direct_lowering: PureFactContext,
    fact: &Proposition,
) -> (PureFactContext, PureFactContext) {
    if is_implicit_fact_transport_context(fact) {
        implicit = implicit.assume_proposition(fact.clone());
    }
    let mut conjuncts = Vec::new();
    collect_owned_atomic_conjuncts(fact, &mut conjuncts);
    for conjunct in conjuncts {
        if is_direct_surface_lowering_fact(&conjunct) {
            direct_lowering = direct_lowering.assume_proposition(conjunct);
        }
    }
    (implicit, direct_lowering)
}

fn directly_conflicts_with_normalized_index(
    exact: &PersistentSet<Proposition>,
    fact: &Proposition,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            directly_conflicts_with_normalized_index(exact, left)
                || directly_conflicts_with_normalized_index(exact, right)
        }
        Proposition::ConditionIs(condition, value) => {
            exact.contains(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => exact.contains(body),
        other => exact.contains(&Proposition::Not(Box::new(other.clone()))),
    }
}

fn index_predicate_fact(
    mut index: PersistentMap<String, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<String, PersistentSequence<Proposition>> {
    let mut names = BTreeSet::new();
    collect_fact_predicate_names(fact, &mut names);
    for name in names {
        let mut facts = index.get(&name).cloned().unwrap_or_default();
        facts.push(fact.clone());
        index = index.with_inserted(name, facts);
    }
    index
}

fn collect_fact_predicate_names(fact: &Proposition, names: &mut BTreeSet<String>) {
    match fact {
        Proposition::Predicate { name, .. } => {
            names.insert(name.clone());
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_fact_predicate_names(left, names);
            collect_fact_predicate_names(right, names);
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => collect_fact_predicate_names(body, names),
        _ => {}
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

    fn fact_node_allocations() -> usize {
        persistent_node_allocations()
    }

    fn opposite_atomic_fact(fact: &Proposition) -> Proposition {
        match fact {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => *body.clone(),
            other => Proposition::Not(Box::new(other.clone())),
        }
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
    fn certificate_suffix_requires_an_exact_shared_ancestor() {
        let fact = indexed_fact(7);
        let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "suffix",
            &[],
            goal.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let root_checkpoint = root.checkpoint();
        let introduced = root
            .apply_step(SimpleProofStep::Intro)
            .expect("intro should create the exact antecedent fact");
        let introduced_checkpoint = introduced.checkpoint();
        let complete = introduced
            .apply_step(SimpleProofStep::Assumption)
            .expect("the introduced fact should close the consequent");

        assert_eq!(
            complete
                .certificate_since(&root_checkpoint)
                .expect("root is an ancestor")
                .steps(),
            &[SimpleProofStep::Intro, SimpleProofStep::Assumption]
        );
        assert_eq!(
            complete
                .certificate_since(&introduced_checkpoint)
                .expect("introduced proof is an ancestor")
                .steps(),
            &[SimpleProofStep::Assumption]
        );
        assert!(
            root.certificate_since(&introduced_checkpoint).is_err(),
            "a descendant cannot be used as an ancestor checkpoint"
        );

        let unrelated = Proof::for_pure_goal(
            "suffix",
            &[],
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        assert!(
            complete.certificate_since(&unrelated.checkpoint()).is_err(),
            "a structurally identical but separately rooted proof cannot be spliced"
        );
    }

    #[test]
    fn cases_branches_join_only_completed_checked_arm_proofs() {
        let equality = |value| ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(value))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(value))),
        };
        let disjunction = ClickProposition::Or(Box::new(equality(0)), Box::new(equality(1)));
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
        };
        let kernel_disjunction = lower_pure_theorem_proposition(
            "cases",
            &disjunction,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant disjunction should lower");
        assert!(matches!(kernel_disjunction, Proposition::Or(_, _)));
        let root = Proof::for_pure_goal(
            "cases",
            std::slice::from_ref(&kernel_disjunction),
            kernel_disjunction.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let branches = root
            .begin_cases(disjunction.clone())
            .expect("the exact disjunction should open two cases");
        assert!(branches.clone().join().is_err());
        assert!(
            branches
                .apply_step(ProofArm::Left, SimpleProofStep::Intro)
                .is_err(),
            "a rejected arm candidate must not mutate the branch set"
        );
        assert!(
            branches
                .arm(ProofArm::Left)
                .certificate()
                .steps()
                .is_empty()
        );

        let branches = branches
            .apply_step(ProofArm::Left, SimpleProofStep::Left)
            .expect("left disjunct should close the left arm");
        assert!(branches.arm(ProofArm::Left).is_complete());
        assert!(!branches.arm(ProofArm::Right).is_complete());
        let branches = branches
            .apply_step(ProofArm::Right, SimpleProofStep::Right)
            .expect("right disjunct should close the right arm");
        let joined = branches.join().expect("both checked arms should join");
        assert!(joined.is_complete());
        assert_eq!(
            joined.certificate().steps(),
            &[SimpleProofStep::Cases {
                disjunction,
                left_proof: Box::new(ProofCertificate::from_steps(vec![SimpleProofStep::Left,])),
                right_proof: Box::new(ProofCertificate::from_steps(vec![SimpleProofStep::Right,])),
            }]
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn have_scope_publishes_only_a_completed_checked_body() {
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
        };
        let kernel = lower_pure_theorem_proposition(
            "have",
            &proposition,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");
        let root = Proof::for_pure_goal(
            "have",
            &[],
            kernel,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let scope = root
            .begin_have(proposition.clone())
            .expect("have should open a nested proposition proof");
        assert!(scope.clone().join().is_err());
        assert!(scope.apply_step(SimpleProofStep::Intro).is_err());
        assert!(scope.body().certificate().steps().is_empty());

        let scope = scope
            .apply_step(SimpleProofStep::Normalize)
            .expect("constant equality should normalize inside the body");
        let enclosing = scope.join().expect("completed body should close the scope");
        assert!(!enclosing.is_complete());
        assert_eq!(enclosing.added_facts().len(), 1);
        let complete = enclosing
            .apply_step(SimpleProofStep::Assumption)
            .expect("published have fact should close the enclosing goal");
        assert_eq!(
            complete.certificate().steps(),
            &[
                SimpleProofStep::Have {
                    proposition,
                    proof: Box::new(ProofCertificate::from_steps(vec![
                        SimpleProofStep::Normalize,
                    ])),
                },
                SimpleProofStep::Assumption,
            ]
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
    fn proof_fact_forks_share_context_and_local_insertions_are_logarithmic() {
        let mut allocation_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let facts = ProofFacts::from_ordered(&initial);
            let fork = facts.clone();
            assert!(facts.exact.shares_root_with(&fork.exact));
            assert!(
                facts
                    .assumptions
                    .shares_persistent_storage_with(&fork.assumptions)
            );

            let added = indexed_fact(size + 1);
            let before = fact_node_allocations();
            let successor = fork.with_fact(added.clone());
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            allocation_samples.push((size, logarithmic_height, allocations));
            assert!(!facts.contains(&added));
            assert!(successor.contains(&added));
            assert!(successor.assumptions.proves(&added));
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        assert!(
            base_allocations <= 48,
            "small persistent fact insertion allocated {base_allocations} nodes"
        );
        for (size, height, allocations) in allocation_samples {
            // A condition fact updates the exact and normalized indexes, the
            // kernel condition map, and the two endpoint maps in its signed
            // order index. Every one is an AVL path copy; adding two tree
            // levels may therefore add at most 24 nodes.
            let allocation_bound = base_allocations + 12 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} local insertion allocated {allocations} fact nodes (logarithmic bound {allocation_bound})"
            );
        }
    }

    #[test]
    fn statement_fact_prefix_preserves_successor_order_without_copying_ambient_history() {
        let first = indexed_fact(1);
        let promoted = indexed_fact(2);
        let added = indexed_fact(3);
        let facts = ProofFacts::from_ordered(&[first.clone(), promoted.clone()]);
        let ambient_tail = facts.ordered.clone();
        let successor = facts.with_statement_facts(vec![promoted.clone(), added.clone()]);

        assert!(successor.ordered.shares_tail_with(&ambient_tail));
        assert_eq!(successor.to_vec(), vec![promoted, added, first]);
    }

    #[test]
    fn replay_availability_probes_equivalent_condition_polarities_by_exact_index() {
        let left = Bitvector32Term::Variable(Variable(80_000));
        let right = Bitvector32Term::Variable(Variable(80_001));
        let available = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ),
            true,
        );
        let facts = ProofFacts::from_ordered(&[available]);
        for required in [
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(left.clone()),
                    Box::new(right.clone()),
                ),
                false,
            ),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(right.clone()),
                    Box::new(left.clone()),
                ),
                false,
            ),
            Proposition::Not(Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterThan(
                    Box::new(right.clone()),
                    Box::new(left.clone()),
                ),
                false,
            ))),
        ] {
            assert!(facts.replay_available_across_effects(&required, &[]));
        }
    }

    #[test]
    fn proof_fact_predicate_index_ignores_unrelated_context() {
        let name = "selected".to_string();
        let predicate = Proposition::Predicate {
            name: name.clone(),
            arguments: Vec::new(),
        };
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
            initial.push(predicate.clone());
            let facts = ProofFacts::from_ordered(&initial);
            let fork = facts.clone();

            assert!(facts.ordered.shares_tail_with(&fork.ordered));
            assert!(facts.exact.shares_root_with(&fork.exact));
            assert!(facts.by_predicate.shares_root_with(&fork.by_predicate));
            assert_eq!(facts.to_vec(), initial);
            assert_eq!(
                facts.mentioning_predicate(&name).collect::<Vec<_>>(),
                vec![&predicate]
            );
        }
    }

    #[test]
    fn proof_if_fork_and_join_work_is_logarithmic_in_unrelated_facts() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let surface_goal = ClickProposition::Or(
            Box::new(condition.clone()),
            Box::new(ClickProposition::Not(Box::new(condition.clone()))),
        );

        for size in [16_u32, 64, 256, 1024, 4096] {
            let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let theorem_context = PureTheoremContext {
                memory: CMemory::new(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires,
            };
            let goal = lower_pure_theorem_proposition(
                "branch scaling",
                &surface_goal,
                &theorem_context.values,
                &theorem_context.array_refs,
                &theorem_context.memory,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("excluded-middle goal should lower");
            let root = Proof::for_pure_goal(
                "branch scaling",
                &theorem_context.requires,
                goal,
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let before = fact_node_allocations();
            let branches = root
                .begin_if(condition.clone())
                .expect("proof if should create two checked arms");
            let branch_allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 8 * logarithmic_height + 16;
            assert!(
                branch_allocations <= allocation_bound,
                "size {size} branch fork allocated {branch_allocations} fact nodes (bound {allocation_bound})"
            );

            let joined = branches
                .apply_step(ProofArm::Left, SimpleProofStep::Left)
                .expect("the condition closes the then arm")
                .apply_step(ProofArm::Right, SimpleProofStep::Right)
                .expect("the exact negation closes the else arm")
                .join()
                .expect("both checked descendants should join");
            assert!(joined.is_complete());
            assert_eq!(joined.certificate().steps().len(), 1);
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::If { then_proof, else_proof, .. }]
                    if then_proof.steps() == [SimpleProofStep::Left]
                        && else_proof.steps() == [SimpleProofStep::Right]
            ));
            assert!(root.certificate().steps().is_empty());
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

    #[test]
    fn point_witness_refines_existential_transactionally_with_constant_local_work() {
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let variable = Variable(9_000_000);
        let expected = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::Constant(7)),
            ),
            true,
        );
        let goal = Proposition::Exists {
            name: "chosen".to_string(),
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(expected),
        };
        let witness = ProofWitness {
            name: "chosen".to_string(),
            value: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let root = Proof::for_point_goal(
                "persistent witness",
                0,
                &facts,
                goal.clone(),
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
            let retained_root = root.clone();
            let wrong_name = SimpleProofStep::Witness(ProofWitness {
                name: "other".to_string(),
                value: ContractExpression::CFragment(CExpression::Value(int32(7))),
            });
            let error = root
                .apply_step(wrong_name)
                .err()
                .expect("a mismatched witness must reject the candidate");
            assert!(error.message().contains("binds `chosen`"), "{error:?}");
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let before = fact_node_allocations();
            let refined = root
                .apply_step(SimpleProofStep::Witness(witness.clone()))
                .expect("the named int32 witness should refine the existential");
            let allocations = fact_node_allocations() - before;
            assert_eq!(
                allocations, 0,
                "size {size} witness should not alter the persistent fact index"
            );
            assert_eq!(
                refined.certificate().steps(),
                &[SimpleProofStep::Witness(witness.clone())]
            );
            assert!(refined.added_facts().is_empty());
            assert!(!refined.is_complete());
            let completed = refined
                .apply_step(SimpleProofStep::Normalize)
                .expect("the instantiated constant equality should normalize");
            assert!(completed.is_complete());
            assert_eq!(
                completed.certificate().steps(),
                &[
                    SimpleProofStep::Witness(witness.clone()),
                    SimpleProofStep::Normalize,
                ]
            );
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn pure_rewrite_uses_indexed_equality_availability_without_changing_facts() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let equality = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable("y".to_string())),
        };
        let unavailable = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("z".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable("w".to_string())),
        };
        let values = BTreeMap::from([
            (
                "x".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_100_000))),
            ),
            ("y".to_string(), int32(1)),
            (
                "z".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_100_001))),
            ),
            ("w".to_string(), int32(3)),
        ]);
        let base_context = PureTheoremContext {
            memory: CMemory::new(),
            values,
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
        };
        let kernel_equality = lower_pure_theorem_proposition(
            "persistent rewrite",
            &equality,
            &base_context.values,
            &base_context.array_refs,
            &base_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.push(kernel_equality.clone());
            let theorem_context = PureTheoremContext {
                requires: requires.clone(),
                ..base_context.clone()
            };
            let root = Proof::for_pure_goal(
                "persistent rewrite",
                &requires,
                kernel_equality.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let error = root
                .apply_step(SimpleProofStep::Rewrite(unavailable.clone()))
                .err()
                .expect("an unavailable equality must reject the candidate");
            assert!(
                error.message().contains("exact available fact"),
                "{error:?}"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let step = SimpleProofStep::Rewrite(equality.clone());
            let before = fact_node_allocations();
            let rewritten = root
                .apply_step(step.clone())
                .expect("the exact available equality should rewrite the goal");
            let allocations = fact_node_allocations() - before;
            assert_eq!(
                allocations, 0,
                "size {size} rewrite should not alter the persistent fact index"
            );
            assert_eq!(rewritten.certificate().steps(), &[step.clone()]);
            assert!(rewritten.added_facts().is_empty());
            assert!(!rewritten.is_complete());
            let complete = rewritten
                .apply_step(SimpleProofStep::Normalize)
                .expect("the rewritten constant equality should normalize");
            assert!(complete.is_complete());
            assert_eq!(
                complete.certificate().steps(),
                &[step.clone(), SimpleProofStep::Normalize]
            );
            let alternative = root
                .apply_step(step)
                .expect("the ancestor should remain usable for another descendant");
            assert_eq!(alternative.certificate(), rewritten.certificate());
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_extract_uses_persistent_proper_conjunct_membership() {
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(7))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let kernel = lower_point_proposition_with_assumptions(
            &surface,
            &PureFactContext::new(),
            &[],
            &[],
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");

        let merely_top_level = Proof::for_point_goal(
            "top-level is not a proper conjunct",
            0,
            std::slice::from_ref(&kernel),
            kernel.clone(),
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
        assert!(
            merely_top_level
                .apply_step(SimpleProofStep::Extract(surface.clone()))
                .is_err(),
            "an independently available fact is not extractable unless it is also a proper conjunct"
        );

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
            available.push(Proposition::And(
                Box::new(indexed_fact(size + 1)),
                Box::new(Proposition::And(
                    Box::new(kernel.clone()),
                    Box::new(indexed_fact(size + 2)),
                )),
            ));
            let root = Proof::for_point_goal(
                "persistent extract",
                0,
                &available,
                kernel.clone(),
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
            let retained_root = root.clone();
            let step = SimpleProofStep::Extract(surface.clone());
            let before = fact_node_allocations();
            let extracted = root
                .apply_step(step.clone())
                .expect("the nested proper conjunct should extract");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 32 * logarithmic_height + 128;
            assert!(
                allocations <= allocation_bound,
                "size {size} extract allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert_eq!(extracted.certificate().steps(), &[step]);
            assert_eq!(extracted.added_facts(), std::slice::from_ref(&kernel));
            assert!(extracted.is_complete());
        }
    }

    #[test]
    fn implication_extract_uses_indexed_consequent_and_alpha_equivalent_antecedent() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let target_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::from([(
                "x".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(8_000_000))),
            )]),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
        };
        let target = lower_pure_theorem_proposition(
            "indexed implication extract",
            &target_surface,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("target should lower");
        let universal = |variable| Proposition::ForAll {
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Variable(variable)),
                ),
                true,
            )),
        };
        let required_antecedent = universal(Variable(8_100_000));
        let available_antecedent = universal(Variable(8_200_000));
        let selected_implication = Proposition::Implies(
            Box::new(required_antecedent.clone()),
            Box::new(target.clone()),
        );

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size)
                .map(|index| {
                    Proposition::Implies(
                        Box::new(indexed_fact(100_000 + index)),
                        Box::new(indexed_fact(200_000 + index)),
                    )
                })
                .collect::<Vec<_>>();
            facts.push(available_antecedent.clone());
            facts.push(selected_implication.clone());
            let root = Proof::for_pure_goal(
                "indexed implication extract",
                &facts,
                target.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let target_key = snapshot_blind_proposition_key(&target);
            assert_eq!(
                root.state
                    .facts
                    .implications_by_consequent
                    .get(&target_key)
                    .expect("selected consequent should be indexed")
                    .len(),
                1,
                "unrelated implications must not enter the selected bucket"
            );
            let quantified_key = quantified_replay_index_key(&required_antecedent)
                .expect("a universal has an alpha-invariant key");
            assert_eq!(
                root.state
                    .facts
                    .by_quantified_replay
                    .get(&quantified_key)
                    .expect("alpha-equivalent antecedent should be indexed")
                    .len(),
                1
            );

            let step = SimpleProofStep::Extract(target_surface.clone());
            let before = fact_node_allocations();
            let extracted = root
                .apply_step(step.clone())
                .expect("the alpha-equivalent antecedent should discharge the implication");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 48 * logarithmic_height + 192;
            assert!(
                allocations <= allocation_bound,
                "size {size} implication extract allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert_eq!(extracted.certificate().steps(), &[step]);
            assert_eq!(extracted.added_facts(), std::slice::from_ref(&target));
            assert!(extracted.is_complete());

            let missing_antecedent = Proof::for_pure_goal(
                "missing implication antecedent",
                std::slice::from_ref(&selected_implication),
                target.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            assert!(
                missing_antecedent
                    .apply_step(SimpleProofStep::Extract(target_surface.clone()))
                    .is_err(),
                "an indexed consequent does not bypass its antecedent"
            );
            assert!(missing_antecedent.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_instantiate_uses_indexed_universal_and_only_named_guards() {
        let parsed_function = syntax::parse_function("int32 selected(int32 x) { return x; }")
            .expect("test function should parse");
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let x_value = CValue::Int32(Bitvector32Term::Variable(Variable(8_700_000)));
        let arguments = vec![CExpression::Value(x_value)];
        let value = |constant| ContractExpression::CFragment(CExpression::Value(int32(constant)));
        let variable =
            |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
        let premise = ClickProposition::Comparison {
            left: variable("x"),
            operator: ComparisonOperator::LessEqual,
            right: value(7),
        };
        let goal_surface = ClickProposition::Comparison {
            left: value(7),
            operator: ComparisonOperator::Equal,
            right: value(7),
        };
        let quantified_surface = ClickProposition::ForAll {
            c_type: C0Type::Int32,
            name: "k".to_string(),
            body: Box::new(ClickProposition::Implies(
                Box::new(ClickProposition::Comparison {
                    left: variable("x"),
                    operator: ComparisonOperator::LessEqual,
                    right: variable("k"),
                }),
                Box::new(ClickProposition::Comparison {
                    left: variable("k"),
                    operator: ComparisonOperator::Equal,
                    right: variable("k"),
                }),
            )),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("test proposition should lower")
        };
        let kernel_premise = lower(&premise);
        let kernel_goal = lower(&goal_surface);
        let kernel_quantified = lower(&quantified_surface);

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
            available.push(kernel_premise.clone());
            available.push(kernel_quantified.clone());
            let root = Proof::for_point_goal(
                "indexed instantiate",
                0,
                &available,
                kernel_goal.clone(),
                parsed_function.parameters(),
                &arguments,
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
            let retained_root = root.clone();
            let key = quantified_replay_index_key(&kernel_quantified)
                .expect("the selected universal should have an alpha key");
            assert_eq!(
                root.state
                    .facts
                    .by_quantified_replay
                    .get(&key)
                    .expect("the selected universal should be indexed")
                    .len(),
                1,
                "unrelated facts must not enter the selected universal bucket"
            );

            let omitted = SimpleProofStep::InstantiateUsing {
                quantified: quantified_surface.clone(),
                argument: value(7),
                premises: Vec::new(),
            };
            assert!(
                root.apply_step(omitted).is_err(),
                "ambient availability must not discharge an omitted guard"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let step = SimpleProofStep::InstantiateUsing {
                quantified: quantified_surface.clone(),
                argument: value(7),
                premises: vec![premise.clone()],
            };
            let before = fact_node_allocations();
            let instantiated = root
                .apply_step(step.clone())
                .expect("the indexed universal and named guard should instantiate");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 48 * logarithmic_height + 192;
            assert!(
                allocations <= allocation_bound,
                "size {size} instantiate allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(instantiated.is_complete());
            assert_eq!(instantiated.certificate().steps(), &[step]);
            assert_eq!(
                instantiated.added_facts(),
                std::slice::from_ref(&kernel_goal)
            );
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn execution_apply_uses_only_named_evidence_and_forks_persistently() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test theorem and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let state = CState::new();
        let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_000_000)));
        let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_000_001)));
        let arguments = vec![CExpression::Value(left.clone())];
        let premise = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let conclusion = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let kernel_premise = lower_point_proposition_with_assumptions(
            &premise,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the exact premise should lower");
        let kernel_conclusion = lower_point_proposition_with_assumptions(
            &conclusion,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the theorem conclusion should lower");
        let application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: vec![
                ContractExpression::CFragment(CExpression::Value(left)),
                ContractExpression::CFragment(CExpression::Value(right)),
            ],
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(kernel_premise.clone());
            let root = Proof::for_execution_frontier(
                "persistent theorem application",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay: TacticReplayState::default(),
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let omitted = root
                .apply_step(SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: Vec::new(),
                })
                .err()
                .expect("ambient facts must not discharge an omitted named premise");
            assert!(
                omitted.message().contains("required exact fact"),
                "{omitted:?}"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let step = SimpleProofStep::ApplyTheoremUsing {
                application: application.clone(),
                premises: vec![premise.clone()],
            };
            let before = fact_node_allocations();
            let applied = root
                .apply_step(step.clone())
                .expect("the exact named premise should certify the application");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 32 * logarithmic_height + 128;
            assert!(
                allocations <= allocation_bound,
                "size {size} theorem application allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(applied.certificate().steps(), &[step.clone()]);
            assert_eq!(
                applied.added_facts(),
                std::slice::from_ref(&kernel_conclusion)
            );
            let root_execution = root.state.execution.as_ref().expect("root execution state");
            let applied_execution = applied
                .state
                .execution
                .as_ref()
                .expect("application successor execution state");
            assert!(
                root_execution
                    .state
                    .shares_storage_with(&applied_execution.state),
                "theorem application does not alter the C state"
            );
            assert!(
                root_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .len()
                    == 0
            );
            assert!(
                applied_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .contains(&kernel_conclusion)
            );
            assert_eq!(
                applied_execution
                    .last_step_delta
                    .function_entry_prerequisites,
                vec![kernel_conclusion.clone()]
            );
            assert_eq!(
                applied_execution
                    .last_step_delta
                    .function_entry_derivations
                    .len(),
                1
            );
            let alternative = root
                .apply_step(step)
                .expect("the retained ancestor should support another checked descendant");
            assert_eq!(alternative.certificate(), applied.certificate());
            assert!(root.certificate().steps().is_empty());
            let result = applied
                .into_execution_context()
                .expect("the checked successor should export at the compatibility boundary");
            assert!(result.pure_facts.contains(&kernel_conclusion));
        }
    }

    #[test]
    fn execution_unfold_forks_persistently_and_ignores_unrelated_facts() {
        let click_file = crate::lang::click::parse(
            r#"
                predicate selected(x: int32) { x == x }
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test predicate and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let state = CState::new();
        let argument = CExpression::Value(CValue::Int32(Bitvector32Term::Constant(7)));
        let arguments = vec![argument.clone()];
        let surface = ClickProposition::PredicateCall {
            name: "selected".to_string(),
            arguments: vec![ContractExpression::CFragment(argument)],
        };
        let predicate = Proposition::Predicate {
            name: "selected".to_string(),
            arguments: vec![
                Term::CState(state.clone()),
                Term::CValue(CValue::Int32(Bitvector32Term::Constant(7))),
            ],
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(predicate.clone());
            let mut replay = TacticReplayState::default();
            replay
                .surface_propositions
                .record_lowering(&surface, &predicate)
                .expect("the selected predicate spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "persistent unfold",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let successor = root
                .apply_step(SimpleProofStep::UnfoldPredicate("selected".to_string()))
                .expect("the exact selected predicate should unfold");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 32 * logarithmic_height + 128;
            assert!(
                allocations <= allocation_bound,
                "size {size} unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
            );

            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert_eq!(root.state.facts.to_vec().len(), size as usize + 1);
            assert_eq!(root.certificate().steps(), &[]);
            assert_eq!(
                successor.certificate().steps(),
                &[SimpleProofStep::UnfoldPredicate("selected".to_string())]
            );
            assert!(successor.state.facts.to_vec().len() > root.state.facts.to_vec().len());
            let root_execution = root.state.execution.as_ref().expect("root execution state");
            let successor_execution = successor
                .state
                .execution
                .as_ref()
                .expect("successor execution state");
            assert!(
                root_execution
                    .state
                    .shares_storage_with(&successor_execution.state),
                "unfold does not alter the C frontier"
            );
            assert!(
                root_execution
                    .replay
                    .proof_certificate_builder
                    .shares_storage_with(&successor_execution.replay.proof_certificate_builder),
                "unfold does not copy unrelated certificate history"
            );
            assert!(
                root_execution
                    .replay
                    .effect_facts
                    .shares_storage_with(&successor_execution.replay.effect_facts),
                "unfold does not copy unrelated effect history"
            );

            let context = successor
                .into_execution_context()
                .expect("a sole successor should materialize its legacy boundary context");
            assert!(
                context
                    .replay
                    .unfolded_predicates
                    .contains(&"selected".to_string())
            );
            assert!(context.pure_facts.len() > size as usize + 1);
        }
    }

    #[test]
    fn execution_transport_forks_without_copying_unrelated_state() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let state = CState::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(7))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let kernel = lower_point_proposition_with_assumptions(
            &surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower at the execution point");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(kernel.clone());
            let mut replay = TacticReplayState::default();
            replay
                .surface_propositions
                .record_lowering(&surface, &kernel)
                .expect("the source spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "persistent transport",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let step = SimpleProofStep::TransportUsing {
                source: surface.clone(),
                target: surface.clone(),
                premises: vec![surface.clone()],
            };
            let successor = root
                .apply_step(step.clone())
                .expect("an exact identity transport should succeed");

            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert_eq!(root.certificate().steps(), &[]);
            assert_eq!(successor.certificate().steps(), &[step]);
            assert!(successor.added_facts().is_empty());
            let root_execution = root.state.execution.as_ref().expect("root execution state");
            let successor_execution = successor
                .state
                .execution
                .as_ref()
                .expect("successor execution state");
            assert!(
                root_execution
                    .state
                    .shares_storage_with(&successor_execution.state),
                "transport does not alter the C state"
            );
            assert!(
                root_execution
                    .replay
                    .proof_certificate_builder
                    .shares_storage_with(&successor_execution.replay.proof_certificate_builder),
                "transport does not copy unrelated certificate history"
            );
            assert!(
                root_execution
                    .replay
                    .effect_facts
                    .shares_storage_with(&successor_execution.replay.effect_facts),
                "transport does not copy unrelated effect history"
            );
            assert_eq!(
                root_execution.replay.surface_propositions,
                successor_execution.replay.surface_propositions,
                "an identity transport does not change the recorded surface lowerings"
            );
        }
    }

    #[test]
    fn checked_statement_step_ignores_unrelated_proof_facts() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 constant(int32 x) {
                    ensures returns_one: result == 1 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 constant(int32 x) { return 1; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let unavailable = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let mut samples = Vec::new();

        for size in [16_u32, 64, 256, 1024, 4096] {
            let replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            let root = Proof::for_execution_frontier(
                "persistent statement step",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let marked = root
                .apply_step(SimpleProofStep::Mark("candidate".to_string()))
                .expect("a fresh proof mark should produce a checked descendant");
            assert!(matches!(
                marked.certificate().steps(),
                [SimpleProofStep::Mark(name)] if name == "candidate"
            ));
            let duplicate = marked
                .apply_step(SimpleProofStep::Mark("candidate".to_string()))
                .err()
                .expect("a duplicate mark must reject the candidate");
            assert!(duplicate.message().contains("duplicate proof mark"));
            assert!(matches!(
                marked.certificate().steps(),
                [SimpleProofStep::Mark(name)] if name == "candidate"
            ));
            let error = root
                .apply_step(SimpleProofStep::StepUsing(vec![unavailable.clone()]))
                .err()
                .expect("an unavailable explicit premise must reject the candidate");
            assert!(error.message().contains("requires an exact premise"));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let before = fact_node_allocations();
            let completed = root
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("an explicit return step should certify");
            let allocations = fact_node_allocations() - before;
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                allocations,
            ));
            assert!(
                completed
                    .state
                    .execution
                    .as_ref()
                    .expect("statement successor retains execution")
                    .replay
                    .is_at_function_exit()
            );
            assert!(matches!(
                completed.certificate().steps(),
                [SimpleProofStep::StepUsing(premises)] if premises.is_empty()
            ));
            let alternative = root
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the retained ancestor should support another checked descendant");
            assert_eq!(alternative.certificate(), completed.certificate());
            let root_execution = root.state.execution.as_ref().expect("root execution state");
            let completed_execution = completed
                .state
                .execution
                .as_ref()
                .expect("statement successor retains execution state");
            assert!(
                root_execution
                    .state
                    .shares_nonlocal_storage_with(&completed_execution.state),
                "a return step should not copy unchanged memory, resources, or populations"
            );
            let retained_completed = completed.clone();
            let exported = completed
                .into_execution_context()
                .expect("a shared checked successor should export at the legacy boundary");
            assert!(exported.replay.is_at_function_exit());
            assert!(matches!(
                retained_completed.certificate().steps(),
                [SimpleProofStep::StepUsing(premises)] if premises.is_empty()
            ));
        }

        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let logarithmic_bound = base_allocations + 24 * (height - base_height);
            assert!(
                allocations <= logarithmic_bound,
                "size {size} statement step allocated {allocations} persistent nodes (logarithmic bound {logarithmic_bound})"
            );
        }
    }

    #[test]
    fn close_invariants_is_a_transactional_constant_local_proof_step() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 loop_region(int32 x) {
                    ensures unchanged: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 loop_region(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];

        for size in [16_u32, 64, 256, 1024, 4096] {
            let make_root = |loop_invariant_region| {
                let replay = TacticReplayState {
                    loop_invariant_region,
                    ..TacticReplayState::default()
                };
                Proof::for_execution_frontier(
                    "persistent close invariants",
                    0,
                    ProofReplayContext {
                        state: CState::new(),
                        pure_facts: (0..size).map(indexed_fact).collect(),
                        replay,
                        branch_path: PersistentSequence::default(),
                    },
                    function_block,
                    &function,
                    &parsed_function,
                    &arguments,
                    &function_environment,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                )
            };

            let outside_loop = make_root(false);
            assert!(
                outside_loop
                    .apply_step(SimpleProofStep::CloseInvariants)
                    .is_err(),
                "the step is restricted to loop-region proofs"
            );
            assert!(outside_loop.certificate().steps().is_empty());

            let root = make_root(true);
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .apply_step(SimpleProofStep::CloseInvariants)
                .expect("the first close should produce a checked descendant");
            assert_eq!(fact_node_allocations() - before, 0);
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert_eq!(
                closed.certificate().steps(),
                &[SimpleProofStep::CloseInvariants]
            );
            let execution = closed
                .state
                .execution
                .as_ref()
                .expect("the successor retains execution state");
            assert!(execution.replay.region_invariants_closed);
            assert!(
                execution.replay.invariant_closer_step.is_none(),
                "source timing metadata is attached only at the replay adapter boundary"
            );
            assert!(closed.apply_step(SimpleProofStep::CloseInvariants).is_err());
            assert_eq!(
                closed.certificate().steps(),
                &[SimpleProofStep::CloseInvariants]
            );
        }
    }

    #[test]
    fn proof_condition_split_filters_conflicts_without_rebuilding_facts() {
        let symbolic = Variable(50_000);
        let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(symbolic)));
        let condition = CExpression::LessThan(
            Box::new(CExpression::Variable("x".to_string())),
            Box::new(CExpression::Value(int32(0))),
        );
        let empty = ProofFacts::default();
        let unconstrained = certified_proof_condition_transitions(
            &state,
            &empty,
            &condition,
            "persistent condition split",
        )
        .expect("a symbolic comparison should expose both paths");
        assert_eq!(unconstrained.len(), 2);
        let rejected_path_fact = unconstrained[0]
            .path_facts
            .first()
            .expect("a symbolic branch path should carry its condition fact")
            .clone();
        let selecting_fact = opposite_atomic_fact(&rejected_path_fact);

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
            available.push(selecting_fact.clone());
            let facts = ProofFacts::from_ordered(&available);
            assert!(facts.directly_conflicts_with(&rejected_path_fact));
            let before = fact_node_allocations();
            let transitions = certified_proof_condition_transitions(
                &state,
                &facts,
                &condition,
                "persistent condition split",
            )
            .expect("the selected condition path should certify");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 24 * logarithmic_height + 64;
            assert!(
                allocations <= allocation_bound,
                "size {size} condition split allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(transitions.len(), 1);
            assert_ne!(transitions[0].is_true, unconstrained[0].is_true);
            assert!(transitions[0].pure_facts.contains(&selecting_fact));
            assert!(matches!(
                implication_body(transitions[0].theorem.proposition()),
                Proposition::CConditionEvaluates { .. }
            ));
            assert_eq!(facts.to_vec().len(), size as usize + 1);
        }
    }

    #[test]
    fn empty_execution_branch_joins_checked_proof_arms_at_the_shared_frontier() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function =
            syntax::parse_function("int32 identity(int32 x) { if (x < 0) {} else {} return x; }")
                .expect("test C branch should parse");
        let function = parsed_function.to_kernel_function();
        let argument =
            CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(60_000))));
        let arguments = vec![argument];
        let function_environment = CExecutionEnvironment::new();
        let mut allocation_samples = Vec::new();
        let mut statement_delta: Option<Vec<Proposition>> = None;
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            let root = Proof::for_execution_frontier(
                "empty branch proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let before = fact_node_allocations();
            let branches = root
                .begin_execution_branch()
                .expect("symbolic condition should open two checked arms");
            assert!(branches.arm(true).is_some());
            assert!(branches.arm(false).is_some());
            let joined = branches
                .join_empty()
                .expect("identical empty arms should rejoin");
            let allocations = fact_node_allocations() - before;
            allocation_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                allocations,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: None,
                    then_proof,
                    else_proof,
                }] if then_proof.steps().is_empty() && else_proof.steps().is_empty()
            ));
            assert!(root.certificate().steps().is_empty());
            let execution = joined
                .state
                .execution
                .as_ref()
                .expect("joined proof should own its continuation");
            assert!(execution.replay.completed_branch_regions.contains(&0));
            assert_eq!(execution.branch_path.len(), 0);
            let completed = joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the joined continuation should execute its return");
            assert!(
                completed
                    .added_facts()
                    .iter()
                    .all(|fact| { !(0..size).any(|index| *fact == indexed_fact(index)) })
            );
            if let Some(expected) = &statement_delta {
                assert_eq!(completed.added_facts(), expected.as_slice());
            } else {
                statement_delta = Some(completed.added_facts().to_vec());
            }
            assert!(
                completed
                    .state
                    .execution
                    .as_ref()
                    .expect("completed proof retains execution state")
                    .replay
                    .is_at_function_exit()
            );
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        assert!(base_allocations <= 160);
        for (size, height, allocations) in allocation_samples {
            let allocation_bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} checked execution branch allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
            );
        }
    }

    #[test]
    fn nonempty_execution_branch_retains_checked_arm_steps_at_the_join() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 constant(int32 x) {
                    ensures returns_one: result == 1 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 constant(int32 x) { if (x < 0) { x = 1; } else { x = 1; } return x; }",
        )
        .expect("test C branch should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(70_000)),
        ))];
        let function_environment = CExecutionEnvironment::new();
        let mut allocation_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            let root = Proof::for_execution_frontier(
                "nonempty branch proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let branches = root
                .begin_execution_branch()
                .expect("symbolic condition should open two checked arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("then assignment should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("else assignment should check");
            let before = fact_node_allocations();
            let joined = branches
                .join()
                .expect("identical checked assignment arms should rejoin");
            allocation_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: None,
                    then_proof,
                    else_proof,
                }] if matches!(then_proof.steps(), [SimpleProofStep::StepUsing(_)])
                    && matches!(else_proof.steps(), [SimpleProofStep::StepUsing(_)])
            ));
            let completed = joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the joined continuation should execute its return");
            assert!(
                completed
                    .state
                    .execution
                    .as_ref()
                    .expect("completed proof retains execution state")
                    .replay
                    .is_at_function_exit()
            );
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        for (size, height, allocations) in allocation_samples {
            let allocation_bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} nonempty branch join allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
            );
        }
    }
}
