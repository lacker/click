//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

use super::{PersistentOrderedSet, PersistentSequence, ProofFacts, SharedValue, SharedVec};
use crate::kernel::{
    CConditionOutcome, CExpression, CFunction, CFunctionExecutionCandidates, CLoopEffectCheck,
    CState, CStatement, CStatementOutcome, CValue, CVerifiedLoopRule, ExecutionBudget,
    ExecutionLimit, ExecutionPureFact, Proposition, PureFactContext, ResourceContext,
    SpecProposition, Theorem,
};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

/// The typed identity of the execution region a frontier executes.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum ExecutionRegionKind {
    #[default]
    Function,
    LoopBody,
    /// One arm of a C `if`: exhausting the arm reaches its typed boundary.
    BranchArm,
}

/// One checked loop-effect obligation carried by an execution proof.
#[derive(Clone)]
pub(crate) struct LoopEffectGoal {
    pub(crate) before_state: CState,
    pub(crate) check: CLoopEffectCheck,
    pub(crate) closed: bool,
}

/// Kernel-issued evidence for one semantic C transition accepted by this
/// proof path.
///
/// The proof driver may choose which feasible transition to take, but it
/// cannot manufacture either theorem. Retaining the exact theorem here lets
/// function-exit certification check the chosen path without executing the C
/// body again.
#[derive(Clone)]
pub(crate) enum CheckedExecutionEvent {
    Statement(Theorem),
    Condition(Theorem),
    Branch(CheckedExecutionBranch),
    ProofCase(CheckedProofCaseArm),
}

/// Kernel-issued evidence for the exact contract-entry state from which a
/// function proof begins. In particular, this retains population materialization
/// instead of asking finalization to reconstruct it from Surface bookkeeping.
#[derive(Clone)]
pub(crate) struct CheckedFunctionEntry {
    caller_state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    entry_state: CState,
}

impl CheckedFunctionEntry {
    fn check(
        caller_state: &CState,
        function: &CFunction,
        arguments: &[CExpression],
        expected_entry_state: &CState,
    ) -> Option<Arc<Self>> {
        let entry_state = crate::kernel::c_function_entry_state(caller_state, function, arguments)?;
        if &entry_state != expected_entry_state {
            return None;
        }
        Some(Arc::new(Self {
            caller_state: caller_state.clone(),
            function: function.clone(),
            arguments: arguments.to_vec(),
            entry_state,
        }))
    }

    pub(crate) fn entry_state_for(
        &self,
        caller_state: &CState,
        function: &CFunction,
        arguments: &[CExpression],
        assumptions: &PureFactContext,
    ) -> Option<CState> {
        if &self.function != function || self.arguments != arguments {
            return None;
        }
        if &self.caller_state == caller_state {
            return Some(self.entry_state.clone());
        }
        let rebased_entry =
            crate::kernel::c_function_entry_state(caller_state, function, arguments)?;
        crate::kernel::api::function_entry_representation_states_match(
            function,
            &self.entry_state,
            &rebased_entry,
            assumptions,
        )
        .then_some(rebased_entry)
    }

    pub(crate) fn resource_relation_assumptions(
        &self,
        assumptions: &PureFactContext,
    ) -> Option<PureFactContext> {
        let Some((_, propositions)) =
            crate::kernel::functions::expand_all_composite_resource_facts_and_propositions(
                self.entry_state.resources(),
                self.function.composite_resource_definitions(),
                self.entry_state.memory(),
                assumptions,
            )
        else {
            return None;
        };
        Some(
            propositions
                .into_iter()
                .fold(assumptions.clone(), |facts, proposition| {
                    facts.assume_proposition(proposition)
                }),
        )
    }

    pub(crate) fn caller_state(&self) -> &CState {
        &self.caller_state
    }
}

/// One kernel-issued complementary logical partition over an unchanged C
/// execution frontier.
#[derive(Clone)]
pub(crate) struct CheckedProofCasePartition {
    identity: Arc<()>,
    root_facts: ProofFacts,
    case_facts: [Proposition; 2],
}

/// One arm of a checked logical partition. This event advances no C source;
/// it changes only the authoritative fact context for later evidence.
#[derive(Clone)]
pub(crate) struct CheckedProofCaseArm {
    partition: Arc<CheckedProofCasePartition>,
    arm_index: usize,
    facts: ProofFacts,
}

impl CheckedProofCasePartition {
    pub(crate) fn check(
        root_facts: &ProofFacts,
        then_fact: Proposition,
        else_fact: Proposition,
    ) -> Option<Arc<Self>> {
        let negated_then = Proposition::Not(Box::new(then_fact.clone()));
        if else_fact != negated_then
            && !super::fact_reasoning::condition_polarity_forms(&negated_then).contains(&else_fact)
        {
            return None;
        }
        Some(Arc::new(Self {
            identity: Arc::new(()),
            root_facts: root_facts.clone(),
            case_facts: [then_fact, else_fact],
        }))
    }
}

impl CheckedProofCaseArm {
    pub(crate) fn identity(&self) -> usize {
        Arc::as_ptr(&self.partition.identity) as usize
    }

    pub(crate) fn arm_index(&self) -> usize {
        self.arm_index
    }

    pub(crate) fn facts(&self) -> &ProofFacts {
        &self.facts
    }

    pub(crate) fn case_fact(&self) -> &Proposition {
        &self.partition.case_facts[self.arm_index]
    }

    pub(crate) fn is_valid(&self) -> bool {
        self.arm_index < 2
            && self
                .facts
                .introduced_since(&self.partition.root_facts)
                .is_some_and(|introduced| {
                    introduced == vec![self.partition.case_facts[self.arm_index].clone()]
                })
    }
}

/// One exhaustive nonterminal C `if`, checked against its exact source arms
/// and retained as a nested execution-evidence node.
#[derive(Clone)]
pub(crate) struct CheckedExecutionBranch {
    split: CheckedBranchSplit,
    arms: [CheckedExecutionBranchArm; 2],
    joined_state: CState,
    interface_successor_facts: Option<ProofFacts>,
}

#[derive(Clone)]
struct CheckedExecutionBranchArm {
    facts: ProofFacts,
    events: Vec<CheckedExecutionEvent>,
}

impl CheckedExecutionBranch {
    #[allow(clippy::too_many_arguments)]
    fn check(
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
    ) -> Result<Self, &'static str> {
        let condition = &split.condition;
        let parent_at_unstepped_function_entry = parent.frontier.is_at_function_entry()
            && parent.execution_evidence.len() == 1
            && parent.execution_evidence[0].is_empty();
        if split.state != *parent.state && !parent_at_unstepped_function_entry {
            return Err("the branch split does not start at the parent execution state");
        }
        if parent.execution_evidence.len() != 1 {
            return Err("the branch parent does not have one execution trace");
        }
        if arms.iter().any(|arm| arm.execution_evidence.len() != 1) {
            return Err("a branch arm does not have one execution trace");
        }
        if arms.iter().any(|arm| !arm.frontier.is_at_region_boundary()) {
            return Err("a branch arm has not reached its typed boundary");
        }
        if *arms[0].state != *arms[1].state {
            return Err("the branch arms do not have one joined state");
        }
        if !split.validates_exhaustive_join(
            &split.state,
            condition,
            root_facts,
            [Some(arm_theorems[0]), Some(arm_theorems[1])],
            [Some(arm_facts[0]), Some(arm_facts[1])],
        ) {
            return Err("the branch arms do not exhaust the checked condition split");
        }
        let parent_trace = &parent.execution_evidence[0];
        let full_source = prepend_checked_evidence_statement(
            split.branch_statement.clone(),
            split.continuation.clone(),
        );
        let mut checked_arms = Vec::with_capacity(2);
        for (index, arm) in arms.iter().enumerate() {
            let events = arm.execution_evidence[0]
                .suffix_since(parent_trace)
                .ok_or("a branch arm trace does not descend from the parent trace")?;
            // Even an empty source arm has this condition event. Its exact
            // theorem also fixes the arm's polarity through the checked split.
            if !matches!(
                events.first(),
                Some(CheckedExecutionEvent::Condition(theorem)) if theorem == arm_theorems[index]
            ) {
                return Err("a branch arm does not begin with its checked condition theorem");
            }
            let progress = check_evidence_events(
                &events,
                arm_facts[index],
                split.state.clone(),
                Some(full_source.clone()),
            )
            .ok_or("a branch arm theorem trace does not follow its exact C source")?;
            if progress.completed.is_some() || progress.remaining != split.continuation {
                return Err("a branch arm theorem trace does not reach the shared continuation");
            }
            if progress.state != *arm.state {
                return Err("a branch arm theorem trace does not reach its recorded state");
            }
            checked_arms.push(CheckedExecutionBranchArm {
                facts: arm_facts[index].clone(),
                events,
            });
        }
        let [then_arm, else_arm] = checked_arms
            .try_into()
            .map_err(|_| "the checked branch does not have exactly two arms")?;
        Ok(Self {
            split,
            arms: [then_arm, else_arm],
            joined_state: (*arms[0].state).clone(),
            interface_successor_facts: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_interface(
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        stable_join_locals: &BTreeMap<String, CValue>,
        interface_specs: &[SpecProposition],
        joined_state: &CState,
        successor_facts: &ProofFacts,
    ) -> Result<Self, &'static str> {
        let parent_at_unstepped_function_entry = parent.frontier.is_at_function_entry()
            && parent.execution_evidence.len() == 1
            && parent.execution_evidence[0].is_empty();
        if split.state != *parent.state && !parent_at_unstepped_function_entry {
            return Err("the interface split does not start at the parent state");
        }
        if parent.execution_evidence.len() != 1
            || arms.iter().any(|arm| arm.execution_evidence.len() != 1)
        {
            return Err("the interface branch does not have one trace per frontier");
        }
        if arms.iter().any(|arm| !arm.frontier.is_at_region_boundary()) {
            return Err("an interface arm has not reached its typed boundary");
        }
        if !split.validates_exhaustive_join(
            &split.state,
            &split.condition,
            root_facts,
            [Some(arm_theorems[0]), Some(arm_theorems[1])],
            [Some(arm_facts[0]), Some(arm_facts[1])],
        ) {
            return Err("the interface arms do not exhaust the checked condition split");
        }

        let expected_stable_locals = arms[0]
            .state
            .locals()
            .object_values()
            .filter(|(name, value)| arms[1].state.locals().get(name) == Some(*value))
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        if &expected_stable_locals != stable_join_locals {
            return Err("the interface stable-local set is not exact");
        }
        let mut continuation_variables = BTreeSet::new();
        if let Some(continuation) = &split.continuation {
            collect_c_statement_variable_names(continuation, &mut continuation_variables);
        }
        if continuation_variables
            .iter()
            .any(|name| !stable_join_locals.contains_key(name))
        {
            return Err("the interface continuation reads an abstracted local");
        }
        let sibling_states = [&*arms[0].state, &*arms[1].state];
        let abstract_then = crate::kernel::abstract_c_state_for_interface_join_across(
            &arms[0].state,
            &sibling_states,
            stable_join_locals,
        )
        .map_err(|_| "the then interface state could not be abstracted")?;
        let abstract_else = crate::kernel::abstract_c_state_for_interface_join_across(
            &arms[1].state,
            &sibling_states,
            stable_join_locals,
        )
        .map_err(|_| "the else interface state could not be abstracted")?;
        if abstract_then != abstract_else {
            return Err("the interface arms do not have one deterministic abstraction");
        }
        if joined_state
            .clone()
            .with_resource_context(ResourceContext::new())
            != abstract_then
        {
            return Err("the interface successor is not the checked arm abstraction");
        }
        for (arm, facts) in arms.iter().zip(arm_facts) {
            if arm
                .state
                .resources()
                .clone()
                .without_facts(joined_state.resources().facts(), facts.assumptions())
                .is_none()
            {
                return Err("the interface successor resources are not owned by both arms");
            }
        }

        let reference_state = parent
            .frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(&split.state);
        for spec in interface_specs {
            for (arm, facts) in arms.iter().zip(arm_facts) {
                if !interface_spec_is_established(spec, &arm.state, reference_state, facts) {
                    return Err("an interface fact is not established by both concrete arms");
                }
            }
            if !interface_spec_is_established(spec, joined_state, reference_state, successor_facts)
            {
                return Err("an interface fact is not retained at the abstract successor");
            }
        }
        let introduced = successor_facts
            .introduced_since(root_facts)
            .ok_or("the interface successor facts do not descend from the branch root")?;
        for fact in introduced {
            let common_arm_fact = arm_facts
                .iter()
                .all(|facts| facts.assumptions().proves(&fact));
            let interface_fact = interface_specs
                .iter()
                .any(|spec| interface_spec_lowers_to(spec, joined_state, reference_state, &fact));
            if !common_arm_fact && !interface_fact {
                return Err("the interface successor contains an unchecked new fact");
            }
        }

        let parent_trace = &parent.execution_evidence[0];
        let full_source = prepend_checked_evidence_statement(
            split.branch_statement.clone(),
            split.continuation.clone(),
        );
        let mut checked_arms = Vec::with_capacity(2);
        for (index, arm) in arms.iter().enumerate() {
            let events = arm.execution_evidence[0]
                .suffix_since(parent_trace)
                .ok_or("an interface arm trace does not descend from the parent trace")?;
            if !matches!(
                events.first(),
                Some(CheckedExecutionEvent::Condition(theorem)) if theorem == arm_theorems[index]
            ) {
                return Err("an interface arm does not begin with its checked condition theorem");
            }
            let progress = check_evidence_events(
                &events,
                arm_facts[index],
                split.state.clone(),
                Some(full_source.clone()),
            )
            .ok_or("an interface arm trace does not follow its exact C source")?;
            if progress.completed.is_some() || progress.remaining != split.continuation {
                return Err("an interface arm trace does not reach the shared continuation");
            }
            if progress.state != *arm.state {
                return Err("an interface arm trace does not reach its recorded state");
            }
            checked_arms.push(CheckedExecutionBranchArm {
                facts: arm_facts[index].clone(),
                events,
            });
        }
        let [then_arm, else_arm] = checked_arms
            .try_into()
            .map_err(|_| "the checked interface branch does not have exactly two arms")?;
        Ok(Self {
            split,
            arms: [then_arm, else_arm],
            joined_state: joined_state.clone(),
            interface_successor_facts: Some(successor_facts.clone()),
        })
    }

    pub(crate) fn matches_source(
        &self,
        state: &CState,
        branch_statement: &CStatement,
        continuation: &Option<CStatement>,
    ) -> bool {
        &self.split.state == state
            && &self.split.branch_statement == branch_statement
            && &self.split.continuation == continuation
    }

    pub(crate) fn joined_state(&self) -> &CState {
        &self.joined_state
    }

    pub(crate) fn start_state(&self) -> &CState {
        &self.split.state
    }

    pub(crate) fn arm_facts(&self, index: usize) -> &ProofFacts {
        &self.arms[index].facts
    }

    pub(crate) fn arm_events(&self, index: usize) -> &[CheckedExecutionEvent] {
        &self.arms[index].events
    }

    pub(crate) fn interface_successor_facts(&self) -> Option<&ProofFacts> {
        self.interface_successor_facts.as_ref()
    }
}

fn collect_c_expression_variable_names(expression: &CExpression, names: &mut BTreeSet<String>) {
    match expression {
        CExpression::Value(_) => {}
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::AddressOf(body)
        | CExpression::Not(body)
        | CExpression::Load(body)
        | CExpression::BitwiseNot(body) => collect_c_expression_variable_names(body, names),
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_variable_names(pointer, names);
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_c_expression_variable_names(left, names);
            collect_c_expression_variable_names(right, names);
        }
    }
}

fn collect_c_statement_variable_names(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip | CStatement::Declare { .. } | CStatement::HeapAllocate { .. } => {}
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        } => collect_c_expression_variable_names(expression, names),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_variable_names(argument, names);
            }
        }
        CStatement::HeapFree { pointer } => collect_c_expression_variable_names(pointer, names),
        CStatement::Seq(first, second) => {
            collect_c_statement_variable_names(first, names);
            collect_c_statement_variable_names(second, names);
        }
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            collect_c_expression_variable_names(pointer, names);
            collect_c_expression_variable_names(value, names);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_variable_names(condition, names);
            collect_c_statement_variable_names(then_branch, names);
            collect_c_statement_variable_names(else_branch, names);
        }
        CStatement::While {
            condition, body, ..
        } => {
            collect_c_expression_variable_names(condition, names);
            collect_c_statement_variable_names(body, names);
        }
    }
}

fn interface_spec_paths(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
) -> Option<Vec<crate::kernel::spec::SpecPropositionPath>> {
    crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
        state,
        spec,
        Some(reference_state),
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
    )
    .ok()
}

fn interface_spec_is_established(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
    facts: &ProofFacts,
) -> bool {
    interface_spec_paths(spec, state, reference_state).is_some_and(|paths| {
        paths.into_iter().any(|path| {
            facts.assumptions().proves(&path.proposition)
                && path
                    .facts
                    .iter()
                    .all(|fact| facts.assumptions().proves(fact.proposition()))
                && path
                    .obligations
                    .iter()
                    .all(|obligation| facts.assumptions().proves(obligation.proposition()))
        })
    })
}

fn interface_spec_lowers_to(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
    expected: &Proposition,
) -> bool {
    interface_spec_paths(spec, state, reference_state)
        .is_some_and(|paths| paths.iter().any(|path| &path.proposition == expected))
}

/// One path retained from a complete kernel C-condition evaluation.
#[derive(Clone)]
pub(crate) struct CheckedBranchPath {
    outcome: CConditionOutcome,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<crate::kernel::ProofObligation>,
    theorem: Theorem,
}

impl CheckedBranchPath {
    pub(crate) fn outcome(&self) -> &CConditionOutcome {
        &self.outcome
    }

    pub(crate) fn facts(&self) -> &[ExecutionPureFact] {
        &self.facts
    }

    pub(crate) fn obligations(&self) -> &[crate::kernel::ProofObligation] {
        &self.obligations
    }

    pub(crate) fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

/// Kernel-issued complete evaluation of one C branch condition at one exact
/// checked proof-fact root.
///
/// This retains every symbolic path, including paths later proved infeasible
/// and error outcomes. Only [`Self::validates_exhaustive_join`] converts it
/// into arm-coverage authority, after checking the original state, condition,
/// fact root, path prerequisites, and one-for-one feasible theorem coverage.
#[derive(Clone)]
pub(crate) struct CheckedBranchSplit {
    state: CState,
    branch_statement: CStatement,
    continuation: Option<CStatement>,
    condition: CExpression,
    root_facts: ProofFacts,
    paths: Vec<CheckedBranchPath>,
}

pub(crate) enum CheckedBranchSplitError {
    Limit(ExecutionLimit),
    InvalidEvidence,
}

impl CheckedBranchSplit {
    pub(crate) fn check(
        state: CState,
        branch_statement: CStatement,
        continuation: Option<CStatement>,
        root_facts: &ProofFacts,
    ) -> Result<Self, CheckedBranchSplitError> {
        let CStatement::If { condition, .. } = &branch_statement else {
            return Err(CheckedBranchSplitError::InvalidEvidence);
        };
        let condition = condition.clone();
        let evaluation = crate::kernel::prove_symbolic_c_condition_evaluation(
            state.clone(),
            condition.clone(),
            root_facts.assumptions().clone(),
        );
        if let Some(limit) = evaluation.limit() {
            return Err(CheckedBranchSplitError::Limit(limit));
        }
        let paths = evaluation
            .paths()
            .iter()
            .filter_map(|path| {
                let mut conclusion = path.theorem().proposition();
                while let Proposition::Implies(_, body) = conclusion {
                    conclusion = body;
                }
                let Proposition::CConditionEvaluates {
                    state: proved_state,
                    condition: proved_condition,
                    outcome,
                } = conclusion
                else {
                    return None;
                };
                if proved_state != &state || proved_condition != &condition {
                    return None;
                }
                Some(CheckedBranchPath {
                    outcome: outcome.clone(),
                    facts: path.facts().to_vec(),
                    obligations: path.obligations().to_vec(),
                    theorem: path.theorem().clone(),
                })
            })
            .collect::<Vec<_>>();
        if paths.len() != evaluation.paths().len() {
            return Err(CheckedBranchSplitError::InvalidEvidence);
        }
        Ok(Self {
            state,
            branch_statement,
            continuation,
            condition,
            root_facts: root_facts.clone(),
            paths,
        })
    }

    pub(crate) fn paths(&self) -> &[CheckedBranchPath] {
        &self.paths
    }

    fn has_exact_root(&self, root_facts: &ProofFacts) -> bool {
        self.root_facts
            .introduced_since(root_facts)
            .is_some_and(|delta| delta.is_empty())
            && root_facts
                .introduced_since(&self.root_facts)
                .is_some_and(|delta| delta.is_empty())
    }

    pub(crate) fn validates_exhaustive_join(
        &self,
        state: &CState,
        condition: &CExpression,
        root_facts: &ProofFacts,
        arm_theorems: [Option<&Theorem>; 2],
        arm_facts: [Option<&ProofFacts>; 2],
    ) -> bool {
        if &self.state != state || &self.condition != condition || !self.has_exact_root(root_facts)
        {
            return false;
        }
        let mut required = [None, None];
        for path in &self.paths {
            let infeasible = path
                .facts
                .iter()
                .any(|fact| root_facts.directly_conflicts_with(fact.proposition()));
            if infeasible {
                continue;
            }
            let CConditionOutcome::Value(value) = path.outcome else {
                return false;
            };
            let arm_index = usize::from(!value);
            let Some(arm_facts) = arm_facts[arm_index] else {
                return false;
            };
            if arm_facts.introduced_since(root_facts).is_none()
                || path
                    .facts
                    .iter()
                    .any(|fact| !arm_facts.contains(fact.proposition()))
                || path
                    .obligations
                    .iter()
                    .any(|obligation| !arm_facts.assumptions().proves(obligation.proposition()))
            {
                return false;
            }
            let slot = &mut required[arm_index];
            if slot.replace(&path.theorem).is_some() {
                return false;
            }
        }
        required == arm_theorems
    }
}

/// One checked execution path's current semantic frontier.
#[derive(Clone, Default)]
pub(crate) struct ExecutionFrontier {
    pub(crate) position: FrontierPosition,
    pub(crate) region: ExecutionRegionKind,
    pub(crate) execution_start_state: Option<CState>,
    pub(crate) next_statement_index: usize,
    pub(crate) continuations: PersistentSequence<ProofExecutionContinuation>,
}

#[derive(Clone)]
pub(crate) struct ProofExecutionContinuation {
    pub(crate) remaining: Option<Arc<CStatement>>,
    pub(crate) next_statement_index: usize,
}

/// Surface-independent execution state owned by a checked proof branch.
///
/// Language lowering and certificate capture wrap this value with their own
/// path-local records. The kernel core contains only C state, checked facts
/// and rules, typed frontier state, and semantic freshness/region flags.
#[derive(Clone)]
pub(crate) struct ExecutionProofCore {
    pub(crate) state: SharedValue<CState>,
    pub(crate) frontier: ExecutionFrontier,
    pub(crate) effect_facts: SharedVec<ExecutionPureFact>,
    /// One append-only evidence trace per operational outcome represented by
    /// this frontier. Ordinary in-flight execution has one trace; a single C
    /// operation with several return outcomes can complete several traces at
    /// once. Forked proofs share every unchanged trace prefix.
    pub(crate) execution_evidence: SharedVec<PersistentSequence<CheckedExecutionEvent>>,
    pub(crate) function_entry: Option<Arc<CheckedFunctionEntry>>,
    pub(crate) frontier_loop_rules: PersistentSequence<CVerifiedLoopRule>,
    pub(crate) execution_abstraction: bool,
    pub(crate) loop_effect_goal: Option<LoopEffectGoal>,
    pub(crate) next_path_choice: usize,
    pub(crate) concrete_loop_execution: bool,
    pub(crate) function_entry_execution_prerequisites: PersistentOrderedSet<Proposition>,
    pub(crate) function_entry_derivations: PersistentOrderedSet<Theorem>,
    pub(crate) region_invariants_closed: bool,
    pub(crate) next_opaque_call: u64,
    pub(crate) next_kernel_variable: u64,
    pub(crate) has_empty_execution_branch_leaf: bool,
    pub(crate) has_structured_branch_history: bool,
    pub(crate) unfolded_predicates: SharedVec<String>,
}

/// One checked execution branch combines kernel semantic state with an opaque
/// language presentation record. The kernel can validate the semantic
/// frontier without depending on Surface Click data; language code can carry
/// that data without treating it as evidence.
#[derive(Clone)]
pub(crate) struct ProofExecutionState<S> {
    pub(crate) core: ExecutionProofCore,
    pub(crate) presentation: S,
}

impl<S> ProofExecutionState<S> {
    pub(crate) fn new(core: ExecutionProofCore, presentation: S) -> Self {
        Self { core, presentation }
    }
}

impl<S> Deref for ProofExecutionState<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.presentation
    }
}

impl<S> DerefMut for ProofExecutionState<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.presentation
    }
}

fn checked_evidence_conclusion(theorem: &Theorem) -> &Proposition {
    let mut conclusion = theorem.proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    conclusion
}

fn checked_evidence_premises_hold(theorem: &Theorem, facts: &ProofFacts) -> bool {
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        if !facts.assumptions().proves_exact(premise) && !facts.assumptions().proves(premise) {
            return false;
        }
        proposition = body;
    }
    true
}

fn split_checked_evidence_statement(statement: CStatement) -> (CStatement, Option<CStatement>) {
    match statement {
        CStatement::Seq(first, second) => {
            let (head, first_tail) = split_checked_evidence_statement(Arc::unwrap_or_clone(first));
            let tail = match first_tail {
                Some(first_tail) => CStatement::Seq(Arc::new(first_tail), second),
                None => Arc::unwrap_or_clone(second),
            };
            (head, Some(tail))
        }
        statement => (statement, None),
    }
}

fn prepend_checked_evidence_statement(
    statement: CStatement,
    tail: Option<CStatement>,
) -> CStatement {
    match tail {
        Some(tail) => CStatement::Seq(Arc::new(statement), Arc::new(tail)),
        None => statement,
    }
}

fn checked_statement_event(
    theorem: &Theorem,
    facts: &ProofFacts,
    state: &CState,
    statement: &CStatement,
) -> Option<CStatementOutcome> {
    if !checked_evidence_premises_hold(theorem, facts) {
        return None;
    }
    let (proved_state, proved_statement, outcome) = match checked_evidence_conclusion(theorem) {
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => (state, statement, outcome),
        _ => return None,
    };
    (proved_state == state && proved_statement == statement).then(|| outcome.clone())
}

fn checked_condition_event(
    theorem: &Theorem,
    facts: &ProofFacts,
    state: &CState,
    statement: CStatement,
    tail: Option<CStatement>,
) -> Option<Option<CStatement>> {
    if !checked_evidence_premises_hold(theorem, facts) {
        return None;
    }
    let (proved_state, proved_condition, value) = match checked_evidence_conclusion(theorem) {
        Proposition::CConditionEvaluates {
            state,
            condition,
            outcome: CConditionOutcome::Value(value),
        } => (state, condition, *value),
        _ => return None,
    };
    if proved_state != state {
        return None;
    }
    let selected = match statement {
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } if &condition == proved_condition => {
            if value {
                *then_branch
            } else {
                *else_branch
            }
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
        } if &condition == proved_condition => {
            if value {
                let loop_head = CStatement::While {
                    condition,
                    invariant,
                    invariant_checks,
                    effect_checks,
                    body: body.clone(),
                };
                prepend_checked_evidence_statement(*body, Some(loop_head))
            } else {
                CStatement::Skip
            }
        }
        _ => return None,
    };
    Some(if matches!(selected, CStatement::Skip) {
        tail
    } else {
        Some(prepend_checked_evidence_statement(selected, tail))
    })
}

struct CheckedEvidenceProgress {
    state: CState,
    remaining: Option<CStatement>,
    completed: Option<CStatementOutcome>,
}

/// Checks a retained event tree by following kernel theorem conclusions
/// through an exact source tree. This does not evaluate a C operation.
fn check_evidence_events(
    events: &[CheckedExecutionEvent],
    facts: &ProofFacts,
    mut state: CState,
    mut remaining: Option<CStatement>,
) -> Option<CheckedEvidenceProgress> {
    let mut completed = None;
    let mut current_facts = facts.clone();
    for event in events {
        if completed.is_some() {
            return None;
        }
        if let CheckedExecutionEvent::ProofCase(arm) = event {
            if !arm.is_valid() {
                return None;
            }
            current_facts = arm.facts.clone();
            continue;
        }
        let source = remaining.take()?;
        let (next_statement, tail) = split_checked_evidence_statement(source);
        match event {
            CheckedExecutionEvent::Statement(theorem) => {
                match checked_statement_event(theorem, &current_facts, &state, &next_statement)? {
                    CStatementOutcome::Normal(next_state) => {
                        state = next_state;
                        remaining = tail;
                    }
                    outcome @ (CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges) => {
                        if tail.is_some() {
                            return None;
                        }
                        completed = Some(outcome);
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => return None,
                }
            }
            CheckedExecutionEvent::Condition(theorem) => {
                remaining =
                    checked_condition_event(theorem, &current_facts, &state, next_statement, tail)?;
            }
            CheckedExecutionEvent::Branch(branch) => {
                let CStatement::If { .. } = &next_statement else {
                    return None;
                };
                if !branch.matches_source(&state, &next_statement, &tail) {
                    return None;
                }
                let full_source = prepend_checked_evidence_statement(next_statement, tail.clone());
                for arm_index in 0..2 {
                    let arm = check_evidence_events(
                        branch.arm_events(arm_index),
                        branch.arm_facts(arm_index),
                        state.clone(),
                        Some(full_source.clone()),
                    )?;
                    if arm.completed.is_some()
                        || arm.remaining != tail
                        || (branch.interface_successor_facts().is_none()
                            && arm.state != *branch.joined_state())
                    {
                        return None;
                    }
                }
                state = branch.joined_state().clone();
                remaining = tail;
                if let Some(successor_facts) = branch.interface_successor_facts() {
                    current_facts = successor_facts.clone();
                }
            }
            CheckedExecutionEvent::ProofCase(_) => unreachable!("handled before source advance"),
        }
    }
    Some(CheckedEvidenceProgress {
        state,
        remaining,
        completed,
    })
}

fn validate_checked_event_shapes(events: &[CheckedExecutionEvent]) -> Result<(), &'static str> {
    for event in events {
        let (theorem, statement) = match event {
            CheckedExecutionEvent::Statement(theorem) => (theorem, true),
            CheckedExecutionEvent::Condition(theorem) => (theorem, false),
            CheckedExecutionEvent::Branch(branch) => {
                for arm in &branch.arms {
                    validate_checked_event_shapes(&arm.events)?;
                }
                continue;
            }
            CheckedExecutionEvent::ProofCase(arm) => {
                if !arm.is_valid() {
                    return Err("retained proof-case evidence has an invalid checked arm");
                }
                continue;
            }
        };
        let right_shape = if statement {
            matches!(
                checked_evidence_conclusion(theorem),
                Proposition::CStatementExecutes { .. } | Proposition::CStatementVerifies { .. }
            )
        } else {
            matches!(
                checked_evidence_conclusion(theorem),
                Proposition::CConditionEvaluates { .. }
            )
        };
        if !right_shape {
            return Err(if statement {
                "retained statement evidence has a non-statement conclusion"
            } else {
                "retained condition evidence has a non-condition conclusion"
            });
        }
    }
    Ok(())
}

impl ExecutionProofCore {
    pub(crate) fn at_entry(state: CState, frontier: ExecutionFrontier) -> Self {
        Self {
            state: state.into(),
            frontier,
            effect_facts: Default::default(),
            execution_evidence: vec![PersistentSequence::default()].into(),
            function_entry: None,
            frontier_loop_rules: Default::default(),
            execution_abstraction: false,
            loop_effect_goal: None,
            next_path_choice: 0,
            concrete_loop_execution: false,
            function_entry_execution_prerequisites: Default::default(),
            function_entry_derivations: Default::default(),
            region_invariants_closed: false,
            next_opaque_call: 0,
            next_kernel_variable: 0,
            has_empty_execution_branch_leaf: false,
            has_structured_branch_history: false,
            unfolded_predicates: Default::default(),
        }
    }

    pub(crate) fn record_checked_function_entry(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        expected_entry_state: &CState,
    ) -> bool {
        if !self.frontier.is_at_function_entry()
            || self.execution_evidence.len() != 1
            || !self.execution_evidence[0].is_empty()
        {
            return false;
        }
        let Some(entry) =
            CheckedFunctionEntry::check(&self.state, function, arguments, expected_entry_state)
        else {
            return false;
        };
        self.function_entry = Some(entry);
        true
    }

    pub(crate) fn record_statement_transition(&mut self, theorem: Theorem) {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
        }
    }

    pub(crate) fn record_statement_outcomes(&mut self, theorems: Vec<Theorem>) {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        let prefix = self.execution_evidence.first().cloned().unwrap_or_default();
        self.execution_evidence = theorems
            .into_iter()
            .map(|theorem| {
                let mut trace = prefix.clone();
                trace.push(CheckedExecutionEvent::Statement(theorem));
                trace
            })
            .collect::<Vec<_>>()
            .into();
    }

    pub(crate) fn record_condition_transition(&mut self, theorem: Theorem) {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::Condition(theorem.clone()));
        }
    }

    pub(crate) fn record_proof_case_arm(
        &mut self,
        partition: Arc<CheckedProofCasePartition>,
        arm_index: usize,
        facts: ProofFacts,
    ) -> bool {
        let arm = CheckedProofCaseArm {
            partition,
            arm_index,
            facts,
        };
        if !arm.is_valid() {
            return false;
        }
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::ProofCase(arm.clone()));
        }
        true
    }

    /// Records a branch node only after [`CheckedExecutionBranch::check`]
    /// has validated exact source coverage, both persistent arm suffixes,
    /// the common continuation, and the joined state.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_exhaustive_branch_join(
        &mut self,
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
    ) -> Result<(), &'static str> {
        let parent_trace = match parent.execution_evidence.as_slice() {
            [trace] => trace,
            _ => return Err("the branch parent does not have one execution trace"),
        };
        let branch = CheckedExecutionBranch::check(
            split,
            root_facts,
            arm_theorems,
            arm_facts,
            parent,
            arms,
        )?;
        let mut trace = parent_trace.clone();
        trace.push(CheckedExecutionEvent::Branch(branch));
        self.execution_evidence = vec![trace].into();
        Ok(())
    }

    /// Records a two-arm `branch ensuring` only after the kernel has checked
    /// both source traces, the deterministic abstraction, every retained
    /// interface fact, and whole-context resource availability in both arms.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_interface_branch_join(
        &mut self,
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        stable_join_locals: &BTreeMap<String, CValue>,
        interface_specs: &[SpecProposition],
        joined_state: &CState,
        successor_facts: &ProofFacts,
    ) -> Result<(), &'static str> {
        let parent_trace = match parent.execution_evidence.as_slice() {
            [trace] => trace,
            _ => return Err("the interface parent does not have one execution trace"),
        };
        let branch = CheckedExecutionBranch::check_interface(
            split,
            root_facts,
            arm_theorems,
            arm_facts,
            parent,
            arms,
            stable_join_locals,
            interface_specs,
            joined_state,
            successor_facts,
        )?;
        let mut trace = parent_trace.clone();
        trace.push(CheckedExecutionEvent::Branch(branch));
        self.execution_evidence = vec![trace].into();
        Ok(())
    }

    /// Checks that every retained event carries the kernel judgment its tag
    /// promises. This is intentionally cheaper than executing any C: it only
    /// inspects the conclusions of already-issued theorem objects.
    pub(crate) fn validate_execution_evidence_shapes(&self) -> Result<(), &'static str> {
        for trace in &self.execution_evidence {
            validate_checked_event_shapes(&trace.to_vec())?;
        }
        Ok(())
    }
}

#[derive(Clone, Default)]
pub(crate) enum FrontierPosition {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: Arc<CStatement>,
    },
    FunctionExit {
        execution: CFunctionExecutionCandidates,
    },
    /// A bounded region exhausted its own statement tree without an enclosing
    /// continuation. Advancing past this typed boundary is unrepresentable.
    RegionBoundary,
}

impl ExecutionFrontier {
    pub(crate) fn is_at_function_exit(&self) -> bool {
        matches!(self.position, FrontierPosition::FunctionExit { .. })
    }

    pub(crate) fn is_at_function_entry(&self) -> bool {
        matches!(self.position, FrontierPosition::FunctionEntry)
    }

    pub(crate) fn is_at_region_boundary(&self) -> bool {
        matches!(self.position, FrontierPosition::RegionBoundary)
    }

    pub(crate) fn execution(&self) -> Option<&CFunctionExecutionCandidates> {
        match &self.position {
            FrontierPosition::FunctionEntry
            | FrontierPosition::StatementEntry { .. }
            | FrontierPosition::RegionBoundary => None,
            FrontierPosition::FunctionExit { execution } => Some(execution),
        }
    }

    pub(crate) fn execution_start_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        self.execution_start_state.as_ref().unwrap_or(current_state)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        Bitvector32Term, CComparisonOperator, CCompositeResourceDefinition, CMemory, CResourceFact,
        CType, CValue, Pointer, PointerBlock, PointerOffsetTerm, SpecExpression, c_function, int32,
    };

    fn condition_event(
        state: &CState,
        condition: &CExpression,
        value: bool,
    ) -> CheckedExecutionEvent {
        CheckedExecutionEvent::Condition(Theorem::new(Proposition::CConditionEvaluates {
            state: state.clone(),
            condition: condition.clone(),
            outcome: CConditionOutcome::Value(value),
        }))
    }

    #[test]
    fn checked_function_entry_rebase_rejects_semantic_memory_and_population_changes() {
        let function = c_function(
            CType::Void,
            "checked_entry",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![
            CCompositeResourceDefinition::counted_population(
                "item",
                Vec::new(),
                None,
                Vec::new(),
                Vec::new(),
            ),
        ]);
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let caller = CState::new()
            .with_memory(
                CMemory::new().store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1))),
            )
            .with_counted_population("item", Vec::new(), Bitvector32Term::Constant(1));
        let entry_state = crate::kernel::c_function_entry_state(&caller, &function, &[])
            .expect("the empty argument list should bind");
        let checked = CheckedFunctionEntry::check(&caller, &function, &[], &entry_state)
            .expect("the exact kernel-computed entry should check");
        let assumptions = PureFactContext::new();

        assert_eq!(
            checked.entry_state_for(&caller, &function, &[], &assumptions),
            Some(entry_state)
        );

        let changed_memory = caller.clone().with_memory(
            CMemory::new().store(pointer, CValue::Int32(Bitvector32Term::Constant(2))),
        );
        assert!(
            checked
                .entry_state_for(&changed_memory, &function, &[], &assumptions)
                .is_none(),
            "a resource rebase must not authorize a changed C memory value"
        );

        let changed_population =
            caller.with_counted_population("item", Vec::new(), Bitvector32Term::Constant(2));
        assert!(
            checked
                .entry_state_for(&changed_population, &function, &[], &assumptions)
                .is_none(),
            "a resource rebase must not authorize a changed counted population"
        );
    }

    #[test]
    fn checked_condition_evidence_preserves_the_tail_for_empty_if_arms() {
        let state = CState::new();
        let condition = CExpression::Variable("x".to_string());
        let branch = CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        let tail = CStatement::Return(CExpression::Variable("x".to_string()));
        let source = prepend_checked_evidence_statement(branch, Some(tail.clone()));

        for value in [true, false] {
            let progress = check_evidence_events(
                &[condition_event(&state, &condition, value)],
                &ProofFacts::default(),
                state.clone(),
                Some(source.clone()),
            )
            .expect("a checked empty arm should advance directly to the shared tail");
            assert_eq!(progress.state, state);
            assert_eq!(progress.remaining, Some(tail.clone()));
            assert!(progress.completed.is_none());
        }
    }

    #[test]
    fn checked_condition_evidence_rejects_a_different_source_condition() {
        let state = CState::new();
        let source_condition = CExpression::Variable("x".to_string());
        let theorem_condition = CExpression::Variable("y".to_string());
        let source = CStatement::If {
            condition: source_condition,
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        assert!(
            check_evidence_events(
                &[condition_event(&state, &theorem_condition, true)],
                &ProofFacts::default(),
                state,
                Some(source),
            )
            .is_none()
        );
    }

    #[test]
    fn checked_branch_join_accepts_empty_arms_only_at_the_artifact_tail() {
        let state = CState::new();
        let condition = CExpression::Variable("x".to_string());
        let branch_statement = CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        let continuation = Some(CStatement::Return(CExpression::Variable("x".to_string())));
        let then_theorem = match condition_event(&state, &condition, true) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let else_theorem = match condition_event(&state, &condition, false) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let root_facts = ProofFacts::default();
        let split = CheckedBranchSplit {
            state: state.clone(),
            branch_statement,
            continuation,
            condition,
            root_facts: root_facts.clone(),
            paths: vec![
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(true),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    theorem: then_theorem.clone(),
                },
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(false),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    theorem: else_theorem.clone(),
                },
            ],
        };
        let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        let mut then_arm = parent.clone();
        then_arm.record_condition_transition(then_theorem.clone());
        then_arm.frontier.region = ExecutionRegionKind::BranchArm;
        then_arm.frontier.position = FrontierPosition::RegionBoundary;
        let mut else_arm = parent.clone();
        else_arm.record_condition_transition(else_theorem.clone());
        else_arm.frontier.region = ExecutionRegionKind::BranchArm;
        else_arm.frontier.position = FrontierPosition::RegionBoundary;

        let checked = CheckedExecutionBranch::check(
            split.clone(),
            &root_facts,
            [&then_theorem, &else_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
        )
        .expect("the exact empty arms should join at the retained continuation");
        assert_eq!(checked.joined_state(), &state);
        assert_eq!(checked.arm_events(0).len(), 1);
        assert_eq!(checked.arm_events(1).len(), 1);

        assert!(
            CheckedExecutionBranch::check(
                split,
                &root_facts,
                [&else_theorem, &then_theorem],
                [&root_facts, &root_facts],
                &parent,
                [&then_arm, &else_arm],
            )
            .is_err(),
            "swapped arm evidence must not certify the source partition"
        );
    }

    #[test]
    fn checked_interface_branch_rejects_unproved_facts_and_unowned_resources() {
        let state = CState::new()
            .with_local("x", int32(7))
            .with_local("flag", int32(0));
        let condition = CExpression::Variable("flag".to_string());
        let branch_statement = CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        let continuation = Some(CStatement::Return(CExpression::Variable("x".to_string())));
        let then_theorem = match condition_event(&state, &condition, true) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let else_theorem = match condition_event(&state, &condition, false) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let root_facts = ProofFacts::default();
        let split = CheckedBranchSplit {
            state: state.clone(),
            branch_statement,
            continuation,
            condition,
            root_facts: root_facts.clone(),
            paths: vec![
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(true),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    theorem: then_theorem.clone(),
                },
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(false),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    theorem: else_theorem.clone(),
                },
            ],
        };
        let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        let mut then_arm = parent.clone();
        then_arm.record_condition_transition(then_theorem.clone());
        then_arm.frontier.region = ExecutionRegionKind::BranchArm;
        then_arm.frontier.position = FrontierPosition::RegionBoundary;
        let mut else_arm = parent.clone();
        else_arm.record_condition_transition(else_theorem.clone());
        else_arm.frontier.region = ExecutionRegionKind::BranchArm;
        else_arm.frontier.position = FrontierPosition::RegionBoundary;
        let stable_join_locals = state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        let spec = SpecProposition::Comparison {
            left: SpecExpression::CExpression(CExpression::Variable("x".to_string())),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(CExpression::Variable("x".to_string())),
        };
        let checked_fact = interface_spec_paths(&spec, &state, &state)
            .expect("the simple interface should lower")
            .remove(0)
            .proposition;
        let successor_facts = root_facts.with_fact(checked_fact);

        CheckedExecutionBranch::check_interface(
            split.clone(),
            &root_facts,
            [&then_theorem, &else_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &stable_join_locals,
            std::slice::from_ref(&spec),
            &state,
            &successor_facts,
        )
        .expect("the exact fact-only abstraction should check");

        let forged_fact = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::signed_less_than(
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        assert!(
            CheckedExecutionBranch::check_interface(
                split.clone(),
                &root_facts,
                [&then_theorem, &else_theorem],
                [&root_facts, &root_facts],
                &parent,
                [&then_arm, &else_arm],
                &stable_join_locals,
                std::slice::from_ref(&spec),
                &state,
                &successor_facts.with_fact(forged_fact),
            )
            .is_err(),
            "an unrelated successor fact must not gain interface authority"
        );

        let forged_resource = CResourceFact::own_token("missing".to_string(), Vec::new());
        let forged_state = state
            .clone()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(forged_resource));
        assert!(
            CheckedExecutionBranch::check_interface(
                split,
                &root_facts,
                [&then_theorem, &else_theorem],
                [&root_facts, &root_facts],
                &parent,
                [&then_arm, &else_arm],
                &stable_join_locals,
                std::slice::from_ref(&spec),
                &forged_state,
                &successor_facts,
            )
            .is_err(),
            "a resource absent from both arms must not gain interface authority"
        );
    }
}

/// Resolves the named function-entry state used by `old(...)`, falling back
/// to the current region's start state when the proof has no entry snapshot.
pub(crate) fn old_reference_state<'a>(
    function_entry_state: Option<&'a CState>,
    frontier: &'a ExecutionFrontier,
    current_state: &'a CState,
) -> &'a CState {
    match function_entry_state {
        Some(entry_state) => entry_state,
        None => frontier.execution_start_state(current_state),
    }
}
