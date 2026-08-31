//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

use super::{PersistentOrderedSet, PersistentSequence, ProofFacts, SharedValue, SharedVec};
use crate::kernel::{
    CConditionOutcome, CExpression, CFunctionExecutionCandidates, CLoopEffectCheck, CState,
    CStatement, CVerifiedLoopRule, ExecutionLimit, ExecutionPureFact, Proposition, Theorem,
};
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
        condition: CExpression,
        root_facts: &ProofFacts,
    ) -> Result<Self, CheckedBranchSplitError> {
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

impl ExecutionProofCore {
    pub(crate) fn at_entry(state: CState, frontier: ExecutionFrontier) -> Self {
        Self {
            state: state.into(),
            frontier,
            effect_facts: Default::default(),
            execution_evidence: vec![PersistentSequence::default()].into(),
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

    /// Checks that every retained event carries the kernel judgment its tag
    /// promises. This is intentionally cheaper than executing any C: it only
    /// inspects the conclusions of already-issued theorem objects.
    pub(crate) fn validate_execution_evidence_shapes(&self) -> Result<(), &'static str> {
        for trace in &self.execution_evidence {
            for event in trace.iter() {
                let (theorem, statement) = match event {
                    CheckedExecutionEvent::Statement(theorem) => (theorem, true),
                    CheckedExecutionEvent::Condition(theorem) => (theorem, false),
                };
                let mut conclusion = theorem.proposition();
                while let Proposition::Implies(_, body) = conclusion {
                    conclusion = body;
                }
                let right_shape = if statement {
                    matches!(
                        conclusion,
                        Proposition::CStatementExecutes { .. }
                            | Proposition::CStatementVerifies { .. }
                    )
                } else {
                    matches!(conclusion, Proposition::CConditionEvaluates { .. })
                };
                if !right_shape {
                    return Err(if statement {
                        "retained statement evidence has a non-statement conclusion"
                    } else {
                        "retained condition evidence has a non-condition conclusion"
                    });
                }
            }
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
