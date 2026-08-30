//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

use super::{PersistentOrderedSet, PersistentSequence, SharedValue, SharedVec};
use crate::kernel::{
    CFunctionExecutionCandidates, CLoopEffectCheck, CState, CStatement, CVerifiedLoopRule,
    ExecutionPureFact, Proposition, Theorem,
};
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
    pub(crate) frontier_loop_rules: PersistentSequence<CVerifiedLoopRule>,
    pub(crate) execution_abstraction: bool,
    pub(crate) loop_effect_goal: Option<LoopEffectGoal>,
    pub(crate) next_path_choice: usize,
    pub(crate) concrete_loop_execution: bool,
    pub(crate) function_entry_execution_prerequisites: PersistentOrderedSet<Proposition>,
    pub(crate) function_entry_derivations: PersistentOrderedSet<Theorem>,
    pub(crate) region_simp: Option<(usize, usize)>,
    pub(crate) region_invariants_closed: bool,
    pub(crate) next_opaque_call: u64,
    pub(crate) next_kernel_variable: u64,
    pub(crate) has_empty_execution_branch_leaf: bool,
    pub(crate) has_structured_branch_history: bool,
    pub(crate) unfolded_predicates: SharedVec<String>,
}

impl ExecutionProofCore {
    pub(crate) fn at_entry(state: CState, frontier: ExecutionFrontier) -> Self {
        Self {
            state: state.into(),
            frontier,
            effect_facts: Default::default(),
            frontier_loop_rules: Default::default(),
            execution_abstraction: false,
            loop_effect_goal: None,
            next_path_choice: 0,
            concrete_loop_execution: false,
            function_entry_execution_prerequisites: Default::default(),
            function_entry_derivations: Default::default(),
            region_simp: None,
            region_invariants_closed: false,
            next_opaque_call: 0,
            next_kernel_variable: 0,
            has_empty_execution_branch_leaf: false,
            has_structured_branch_history: false,
            unfolded_predicates: Default::default(),
        }
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
