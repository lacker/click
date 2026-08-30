//! Language environments borrowed while checking a proof.
//!
//! These values provide Surface Click lowering, diagnostics, and project
//! lookup. They are intentionally separate from the persistent checked state
//! owned by the proof object.

use super::pure_theorems::PureTheoremContext;
use super::*;
use std::sync::Arc;

pub(in crate::surface::proof) enum ProofContext<'a> {
    Pure(PureProofContext<'a>),
    FixedState(FixedStateProofContext<'a>),
    Execution(ExecutionProofContext<'a>),
}

pub(in crate::surface::proof) struct PureProofContext<'a> {
    pub(in crate::surface::proof) claim_label: &'a str,
    pub(in crate::surface::proof) theorem_context: &'a PureTheoremContext,
    pub(in crate::surface::proof) predicate_environment: &'a PredicateEnvironment,
    pub(in crate::surface::proof) click_function_environment: &'a ClickFunctionEnvironment,
    pub(in crate::surface::proof) theorem_environment: &'a TheoremEnvironment,
}

pub(in crate::surface::proof) struct FixedStateProofContext<'a> {
    pub(in crate::surface::proof) claim_label: &'a str,
    pub(in crate::surface::proof) tactic_index: usize,
    pub(in crate::surface::proof) parameters: &'a [syntax::C0Parameter],
    pub(in crate::surface::proof) arguments: &'a [CExpression],
    pub(in crate::surface::proof) pre_state: &'a CState,
    pub(in crate::surface::proof) state: &'a CState,
    pub(in crate::surface::proof) result: Option<&'a CValue>,
    pub(in crate::surface::proof) premise_anchor: Option<ProgramPointRef>,
    pub(in crate::surface::proof) recorded_snapshots: &'a RecordedSnapshots,
    pub(in crate::surface::proof) surface_propositions: &'a SurfacePropositionMap,
    pub(in crate::surface::proof) predicate_environment: &'a PredicateEnvironment,
    pub(in crate::surface::proof) click_function_environment: &'a ClickFunctionEnvironment,
    pub(in crate::surface::proof) theorem_environment: &'a TheoremEnvironment,
    pub(in crate::surface::proof) unfolded_predicates: &'a [String],
    pub(in crate::surface::proof) effect_facts: &'a [ExecutionPureFact],
    pub(in crate::surface::proof) lowering_context: Arc<Vec<Proposition>>,
    pub(in crate::surface::proof) original_requirements: &'a [Requirement],
    pub(in crate::surface::proof) requirement_label_indices: Option<&'a BTreeMap<String, usize>>,
    pub(in crate::surface::proof) requirement_facts: &'a [Proposition],
}

/// The per-proof constants of an execution proof: which claim is being
/// proved, the source layout it executes, and the entry facts and state
/// that `old(...)` and requirement premises resolve against.
#[derive(Clone, Default)]
pub(in crate::surface::proof) struct ExecutionProofConstants {
    pub(in crate::surface::proof) proof_site: Option<ProofSite>,
    pub(in crate::surface::proof) source_layout: SourceExecutionLayout,
    pub(in crate::surface::proof) execution_start_facts: Arc<Vec<Proposition>>,
    pub(in crate::surface::proof) function_entry_state: Option<CState>,
    pub(in crate::surface::proof) grouped_contract: bool,
}

pub(in crate::surface::proof) struct ExecutionProofContext<'a> {
    pub(in crate::surface::proof) claim_label: &'a str,
    pub(in crate::surface::proof) tactic_index: usize,
    pub(in crate::surface::proof) function_block: &'a FunctionBlock,
    pub(in crate::surface::proof) function: &'a CFunction,
    pub(in crate::surface::proof) parsed_function: &'a syntax::C0Function,
    pub(in crate::surface::proof) arguments: &'a [CExpression],
    pub(in crate::surface::proof) function_environment: &'a CExecutionEnvironment,
    pub(in crate::surface::proof) resource_environment: &'a ResourceEnvironment,
    pub(in crate::surface::proof) predicate_environment: &'a PredicateEnvironment,
    pub(in crate::surface::proof) click_function_environment: &'a ClickFunctionEnvironment,
    pub(in crate::surface::proof) theorem_environment: &'a TheoremEnvironment,
    /// Shared by every context derived from this proof (tactic-index
    /// re-attribution, loop-bound executions), so deriving one is cheap.
    pub(in crate::surface::proof) constants: Arc<ExecutionProofConstants>,
}

impl<'a> ExecutionProofContext<'a> {
    /// The state that `old(...)` and `at(function.entry, ...)` resolve to when
    /// a contract clause is lowered at `frontier`.
    pub(in crate::surface::proof) fn old_reference_state<'s>(
        &'s self,
        frontier: &'s ExecutionFrontier,
        current_state: &'s CState,
    ) -> &'s CState {
        old_reference_state(
            self.constants.function_entry_state.as_ref(),
            frontier,
            current_state,
        )
    }

    /// The same proof, attributing subsequent diagnostics to `tactic_index`.
    pub(in crate::surface::proof) fn with_tactic_index(&self, tactic_index: usize) -> Self {
        Self {
            tactic_index,
            constants: self.constants.clone(),
            ..*self
        }
    }

    /// The same proof executing a function whose frontier loop clauses are
    /// bound: a `loop` tactic runs its one step against the bound block,
    /// the annotated function, and an environment carrying the verified
    /// loop rules, then returns to the enclosing context.
    pub(in crate::surface::proof) fn with_loop_binding<'l>(
        &'l self,
        function_block: &'l FunctionBlock,
        function: &'l CFunction,
        function_environment: &'l CExecutionEnvironment,
    ) -> ExecutionProofContext<'l> {
        ExecutionProofContext {
            function_block,
            function,
            function_environment,
            constants: self.constants.clone(),
            ..*self
        }
    }
}

impl ProofContext<'_> {
    pub(in crate::surface::proof) fn claim_label(&self) -> &str {
        match self {
            Self::Pure(context) => context.claim_label,
            Self::FixedState(context) => context.claim_label,
            Self::Execution(context) => context.claim_label,
        }
    }
}
