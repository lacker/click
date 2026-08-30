//! Surface-independent proof obligations and checked capabilities.
//!
//! These values describe what a checked proof branch still owes. They carry
//! no Surface Click syntax, source selector, diagnostic data, or smart-plan
//! state.

use std::sync::Arc;

use super::storage::SharedValue;
use crate::kernel::{CState, CValue, ExecutionPureFact, Proposition};

/// Function-effect obligations owned alongside an execution frontier.
///
/// The selection is symbolic so grouped verification does not copy every
/// effect clause into every short-lived proof root. The checked function block
/// remains the indexed clause store.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EffectGoalSelection {
    None,
    One(usize),
    All,
}

/// One open C frontier judgment's remaining semantic obligation.
#[derive(Clone)]
pub(crate) struct FrontierObligation {
    pub(crate) selection: EffectGoalSelection,
}

impl FrontierObligation {
    pub(crate) fn new(selection: EffectGoalSelection) -> Self {
        Self { selection }
    }
}

/// The kernel meaning of one proposition branch obligation.
#[derive(Clone)]
pub(crate) struct PropositionObligation {
    proposition: Arc<Proposition>,
}

impl PropositionObligation {
    pub(crate) fn new(proposition: Proposition) -> Self {
        Self {
            proposition: Arc::new(proposition),
        }
    }

    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

/// Surface-independent result-aware state for one checked function outcome.
#[derive(Clone)]
pub(crate) struct OutcomeProofCore {
    pub(crate) result: Arc<CValue>,
    pub(crate) state: SharedValue<CState>,
    pub(crate) effect_facts: Arc<Vec<ExecutionPureFact>>,
    pub(crate) execution_pure_facts: Arc<Vec<ExecutionPureFact>>,
    pub(crate) requirement_facts: Arc<Vec<Proposition>>,
}

/// The remaining semantic obligation for one checked returning path.
#[derive(Clone)]
pub(crate) struct FunctionOutcomeObligation {
    pub(crate) path_index: usize,
    pub(crate) selection: EffectGoalSelection,
    pub(crate) checked_effects: Arc<Vec<usize>>,
}

impl FunctionOutcomeObligation {
    pub(crate) fn new(path_index: usize, selection: EffectGoalSelection) -> Self {
        Self {
            path_index,
            selection,
            checked_effects: Arc::new(Vec::new()),
        }
    }
}

/// Private authority that ordered outcome finalization may consume without
/// proving the same function effect a second time.
///
/// Only checked proof frame operations construct this value, after checking
/// every selected effect against the outcome or outcomes they own.
#[derive(Clone)]
pub(crate) struct CheckedFrameAuthority {
    effect_indices: Arc<Vec<usize>>,
}

impl CheckedFrameAuthority {
    pub(crate) fn new(effect_indices: Vec<usize>) -> Self {
        Self {
            effect_indices: Arc::new(effect_indices),
        }
    }

    pub(crate) fn contains(&self, effect_index: usize) -> bool {
        self.effect_indices.binary_search(&effect_index).is_ok()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.effect_indices.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.effect_indices.len()
    }

    pub(crate) fn matches(&self, effect_indices: &[usize]) -> bool {
        self.effect_indices.as_slice() == effect_indices
    }
}
