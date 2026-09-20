//! What a fresh model-field variable stands for.
//!
//! A resource instance that survives a call keeps its identity and gets fresh
//! field variables, so a contract that promises nothing about a field leaves
//! the reader holding `v1000002`. There is nothing in the term to recover: the
//! field value is stored *inside* the instance fact, and a projection is
//! resolved at lowering to whatever instance carries that identity then.
//!
//! So the mint records it. Every fresh field variable is registered where it is
//! minted — with the instance it belongs to, the field of the schema it is, and
//! **why** it was minted, which the mint site is the only place that knows. A
//! refusal then spells the variable `c.rank` and says which step replaced it,
//! instead of printing a kernel name.
//!
//! This is the model-field counterpart of the load-variable registry
//! (`crate::kernel::eval::memory_loads`), and it is kept the same way: one map
//! insert per fresh field variable at the site that already mints it, bounded,
//! and emptied when a `VerificationSession` starts, because a field variable's
//! meaning belongs to the verification that issued it.
//!
//! Nothing reads this on a successful path. It is diagnostics only: no rule, no
//! premise and no name a term carries depends on it.

use crate::kernel::primitives::{
    AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, Bitvector32Term, IntegerTerm, Variable,
};
use std::sync::Arc;

/// The variable a freshly minted field value is, for all three field kinds. A
/// value that is not a bare variable was not minted as an arbitrary model and
/// is not registered.
pub(crate) fn algebraic_value_variable(value: &AlgebraicValue) -> Option<Variable> {
    match value {
        AlgebraicValue::Integer(IntegerTerm::Variable(variable)) => Some(*variable),
        AlgebraicValue::Algebraic(AlgebraicTerm {
            node: AlgebraicTermNode::Variable(variable),
            ..
        }) => Some(*variable),
        AlgebraicValue::C(value) => match crate::kernel::spec::c_value_bitvector_term(value) {
            Some(Bitvector32Term::Variable(variable)) => Some(variable),
            _ => None,
        },
        _ => None,
    }
}

/// The bound on each table, in the style of the other per-session memos: a
/// verification that somehow mints more field variables than this loses the
/// spellings rather than growing without limit.
const MAX_REGISTERED: usize = 100_000;

/// Which step replaced an instance's model, recorded at the mint.
///
/// This is not a guess reconstructed from a refusal site: the recorded memory
/// history says nothing about model fields (`resource_tracker::Change::Unrecorded`),
/// and the only place that knows why a field vector is fresh is the place that
/// made it fresh.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModelMint {
    /// A call returned ownership of the instance. Its identity survived and its
    /// field values did not, so only the callee's own `ensures` relate the two.
    CallReturn { callee: Arc<str> },
    /// A contract's `produces` created the instance at the call.
    Produced { callee: Arc<str> },
    /// A loop head havocked the model of a binder the loop declares, so the
    /// body starts from an arbitrary model of it.
    LoopHead,
    /// Contract/implementation refinement drew one arbitrary model for both
    /// sides of the comparison.
    Refinement,
    /// The contract's own entry model, which `old(..)` names. This one is
    /// minted on the surface side, where the binder is elaborated.
    ContractEntry,
}

/// One fresh model-field variable: which instance's field it is, and why it
/// exists.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModelFieldOrigin {
    /// The instance the field belongs to, by the identity the state indexes.
    pub(crate) identity: Variable,
    /// The field's declared name, for spelling `c.rank`.
    pub(crate) field: Arc<str>,
    pub(crate) field_index: usize,
    pub(crate) minted_by: ModelMint,
}

thread_local! {
    static MODEL_FIELD_VARIABLES: std::cell::RefCell<
        std::collections::HashMap<Variable, ModelFieldOrigin>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static INSTANCE_SPELLINGS: std::cell::RefCell<
        std::collections::HashMap<Variable, Arc<str>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Records one fresh field variable. One insert, at the site that already
/// allocated the variable, so the cost is one entry per field of the instance
/// whose model was just replaced.
pub(crate) fn register_model_field_variable(variable: Variable, origin: ModelFieldOrigin) {
    MODEL_FIELD_VARIABLES.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.len() >= MAX_REGISTERED {
            registry.clear();
        }
        registry.insert(variable, origin);
    });
}

/// What a model-field variable stands for, if this session minted it.
pub(crate) fn registered_model_field_origin(variable: Variable) -> Option<ModelFieldOrigin> {
    MODEL_FIELD_VARIABLES.with(|registry| registry.borrow().get(&variable).cloned())
}

/// Records the name a reader wrote for one resource instance — the contract's
/// binder, `c`. The surface supplies it where it resolves a field access,
/// because an instance identity is a kernel variable and only the surface knows
/// what it was called.
pub(crate) fn register_instance_spelling(identity: Variable, spelling: &str) {
    INSTANCE_SPELLINGS.with(|registry| {
        let mut registry = registry.borrow_mut();
        if registry.len() >= MAX_REGISTERED {
            registry.clear();
        }
        if !registry.contains_key(&identity) {
            registry.insert(identity, Arc::from(spelling));
        }
    });
}

pub(crate) fn registered_instance_spelling(identity: Variable) -> Option<Arc<str>> {
    INSTANCE_SPELLINGS.with(|registry| registry.borrow().get(&identity).cloned())
}

/// The reader's own spelling of a model-field variable: `c.rank`, or
/// `old(c.rank)` when the variable is the contract's entry model, which is the
/// version `old(..)` names in source.
///
/// `None` unless both halves are known: a half-spelled name would be worse
/// than the kernel variable it replaced, because it would look like source the
/// reader could search for.
pub(crate) fn model_field_spelling(variable: Variable) -> Option<String> {
    let origin = registered_model_field_origin(variable)?;
    let owner = registered_instance_spelling(origin.identity)?;
    let field = format!("{owner}.{}", origin.field);
    Some(match origin.minted_by {
        ModelMint::ContractEntry => format!("old({field})"),
        _ => field,
    })
}

pub(crate) fn clear_model_field_registry() {
    MODEL_FIELD_VARIABLES.with(|registry| registry.borrow_mut().clear());
    INSTANCE_SPELLINGS.with(|registry| registry.borrow_mut().clear());
}
