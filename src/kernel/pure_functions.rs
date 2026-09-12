//! One-step definitions of the Click source's memory-independent pure
//! functions, in the kernel's own specification vocabulary.
//!
//! The kernel keeps a pure function application opaque: only an explicit
//! `unfold` step introduces its defining equation, and that step is checked
//! at the Surface. Arm refutation (D7 in reverse) needs less than that and
//! cannot ask for it, because it runs inside contract lowering, a loop head,
//! a back edge and a guard prefix, where there is no proof script to place an
//! `unfold` in. What it needs is the value of one predicate at one
//! constructor, which is one substitution and one evaluation of an expression
//! this registry already holds.
//!
//! The registry therefore holds program data, not derived facts: each entry
//! is one declared function body, lowered once per verification by the same
//! lowering that lowers every other annotation, with the parameters left as
//! names the evaluation binds. It is scoped to one
//! [`crate::kernel::VerificationSession`] exactly as the block alignment
//! registry is, and it is consulted only through
//! [`evaluate_registered_pure_function`], which refuses anything it cannot
//! evaluate to one unconditional value.
//!
//! Only memory-independent functions are registered (the classification
//! package A20 added), so an evaluation here reads no snapshot and the value
//! it produces is a function of the argument values alone.

use std::collections::BTreeMap;

use super::primitives::{
    AlgebraicTerm, AlgebraicType, CState, CType, CValue, ExecutionBudget, PureFactContext,
    PureFunctionArgument, SpecExpression,
};

/// One parameter of a registered pure function: the name its body refers to
/// and the sort the evaluation binds it in.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CPureFunctionParameter {
    C {
        name: String,
        c_type: CType,
    },
    Algebraic {
        name: String,
        algebraic_type: AlgebraicType,
    },
}

impl CPureFunctionParameter {
    pub fn c(name: impl Into<String>, c_type: CType) -> Self {
        Self::C {
            name: name.into(),
            c_type,
        }
    }

    pub fn algebraic(name: impl Into<String>, algebraic_type: AlgebraicType) -> Self {
        Self::Algebraic {
            name: name.into(),
            algebraic_type,
        }
    }
}

/// One declared pure function's defining body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CPureFunctionDefinition {
    name: String,
    parameters: Vec<CPureFunctionParameter>,
    body: SpecExpression,
}

impl CPureFunctionDefinition {
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<CPureFunctionParameter>,
        body: SpecExpression,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            body,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

thread_local! {
    /// The declared body of each memory-independent pure function, recorded
    /// once per verification from the Click source.
    static PURE_FUNCTION_DEFINITIONS: std::cell::RefCell<
        BTreeMap<String, std::sync::Arc<CPureFunctionDefinition>>,
    > = const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// Records one declared function body for this verification. A name recorded
/// twice keeps the first body: two declarations of one name are a Surface
/// error, and the kernel never resolves that by preferring the later one.
pub fn register_pure_function_definition(definition: CPureFunctionDefinition) {
    PURE_FUNCTION_DEFINITIONS.with(|registry| {
        registry
            .borrow_mut()
            .entry(definition.name.clone())
            .or_insert_with(|| std::sync::Arc::new(definition));
    });
}

pub(crate) fn registered_pure_function_definition(
    name: &str,
) -> Option<std::sync::Arc<CPureFunctionDefinition>> {
    PURE_FUNCTION_DEFINITIONS.with(|registry| registry.borrow().get(name).cloned())
}

pub(crate) fn clear_pure_function_definitions() {
    PURE_FUNCTION_DEFINITIONS.with(|registry| registry.borrow_mut().clear());
}

/// The value of one registered pure function at explicit arguments, or `None`
/// when this registry cannot decide it.
///
/// The evaluation binds each parameter to its argument and evaluates the
/// declared body once. It answers only when the body has a single evaluation
/// path that owes nothing: a body needing a side condition, a memory read, or
/// a case split is not a value this rule may use. Cost is one traversal of
/// the declared body.
pub(crate) fn evaluate_registered_pure_function(
    name: &str,
    arguments: &[PureFunctionArgument],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<CValue> {
    let definition = registered_pure_function_definition(name)?;
    if definition.parameters.len() != arguments.len() {
        return None;
    }
    let mut state = CState::new();
    let mut bindings = BTreeMap::new();
    for (parameter, argument) in definition.parameters.iter().zip(arguments) {
        crate::instrumentation::record_deterministic_work(1);
        match (parameter, argument) {
            // A pointer argument of a memory-independent function travels as
            // an array reference anchored to one canonical snapshot (package
            // A20). The snapshot is dead weight here for the same reason it
            // is there: what the body reads is the pointer value.
            (
                CPureFunctionParameter::C { name, c_type },
                PureFunctionArgument::Value(value)
                | PureFunctionArgument::ArrayRef { pointer: value, .. },
            ) => {
                if value.c_type() != *c_type {
                    return None;
                }
                state.locals.set_typed(name.clone(), value.clone(), *c_type);
            }
            (
                CPureFunctionParameter::Algebraic {
                    name,
                    algebraic_type,
                },
                PureFunctionArgument::Algebraic(value),
            ) => {
                if value.algebraic_type != *algebraic_type || !value.is_well_formed() {
                    return None;
                }
                bindings.insert(name.clone(), value.clone());
            }
            _ => return None,
        }
    }
    let paths = super::spec::evaluate_spec_expression_paths_with_bindings(
        &state,
        &definition.body,
        assumptions,
        &bindings,
        budget,
    )
    .ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    (path.facts.is_empty() && path.obligations.is_empty()).then(|| path.value.clone())
}

/// Substitutes one algebraic argument of an application, leaving the rest as
/// they were. Used to ask what a predicate known about a symbolic model would
/// say about one constructor of that model's type.
pub(crate) fn arguments_with_algebraic_substitution(
    arguments: &[PureFunctionArgument],
    position: usize,
    value: AlgebraicTerm,
) -> Option<Vec<PureFunctionArgument>> {
    let mut arguments = arguments.to_vec();
    let slot = arguments.get_mut(position)?;
    if !matches!(slot, PureFunctionArgument::Algebraic(_)) {
        return None;
    }
    *slot = PureFunctionArgument::Algebraic(value);
    Some(arguments)
}
