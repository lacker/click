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
//! it produces is a function of the argument values alone. The registry does
//! not take that on trust: [`register_pure_function_definition`] refuses a
//! body that loads memory or reads a C name that is not one of its
//! parameters, whenever the body is built from forms the check inspects.

use std::collections::{BTreeMap, BTreeSet};

use super::primitives::{
    AlgebraicTerm, AlgebraicType, CExpression, CState, CType, CValue, ExecutionBudget,
    PureFactContext, PureFunctionArgument, SpecAlgebraicExpression, SpecAlgebraicExpressionNode,
    SpecExpression, SpecIntegerExpression, SpecProposition,
};
use super::spec::walk::{SpecNode, Visit, WalkBudget, Walked, walk_spec};

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

    /// Why this body is not a function of its parameters alone, when the
    /// closedness check can decide that.
    ///
    /// The body was lowered with its parameters left as names, so a C name
    /// it reads that is not a parameter, a `let`, a fold binder or a match
    /// binding is something outside the function: a file-scope object the
    /// Surface left as a bare name, or a local of whatever contract applies
    /// the function. A memory load is outside it the same way. Either would
    /// make one application term stand for different values, which is what
    /// the memory-independent classification promises cannot happen.
    fn openness(&self) -> Option<String> {
        let mut bound = self
            .parameters
            .iter()
            .map(|parameter| match parameter {
                CPureFunctionParameter::C { name, .. }
                | CPureFunctionParameter::Algebraic { name, .. } => name.clone(),
            })
            .collect::<Vec<_>>();
        let mut reads = BodyReads::default();
        if collect_body_reads(SpecNode::Expression(&self.body), &mut bound, &mut reads).is_err() {
            // A form the check does not inspect: the classification stands
            // on its own, as it did before the check existed.
            return None;
        }
        if reads.memory {
            return Some("loads memory".to_string());
        }
        reads
            .free_c_names
            .into_iter()
            .next()
            .map(|name| format!("reads the C name `{name}`, which is not a parameter"))
    }
}

/// What a declared body reads besides the names bound around the read.
#[derive(Default)]
struct BodyReads {
    free_c_names: BTreeSet<String>,
    memory: bool,
}

/// A body form the closedness check does not inspect.
struct UninspectedForm(#[allow(dead_code)] &'static str);

fn note_c_name(name: &str, bound: &[String], reads: &mut BodyReads) {
    if !bound.iter().any(|bound| bound == name) {
        reads.free_c_names.insert(name.to_string());
    }
}

fn with_bound<T>(
    bound: &mut Vec<String>,
    names: impl IntoIterator<Item = String>,
    visit: impl FnOnce(&mut Vec<String>) -> T,
) -> T {
    let depth = bound.len();
    bound.extend(names);
    let result = visit(bound);
    bound.truncate(depth);
    result
}

/// Collects what a body subtree reads besides the names in `bound`, or names
/// the first form the check does not inspect. A binder's names are bound only
/// around the subtrees it scopes: a match arm's body, and a fold's or `let`'s
/// body.
fn collect_body_reads(
    root: SpecNode<'_>,
    bound: &mut Vec<String>,
    reads: &mut BodyReads,
) -> Result<(), UninspectedForm> {
    fn scoped(
        names: &[String],
        body: SpecNode<'_>,
        bound: &mut Vec<String>,
        reads: &mut BodyReads,
    ) -> Result<(), UninspectedForm> {
        with_bound(bound, names.iter().cloned(), |bound| {
            collect_body_reads(body, bound, reads)
        })
    }
    let walked = walk_spec(root, WalkBudget::Unmetered, |node| {
        use SpecNode as N;
        let binder = match node {
            N::Expression(SpecExpression::AlgebraicMatch { scrutinee, arms }) => {
                collect_body_reads(N::Algebraic(scrutinee), bound, reads).and_then(|()| {
                    arms.iter().try_for_each(|arm| {
                        scoped(&arm.bindings, N::Expression(&arm.body), bound, reads)
                    })
                })
            }
            N::Integer(SpecIntegerExpression::AlgebraicMatch { scrutinee, arms }) => {
                collect_body_reads(N::Algebraic(scrutinee), bound, reads).and_then(|()| {
                    arms.iter().try_for_each(|arm| {
                        scoped(&arm.bindings, N::Integer(&arm.body), bound, reads)
                    })
                })
            }
            N::Algebraic(SpecAlgebraicExpression {
                node: SpecAlgebraicExpressionNode::Match { scrutinee, arms },
                ..
            }) => collect_body_reads(N::Algebraic(scrutinee), bound, reads).and_then(|()| {
                arms.iter().try_for_each(|arm| {
                    scoped(&arm.bindings, N::Algebraic(&arm.body), bound, reads)
                })
            }),
            N::Expression(SpecExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            }) => [start, end, initial]
                .into_iter()
                .try_for_each(|value| collect_body_reads(N::Expression(value), bound, reads))
                .and_then(|()| {
                    scoped(
                        &[accumulator.clone(), item.clone()],
                        N::Expression(body),
                        bound,
                        reads,
                    )
                }),
            N::Expression(SpecExpression::Let { name, value, body }) => {
                collect_body_reads(N::Expression(value), bound, reads).and_then(|()| {
                    scoped(
                        std::slice::from_ref(name),
                        N::Expression(body),
                        bound,
                        reads,
                    )
                })
            }
            N::Expression(SpecExpression::CExpression(expression)) => {
                collect_c_expression_reads(expression, bound, reads);
                return Visit::Descend;
            }
            N::Expression(SpecExpression::MemoryLoad { .. }) => {
                reads.memory = true;
                return Visit::Descend;
            }
            N::Expression(SpecExpression::AggregateFieldValue { parameter, .. }) => {
                note_c_name(parameter, bound, reads);
                return Visit::Descend;
            }
            N::Expression(SpecExpression::CountedResourceCount { .. }) => {
                Err(UninspectedForm("a counted-resource count"))
            }
            N::Expression(SpecExpression::LoopEntrySnapshot(_)) => {
                Err(UninspectedForm("a loop-entry snapshot"))
            }
            // Quantifiers, sequences, resources and loadability do not occur
            // in a memory-independent body; a body that has one is not
            // inspected.
            N::Proposition(
                SpecProposition::ForAllMachineInteger { .. }
                | SpecProposition::ForAllInt32 { .. }
                | SpecProposition::ForAllInteger { .. }
                | SpecProposition::ForAllAlgebraic { .. }
                | SpecProposition::ForAllPointer { .. }
                | SpecProposition::ExistsMachineInteger { .. }
                | SpecProposition::ExistsInt32 { .. }
                | SpecProposition::ExistsInteger { .. }
                | SpecProposition::ExistsAlgebraic { .. }
                | SpecProposition::ExistsPointer { .. }
                | SpecProposition::SequenceMembership { .. }
                | SpecProposition::SequenceComparison { .. }
                | SpecProposition::ResourceSeparate { .. }
                | SpecProposition::ResourceContains { .. }
                | SpecProposition::MemoryLoadable { .. },
            ) => Err(UninspectedForm(
                "a proposition form the closedness check does not inspect",
            )),
            // A resource field reads the binder's instance, and an algebraic
            // binding is a parameter or a match binding of the algebraic sort,
            // never a C name. An array reference carries its own snapshot as
            // an argument; only the pointer expression is a read of this
            // body's scope.
            _ => return Visit::Descend,
        };
        match binder {
            Ok(()) => Visit::Skip,
            Err(form) => Visit::Stop(form),
        }
    });
    match walked {
        Walked::Stopped(form) => Err(form),
        Walked::Completed | Walked::OutOfTime => Ok(()),
    }
}

fn collect_c_expression_reads(expression: &CExpression, bound: &[String], reads: &mut BodyReads) {
    use CExpression::*;
    match expression {
        Variable(name) => note_c_name(name, bound, reads),
        Value(_) | FunctionAddress(_) => {}
        Load(expression) => {
            reads.memory = true;
            collect_c_expression_reads(expression, bound, reads);
        }
        TypedLoad { pointer, .. } => {
            reads.memory = true;
            collect_c_expression_reads(pointer, bound, reads);
        }
        Cast { expression, .. }
        | FloatNegate(expression)
        | FloatClassification { expression, .. }
        | AddressOf(expression)
        | CheckedObjectAddress(expression)
        | MemberAddress {
            object: expression, ..
        }
        | PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | PointerAligned {
            pointer: expression,
            ..
        }
        | Not(expression)
        | BitwiseNot(expression) => collect_c_expression_reads(expression, bound, reads),
        Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_reads(condition, bound, reads);
            collect_c_expression_reads(then_branch, bound, reads);
            collect_c_expression_reads(else_branch, bound, reads);
        }
        ArrayRowAddress {
            array: left,
            index: right,
            ..
        }
        | RecordPointerOffset {
            pointer: left,
            index: right,
            ..
        }
        | LessThan(left, right)
        | LessEqual(left, right)
        | GreaterThan(left, right)
        | GreaterEqual(left, right)
        | Equal(left, right)
        | NotEqual(left, right)
        | And(left, right)
        | Or(left, right)
        | Add(left, right)
        | Subtract(left, right)
        | Multiply(left, right)
        | Divide(left, right)
        | Remainder(left, right)
        | ShiftLeft(left, right)
        | ShiftRight(left, right)
        | BitwiseAnd(left, right)
        | BitwiseOr(left, right)
        | BitwiseXor(left, right)
        | Index(left, right) => {
            collect_c_expression_reads(left, bound, reads);
            collect_c_expression_reads(right, bound, reads);
        }
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
///
/// A recorded body must be a function of its parameters alone, because the
/// application of a memory-independent function is keyed on its argument
/// values and nothing else. A body that loads memory, or reads a C name that
/// is not one of its parameters, is refused with a reason that completes the
/// sentence "pure function `f` ...". The check inspects the forms a
/// memory-independent body is built from and records a body it cannot
/// inspect as before; it is a defence behind the Surface classification, not
/// a replacement for it.
pub fn register_pure_function_definition(
    definition: CPureFunctionDefinition,
) -> Result<(), String> {
    if let Some(openness) = definition.openness() {
        return Err(openness);
    }
    PURE_FUNCTION_DEFINITIONS.with(|registry| {
        registry
            .borrow_mut()
            .entry(definition.name.clone())
            .or_insert_with(|| std::sync::Arc::new(definition));
    });
    Ok(())
}

pub(crate) fn registered_pure_function_definition(
    name: &str,
) -> Option<std::sync::Arc<CPureFunctionDefinition>> {
    PURE_FUNCTION_DEFINITIONS.with(|registry| registry.borrow().get(name).cloned())
}

/// The registered pure-function definitions, for a reusable session to
/// capture and restore.
pub(crate) fn capture_pure_function_definitions()
-> BTreeMap<String, std::sync::Arc<CPureFunctionDefinition>> {
    PURE_FUNCTION_DEFINITIONS.with(|definitions| definitions.borrow().clone())
}

pub(crate) fn restore_pure_function_definitions(
    state: &BTreeMap<String, std::sync::Arc<CPureFunctionDefinition>>,
) {
    PURE_FUNCTION_DEFINITIONS.with(|definitions| *definitions.borrow_mut() = state.clone());
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

#[cfg(test)]
mod spec_walk_oracle_tests;
