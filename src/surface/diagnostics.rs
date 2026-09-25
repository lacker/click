use super::*;
use crate::kernel::SharedCMemory;
use crate::kernel::resource_tracker;
use crate::kernel::{CComparisonOperator, CFloatBinaryOperator, CFloatCondition, CUpdateOperator};
use crate::surface::validation::describe_click_type;
use std::fmt::Write;

const MAX_DIAGNOSTIC_ITEMS: usize = 12;
const DEBUG_VALUE_BYTE_LIMIT: usize = 2 * 1024;
const TRUNCATION_SUFFIX: &str =
    "\n… <diagnostic truncated; set CLICK_FULL_DIAGNOSTICS=1 for full internal state>";

pub(super) fn bound_error_message(message: String) -> String {
    bound_error_message_for_mode(message, std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some())
}

pub(super) fn bound_error_message_for_mode(message: String, full_internal_state: bool) -> String {
    if full_internal_state || message.len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT {
        return message;
    }
    truncate_utf8_with_suffix(&message, DEFAULT_DIAGNOSTIC_BYTE_LIMIT, TRUNCATION_SUFFIX)
}

fn truncate_utf8_with_suffix(message: &str, limit: usize, suffix: &str) -> String {
    if message.len() <= limit {
        return message.to_string();
    }
    let content_limit = limit.saturating_sub(suffix.len());
    let mut boundary = content_limit.min(message.len());
    while !message.is_char_boundary(boundary) {
        boundary -= 1;
    }
    let mut bounded = String::with_capacity(boundary + suffix.len());
    bounded.push_str(&message[..boundary]);
    bounded.push_str(suffix);
    bounded
}

struct BoundedDebugWriter {
    output: String,
    content_limit: usize,
}

impl Write for BoundedDebugWriter {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let remaining = self.content_limit.saturating_sub(self.output.len());
        if value.len() <= remaining {
            self.output.push_str(value);
            return Ok(());
        }
        let mut boundary = remaining.min(value.len());
        while !value.is_char_boundary(boundary) {
            boundary -= 1;
        }
        self.output.push_str(&value[..boundary]);
        Err(fmt::Error)
    }
}

pub(super) fn bounded_debug(value: &impl fmt::Debug) -> String {
    bounded_debug_for_mode(value, std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some())
}

pub(super) fn bounded_debug_for_mode(value: &impl fmt::Debug, full_internal_state: bool) -> String {
    if full_internal_state {
        return format!("{value:?}");
    }
    let content_limit = DEBUG_VALUE_BYTE_LIMIT.saturating_sub(TRUNCATION_SUFFIX.len());
    let mut writer = BoundedDebugWriter {
        output: String::with_capacity(DEBUG_VALUE_BYTE_LIMIT),
        content_limit,
    };
    if write!(&mut writer, "{value:?}").is_err() {
        writer.output.push_str(TRUNCATION_SUFFIX);
    }
    writer.output
}

fn describe_bounded_list<T>(items: &[T], mut describe: impl FnMut(&T) -> String) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let item_limit = diagnostic_item_limit();
    let mut entries = items
        .iter()
        .take(item_limit)
        .map(&mut describe)
        .collect::<Vec<_>>();
    if items.len() > item_limit {
        entries.push(format!("… {} more omitted", items.len() - item_limit));
    }
    format!("[{}]", entries.join(", "))
}

fn diagnostic_item_limit() -> usize {
    if std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some() {
        usize::MAX
    } else {
        MAX_DIAGNOSTIC_ITEMS
    }
}

fn describe_context_pure_and_execution_facts(
    pure_facts: &[Proposition],
    execution_pure_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let total = pure_facts.len() + execution_pure_facts.len();
    if total == 0 {
        return "[]".to_string();
    }
    let item_limit = diagnostic_item_limit();
    let mut entries = pure_facts
        .iter()
        .chain(
            execution_pure_facts
                .iter()
                .map(ExecutionPureFact::proposition),
        )
        .take(item_limit)
        .map(|fact| describe_pure_fact(fact, parameters, arguments))
        .collect::<Vec<_>>();
    if total > item_limit {
        entries.push(format!("… {} more omitted", total - item_limit));
    }
    format!("[{}]", entries.join(", "))
}

/// The bounded spelling of a fact list against the current function's
/// parameters: a diagnostic that reports several fact lists (the condition
/// paths of an undecided C `if`, for one) must not print a kernel debug dump
/// of every memory snapshot those facts read.
pub(super) fn describe_pure_facts_for_diagnostic(
    pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }
    describe_bounded_list(pure_facts, |fact| {
        describe_pure_fact(fact, parameters, arguments)
    })
}

pub(super) fn describe_pure_facts(pure_facts: &[Proposition]) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }

    describe_bounded_list(pure_facts, |fact| describe_pure_fact(fact, &[], &[]))
}

pub(super) fn describe_unexpressed_pure_facts(
    facts: &[(Proposition, ClickError)],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    describe_bounded_list(facts, |(fact, error)| {
        format!(
            "{}: {}",
            describe_pure_fact(fact, parameters, arguments),
            error.message()
        )
    })
}

/// Describes one fact, and for a refused concrete named-contract formation
/// appends the explicit refinement theorem the user has to write.
///
/// The prefix is the same sentence [`describe_pure_fact`] prints without an
/// environment, so a reader (and a fixture) sees one diagnostic either way.
/// The skeleton itself comes from the kernel, built from the two declarations
/// the formation check read.
pub(super) fn describe_pure_fact_with_environment(
    fact: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    environment: &crate::kernel::CExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
) -> String {
    let description = describe_pure_fact(fact, parameters, arguments);
    let Some((contract, target)) = concrete_named_contract_fact(fact) else {
        return description;
    };
    let Some(skeleton) = crate::kernel::c_named_contract_refinement_theorem_skeleton(
        environment,
        contract,
        target,
        &declared_contract_parameter_spellings(predicate_environment, contract),
    ) else {
        return description;
    };
    format!("{description} automatically;\nprove it explicitly:\n{skeleton}")
}

/// The C spelling each of a named contract's parameters has in its source
/// declaration, for the positions the kernel cannot spell on its own.
///
/// The kernel models an aggregate pointer as a layout and keeps no struct
/// tag, so it prints `struct node*` as the pointer type it is modeled by. The
/// declaration that names the struct is right here on the surface, and this
/// is where the skeleton is rendered, so recover the tag from it rather than
/// teaching the kernel about tags. Every other position is left empty and
/// keeps the kernel's spelling.
fn declared_contract_parameter_spellings(
    predicate_environment: Option<&PredicateEnvironment>,
    contract: &str,
) -> Vec<Option<String>> {
    let Some(definition) =
        predicate_environment.and_then(|environment| environment.contract_definition(contract))
    else {
        return Vec::new();
    };
    definition
        .function_block()
        .signature()
        .parameters()
        .iter()
        .map(|parameter| {
            let name = parameter.struct_name()?;
            // A struct-valued parameter is modeled as a byte array; every
            // other tagged parameter is a pointer to the struct.
            let base = if matches!(parameter.click_type(), ClickType::C(C0Type::UInt8Array(_))) {
                format!("struct {name}")
            } else {
                format!("struct {name}*")
            };
            Some(if parameter.pointee_is_constant() {
                format!("const {base}")
            } else {
                base
            })
        })
        .collect()
}

/// The contract and concrete target of a named-contract fact over an exact
/// function address, which is the shape automatic formation refuses and the
/// shape a missing-fact report has to explain rather than blame.
fn concrete_named_contract_fact(fact: &Proposition) -> Option<(&str, &str)> {
    let Proposition::Predicate { name, arguments } = fact else {
        return None;
    };
    let contract = crate::kernel::CFunctionContract::surface_name_from_predicate(name)?;
    let [_, Term::CValue(CValue::Pointer(pointer))] = arguments.as_slice() else {
        return None;
    };
    let Pointer {
        block: PointerBlock::Function(target),
        offset: PointerOffsetTerm::Constant(0),
    } = pointer.pointer()
    else {
        return None;
    };
    Some((contract, target))
}

/// A lowering's value environment as the parameter/argument tables surface
/// reconstruction reads.
///
/// This is the only way a kernel variable becomes `hi` in a message, so every
/// diagnostic that holds a value environment and prints a lowered term goes
/// through it rather than showing `v2`. One definition, so a pure theorem and a
/// C proof name the same term the same way.
pub(in crate::surface) fn value_naming_tables(
    values: &std::collections::BTreeMap<String, CValue>,
) -> (Vec<syntax::C0Parameter>, Vec<CExpression>) {
    let mut parameters = Vec::with_capacity(values.len());
    let mut arguments = Vec::with_capacity(values.len());
    for (name, value) in values {
        parameters.push(syntax::C0Parameter::new(
            crate::surface::generics::c0_type_from_kernel(value.c_type()),
            name.clone(),
            None,
        ));
        arguments.push(CExpression::Value(value.clone()));
    }
    (parameters, arguments)
}

pub(super) fn describe_pure_fact(
    fact: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match fact {
        Proposition::CResourceComposition(context) => format!(
            "resource composition {}",
            describe_resource_facts(context.facts(), parameters, arguments)
        ),
        Proposition::Not(body) => {
            format!("not ({})", describe_pure_fact(body, parameters, arguments))
        }
        Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_)) => {
            "algebraic value equality".to_string()
        }
        Proposition::CMemoryLoadable { base, bytes, .. } => format!(
            "viewable(base={}, bytes={})",
            describe_pointer(base, parameters, arguments),
            describe_bitvector_with_context(bytes, parameters, arguments)
        ),
        Proposition::CResourceSeparate { left, right } => format!(
            "separate({}, {})",
            describe_c_resource(left, parameters, arguments),
            describe_c_resource(right, parameters, arguments)
        ),
        Proposition::CResourceContains { parent, child } => format!(
            "contains({}, {})",
            describe_c_resource(parent, parameters, arguments),
            describe_c_resource(child, parameters, arguments)
        ),
        Proposition::CMemoryMutatesOnly { writes, .. } => format!(
            "memory mutates only at {}",
            describe_bounded_list(writes, |(pointer, bytes)| {
                format!(
                    "{} ({bytes} bytes)",
                    describe_pointer(pointer, parameters, arguments)
                )
            })
        ),
        Proposition::CMemoryEffectSummary { mutable_ranges, .. } => format!(
            "memory effect ranges {}",
            describe_bounded_list(mutable_ranges, |range| {
                describe_memory_range(range, parameters, arguments)
            })
        ),
        Proposition::CHeapAllocationFreed {
            allocation_base,
            bytes,
            ..
        } => format!(
            "freed heap allocation {} ({} bytes)",
            describe_pointer(allocation_base, parameters, arguments),
            describe_bitvector_with_context(bytes, parameters, arguments)
        ),
        Proposition::ForAll { sort, .. } => {
            format!(
                "universal proposition over {}",
                crate::surface::proof_diagnostics::render::render_sort(sort)
            )
        }
        Proposition::Exists { sort, .. } => {
            format!(
                "existential proposition over {}",
                crate::surface::proof_diagnostics::render::render_sort(sort)
            )
        }
        // A ground constant has nothing to name but its value: say which
        // constant, so `false is true` does not read as a true condition.
        Proposition::ConditionIs(ConditionTerm::Constant(constant), value) => {
            format!("constant condition `{constant}` is {value}")
        }
        Proposition::ConditionIs(condition, value) => {
            let kind = match condition {
                ConditionTerm::AlgebraicEqual(_, _) => "algebraic equality",
                ConditionTerm::IntegerLessThan(_, _) => "Integer less-than",
                ConditionTerm::IntegerLessEqual(_, _) => "Integer less-or-equal",
                ConditionTerm::IntegerGreaterThan(_, _) => "Integer greater-than",
                ConditionTerm::IntegerGreaterEqual(_, _) => "Integer greater-or-equal",
                ConditionTerm::IntegerEqual(_, _) => "Integer equality",
                ConditionTerm::IntegerNotEqual(_, _) => "Integer disequality",
                ConditionTerm::Bitvector32SignedLessThan(_, _) => "signed less-than",
                ConditionTerm::Bitvector32SignedLessEqual(_, _) => "signed less-or-equal",
                ConditionTerm::Bitvector32SignedGreaterThan(_, _) => "signed greater-than",
                ConditionTerm::Bitvector32SignedGreaterEqual(_, _) => "signed greater-or-equal",
                ConditionTerm::Bitvector32Equal(_, _) => "int32 equality",
                ConditionTerm::Bitvector32SignedAddOverflows(_, _) => "addition overflow",
                ConditionTerm::Bitvector32SignedSubtractOverflows(_, _) => "subtraction overflow",
                ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _) => {
                    "multiplication overflow"
                }
                ConditionTerm::Bitvector32SignedDivideOverflows(_, _) => "division overflow",
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _) => "left-shift overflow",
                ConditionTerm::Bitvector64SignedLessThan(_, _) => "int64 signed less-than",
                ConditionTerm::Bitvector64SignedLessEqual(_, _) => "int64 signed less-or-equal",
                ConditionTerm::Bitvector64SignedGreaterThan(_, _) => "int64 signed greater-than",
                ConditionTerm::Bitvector64SignedGreaterEqual(_, _) => {
                    "int64 signed greater-or-equal"
                }
                ConditionTerm::Bitvector64UnsignedLessThan(_, _) => "uint64 less-than",
                ConditionTerm::Bitvector64UnsignedLessEqual(_, _) => "uint64 less-or-equal",
                ConditionTerm::Bitvector64UnsignedGreaterThan(_, _) => "uint64 greater-than",
                ConditionTerm::Bitvector64UnsignedGreaterEqual(_, _) => "uint64 greater-or-equal",
                ConditionTerm::Bitvector64Equal(_, _) => "64-bit equality",
                ConditionTerm::Bitvector64SignedAddOverflows(_, _) => "int64 addition overflow",
                ConditionTerm::Bitvector64SignedSubtractOverflows(_, _) => {
                    "int64 subtraction overflow"
                }
                ConditionTerm::Bitvector64SignedMultiplyOverflows(_, _) => {
                    "int64 multiplication overflow"
                }
                ConditionTerm::Bitvector64SignedDivideOverflows(_, _) => "int64 division overflow",
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(_, _) => {
                    "int64 left-shift overflow"
                }
                ConditionTerm::Float32(CFloatCondition::Comparison { .. }) => "float32 comparison",
                ConditionTerm::Float32(CFloatCondition::Classification { .. }) => {
                    "float32 classification"
                }
                ConditionTerm::Float64(CFloatCondition::Comparison { .. }) => "float64 comparison",
                ConditionTerm::Float64(CFloatCondition::Classification { .. }) => {
                    "float64 classification"
                }
                ConditionTerm::PointerOffsetEqual(_, _) => "pointer-offset equality",
                ConditionTerm::PointerEqual(_, _) => "pointer equality",
                ConditionTerm::Constant(_) => "constant condition",
                ConditionTerm::Variable(_) => "condition variable",
            };
            format!("{kind} is {value}")
        }
        Proposition::Predicate {
            name,
            arguments: predicate_arguments,
        } if crate::kernel::CFunctionContract::surface_name_from_predicate(name).is_some() => {
            let contract = crate::kernel::CFunctionContract::surface_name_from_predicate(name)
                .expect("guarded contract predicate");
            match predicate_arguments.as_slice() {
                [_, Term::CValue(CValue::Pointer(pointer))] => match pointer.pointer() {
                    Pointer {
                        block: PointerBlock::Function(target),
                        offset: PointerOffsetTerm::Constant(0),
                    } => {
                        format!("function `{target}` does not satisfy named contract `{contract}`")
                    }
                    // This arm describes a fact, and the same sentence serves
                    // a list of available facts and a report of a missing
                    // one. Say what the fact asserts; the surrounding
                    // sentence says whether it is held or wanted.
                    pointer => format!(
                        "named contract `{contract}` holds for {}",
                        describe_pointer(pointer, parameters, arguments)
                    ),
                },
                _ => format!("malformed named contract fact `{contract}`"),
            }
        }
        _ => describe_unclassified_pure_fact(fact),
    }
}

/// Renders a fact whose shape has no sentence above through the bounded
/// proposition printer.
///
/// `Debug` is not an option here. A kernel proposition carries shared
/// structure a developer dump repeats per occurrence — an algebraic term
/// holds its whole instantiated `AlgebraicSchemas`, and a state-indexed term
/// holds memory snapshots — so the fallback grows with the datatype
/// declarations rather than with the claim. The printer in
/// `proof_diagnostics::render` spells the same proposition in its source
/// vocabulary under node, depth, and byte bounds; `CLICK_FULL_DIAGNOSTICS`
/// still yields the developer dump.
fn describe_unclassified_pure_fact(fact: &Proposition) -> String {
    if std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some() {
        return format!("{fact:?}");
    }
    crate::surface::proof_diagnostics::render::render_proposition(fact)
}

pub(super) fn describe_execution_pure_facts(facts: &[ExecutionPureFact]) -> String {
    if facts.is_empty() {
        return "[]".to_string();
    }

    describe_bounded_list(facts, |fact| {
        describe_pure_fact(fact.proposition(), &[], &[])
    })
}

pub(super) fn describe_available_facts(
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "available pure facts: {}\n  available resource facts: {}",
        describe_context_pure_and_execution_facts(
            pure_facts,
            execution_pure_facts,
            parameters,
            arguments
        ),
        describe_resource_facts(resource_facts, parameters, arguments)
    )
}

/// Describes a fact a proof needs and does not have.
///
/// A named-contract fact over a concrete function address reads as a refused
/// refinement in [`describe_pure_fact`], which is what it means where
/// automatic formation refused it. Here nothing was refused: the fact was
/// never established, so name the two routes that establish it instead of
/// blaming the implementation.
fn describe_required_pure_fact(
    required: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match concrete_named_contract_fact(required) {
        Some((contract, target)) => format!(
            "no `{contract}(&{target})` fact is available; apply a refinement theorem or pass `&{target}` where `{contract}` is required"
        ),
        None => describe_pure_fact(required, parameters, arguments),
    }
}

pub(super) fn describe_missing_pure_fact(
    required: &Proposition,
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "missing pure fact: {}\n  {}",
        describe_required_pure_fact(required, parameters, arguments),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameters,
            arguments,
            execution_pure_facts
        )
    )
}

pub(super) fn describe_missing_resource_fact(
    required: &CResourceFact,
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    let mut note = String::new();
    if let CResource::Iterated(required_iterated) = required.resource()
        && let Some(held) = resource_facts
            .iter()
            .find_map(|fact| match fact.resource() {
                CResource::Iterated(held)
                    if held.owner() == required_iterated.owner() && !held.holes().is_empty() =>
                {
                    Some(held)
                }
                _ => None,
            })
    {
        note = format!(
            "\n  note: the held iterated ownership of `{}` has index {} taken out, and at a fold it must hold exactly the elements whose guard is true; `give` each element back, or store a guard value that makes its guard false, before folding",
            held.owner(),
            held.holes()
                .iter()
                .map(|hole| format!(
                    "`{}`",
                    describe_bitvector_with_context(hole, parameters, arguments)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    format!(
        "missing resource fact `{}`{note}\n  {}",
        describe_resource_fact(required, parameters, arguments),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameters,
            arguments,
            execution_pure_facts
        )
    )
}

/// The conditions that tell several statement successors apart.
///
/// A refusal that only says "got 2" leaves the reader to guess which `if`
/// inside an inlined helper is undecided. Each successor's own path facts name
/// the branch it took, so reporting the facts that are *not* common to every
/// successor names the undecided condition and its polarity, bounded by the
/// same item limit as every other fact list.
pub(super) fn describe_undecided_statement_successors(
    transitions: &[crate::surface::CertifiedStatementTransition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let item_limit = diagnostic_item_limit();
    let mut lines = Vec::new();
    for (index, transition) in transitions.iter().take(item_limit).enumerate() {
        let distinguishing = transition
            .path_facts
            .iter()
            .filter(|fact| {
                !transitions
                    .iter()
                    .all(|other| other.path_facts.contains(fact))
            })
            .take(item_limit)
            .map(|fact| describe_pure_fact(fact, parameters, arguments))
            .collect::<Vec<_>>();
        if distinguishing.is_empty() {
            continue;
        }
        lines.push(format!(
            "  successor {}: {}",
            index + 1,
            distinguishing.join(", ")
        ));
    }
    if lines.is_empty() {
        return String::new();
    }
    format!("undecided condition:\n{}\n", lines.join("\n"))
}

pub(super) fn describe_multiple_statement_successors_guidance(
    statement: &CStatement,
    successor_count: usize,
) -> String {
    if successor_count != 2
        || !matches!(
            statement,
            CStatement::Call { .. } | CStatement::CallAssign { .. }
        )
    {
        return String::new();
    }
    r#"
`step()` cannot choose between the two successors of this call. Use `outcomes` at this point:
outcomes {
    returned { step(); }
    threw { step(); }
}
The `step()` in each arm advances the selected path; add the remaining
`step()`, `execute()`, and `simp()` tactics inside that arm until all
contract claims are closed.
"#
    .to_string()
}

pub(super) fn describe_proof_context(
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "proof context:\n  pure facts: {}\n  resource facts: {}",
        describe_context_pure_and_execution_facts(
            pure_facts,
            execution_pure_facts,
            parameters,
            arguments
        ),
        describe_resource_facts(resource_facts, parameters, arguments)
    )
}

pub(super) fn describe_missing_proof_obligations(
    obligations: &[ProofObligation],
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    let item_limit = diagnostic_item_limit();
    let mut required = obligations
        .iter()
        .take(item_limit)
        .map(|obligation| match obligation.context() {
            Some(context) => format!(
                "{context}: {}",
                describe_pure_fact(obligation.proposition(), parameters, arguments)
            ),
            None => describe_pure_fact(obligation.proposition(), parameters, arguments),
        })
        .collect::<Vec<_>>();
    if obligations.len() > item_limit {
        required.push(format!("… {} more omitted", obligations.len() - item_limit));
    }

    let label = if required.len() == 1 {
        "missing pure fact"
    } else {
        "missing pure facts"
    };
    format!(
        "{label}: [{}]\n  {}",
        required.join(", "),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameters,
            arguments,
            execution_pure_facts
        )
    )
}

pub(super) fn describe_function_outcome(
    outcome: &CFunctionOutcome,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match outcome {
        CFunctionOutcome::Return { value, .. } => {
            format!(
                "returned {}",
                describe_c_value(value, parameters, arguments)
            )
        }
        CFunctionOutcome::Throw { value, .. } => {
            format!("threw {}", describe_c_value(value, parameters, arguments))
        }
        CFunctionOutcome::VerificationDiverges => "has no verified return frontier".to_string(),
        CFunctionOutcome::UndefinedBehavior(kind) => {
            format!("undefined behavior: {}", kind.description())
        }
        CFunctionOutcome::RuntimeError(error) => format!(
            "C operation could not be verified: {}",
            describe_runtime_error(error, parameters, arguments)
        ),
    }
}

pub(super) fn describe_runtime_error(
    error: &crate::kernel::CRuntimeError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        crate::kernel::CRuntimeError::UnboundVariable(name) => {
            format!("unbound variable `{name}`")
        }
        crate::kernel::CRuntimeError::UnknownFunction(name) => {
            format!("unknown function `{name}`")
        }
        crate::kernel::CRuntimeError::TypeMismatch => "type mismatch".to_string(),
        crate::kernel::CRuntimeError::LoadTypeMismatch {
            pointer,
            value_type,
            stored,
        } => {
            let found = match stored {
                Some(stored) => {
                    format!("found {}", describe_c_value(stored, parameters, arguments))
                }
                None => "did not fit the cell's value".to_string(),
            };
            format!(
                "a {}-byte load at `{}` {found}",
                value_type.byte_width(),
                describe_pointer(pointer, parameters, arguments)
            )
        }
        crate::kernel::CRuntimeError::PointerConversion(message) => message.clone(),
        crate::kernel::CRuntimeError::IndeterminatePointeeType => {
            "pointer operation has no known pointee type".to_string()
        }
        crate::kernel::CRuntimeError::WrongArity { expected, actual } => {
            format!("wrong argument count: expected {expected}, got {actual}")
        }
        crate::kernel::CRuntimeError::MissingReturn => "missing return".to_string(),
        crate::kernel::CRuntimeError::MissingResource { resource } => format!(
            "missing resource fact `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::MissingVerifiedFunctionRule(name) => format!(
            "cannot execute call to `{name}` opaquely: its contract has not been verified yet"
        ),
        crate::kernel::CRuntimeError::UnsupportedOpaqueFunctionContract(name) => format!(
            "cannot execute call to `{name}` opaquely: its contract refers to an internal program point that is unavailable at the call site"
        ),
        crate::kernel::CRuntimeError::AbstractFunctionPointerCall(name) => format!(
            "cannot verify call through function pointer `{name}`: no matching named contract is available for this value"
        ),
        crate::kernel::CRuntimeError::FunctionContract(message) => {
            format!("function contract could not be applied: {message}")
        }
        crate::kernel::CRuntimeError::UninitializedMutex { mutex } => format!(
            "could not prove that mutex `{}` was initialized on this path",
            describe_pointer(mutex, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::UnsupportedConcurrentMutex => {
            "Click cannot yet verify pthread workers sharing an initialized mutex".to_string()
        }
        crate::kernel::CRuntimeError::InvalidFree(reason) => match reason {
            crate::kernel::CInvalidFree::InteriorPointer => {
                "cannot free an interior pointer; free requires the allocation base".to_string()
            }
            crate::kernel::CInvalidFree::NonHeapPointer => {
                "cannot free a pointer that is not a live heap allocation".to_string()
            }
            crate::kernel::CInvalidFree::DoubleFree => {
                "cannot free an allocation whose lifetime has already ended".to_string()
            }
        },
        crate::kernel::CRuntimeError::UnresolvedAllocationOutcome => {
            "malloc result was neither refined by a null check nor returned".to_string()
        }
        crate::kernel::CRuntimeError::LiveAllocationLeak {
            allocation,
            resource,
            hint,
        } => {
            let mut message = format!(
                "live allocation obligation was neither returned nor freed: `{}`",
                describe_resource_fact(allocation, parameters, arguments)
            );
            if let Some(resource) = resource {
                message.push_str("; held by ");
                message.push_str(&describe_resource_fact(resource, parameters, arguments));
            }
            if let Some(hint) = hint {
                message.push(' ');
                message.push_str(hint);
            }
            message
        }
        crate::kernel::CRuntimeError::StaleResourceAfterFree { resource } => format!(
            "resource would remain usable after its allocation is freed: `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::DuplicateResource { resource } => format!(
            "duplicate resource fact `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::OverlappingOwnedMemoryResources { left, right } => format!(
            "overlapping owned memory resource facts `owns {}` and `owns {}`",
            describe_memory_range(left, parameters, arguments),
            describe_memory_range(right, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::ProducedCompositeOverlapsHeldResource {
            produced,
            piece,
            held,
        } => format!(
            "produced composite `{}` overlaps a resource the caller already holds: \
             its body `{}` overlaps `{}`",
            describe_c_resource(produced.resource(), parameters, arguments),
            describe_resource_fact(piece, parameters, arguments),
            describe_resource_fact(held, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::LoanRefusal(diagnostic) => {
            describe_loan_refusal(diagnostic, parameters, arguments)
        }
    }
}

/// Kernel `RuntimeError` includes ordinary proof refusals, so its name is not
/// a surface error category. Only explicitly marked verifier limitations are
/// reported as internal errors.
pub(super) fn runtime_refusal_kind(error: &crate::kernel::CRuntimeError) -> ClickErrorKind {
    match error {
        crate::kernel::CRuntimeError::UnsupportedConcurrentMutex => ClickErrorKind::Internal,
        _ => ClickErrorKind::Proof,
    }
}

/// The D13 shape for a refusal that is a conflict between two named things:
/// which loan refused, where that loan came from, what it protects, and what
/// the refused operation attempted. Both halves are bounded facts from the
/// refusal subject; nothing here reads the ledger or the resource frame.
fn describe_loan_conflict(
    diagnostic: &crate::kernel::LoanRefusalDiagnostic,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let subject = diagnostic.subject();
    let conflicting = subject.conflicting_resource_fact()?;
    let conflicting = describe_resource_fact(conflicting, parameters, arguments);
    if diagnostic.operation() == crate::kernel::LoanRefusalOperation::Entry {
        let viewed = subject.resource_fact()?;
        // This message follows the proof's own sentence about the contract
        // input, so it names the two clauses directly and adds no prefix.
        return Some(format!(
            "the contract's `views` clause overlaps its own `owns` clause: `{}` is already supported by `{conflicting}`; \
             a view must name authority the caller lends, not authority this contract owns",
            describe_resource_fact(viewed, parameters, arguments)
        ));
    }
    let attempted = subject.memory_range()?;
    let origin = match subject.origin()? {
        crate::kernel::LoanOriginKind::LocalStorage => "a view of local storage",
        crate::kernel::LoanOriginKind::ContractInputView => "a contract input view",
        crate::kernel::LoanOriginKind::LentOwner => "an owner lent for a call",
        crate::kernel::LoanOriginKind::Reborrow => "a reborrow of a live loan",
    };
    let loan = subject
        .loan_id()
        .map_or_else(String::new, |(arena, ordinal)| {
            format!(" (loan {arena}:{ordinal})")
        });
    Some(format!(
        "stable-view memory access conflicts with an active loan: the attempted range `{}` overlaps `{conflicting}`, lent as {origin}{loan}",
        describe_memory_range(attempted, parameters, arguments)
    ))
}

pub(in crate::surface) fn describe_loan_refusal(
    diagnostic: &crate::kernel::LoanRefusalDiagnostic,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(conflict) = describe_loan_conflict(diagnostic, parameters, arguments) {
        return conflict;
    }
    let category = match diagnostic.category() {
        crate::kernel::LoanRefusalCategory::ProvenOverlap => {
            "a required resource overlaps a live borrowed footprint"
        }
        crate::kernel::LoanRefusalCategory::SeparationUnproved => {
            "the verifier could not prove the requested ranges separate"
        }
        crate::kernel::LoanRefusalCategory::WrongHolder => {
            "the loan evidence names the wrong participant"
        }
        crate::kernel::LoanRefusalCategory::WrongArena => {
            "the loan evidence belongs to a different authority arena"
        }
        crate::kernel::LoanRefusalCategory::WrongScope => "the loan evidence names the wrong scope",
        crate::kernel::LoanRefusalCategory::ActiveDependency => {
            "an active loan dependency blocks this operation"
        }
        crate::kernel::LoanRefusalCategory::StalePredecessor => {
            "the loan evidence uses a stale predecessor state"
        }
        crate::kernel::LoanRefusalCategory::Recovery => {
            "loan recovery evidence is inconsistent or already consumed"
        }
        crate::kernel::LoanRefusalCategory::Lifetime => {
            "the loan scope has an incompatible lifetime state"
        }
        crate::kernel::LoanRefusalCategory::Unsupported => {
            "this resource shape is outside stable-view support"
        }
        crate::kernel::LoanRefusalCategory::Missing => {
            "the required loan backing or binding is missing"
        }
        crate::kernel::LoanRefusalCategory::InvalidEvidence => "the loan evidence is invalid",
    };
    let subject = diagnostic.subject();
    let subject = if let Some(resource) = subject.resource_fact() {
        format!(
            "; selected resource `{}`",
            describe_resource_fact(resource, parameters, arguments)
        )
    } else if let Some(range) = subject.memory_range() {
        format!(
            "; selected range `{}`",
            describe_memory_range(range, parameters, arguments)
        )
    } else {
        String::new()
    };
    let ids = {
        let subject = diagnostic.subject();
        let mut ids = Vec::new();
        if let Some((arena, ordinal)) = subject.loan_id() {
            ids.push(format!("loan {arena}:{ordinal}"));
        }
        if let Some((arena, ordinal)) = subject.scope_id() {
            ids.push(format!("scope {arena}:{ordinal}"));
        }
        if let Some((arena, ordinal)) = subject.share_id() {
            ids.push(format!("share {arena}:{ordinal}"));
        }
        if let Some((arena, ordinal)) = subject.support_id() {
            ids.push(format!("support {arena}:{ordinal}"));
        }
        if let Some(clause) = diagnostic.source_clause() {
            ids.push(format!("clause {clause}"));
        }
        if let Some(step) = diagnostic.source_step() {
            ids.push(format!("step {step}"));
        }
        if ids.is_empty() {
            String::new()
        } else {
            format!(" ({})", ids.join(", "))
        }
    };
    format!(
        "stable-view {} refused during {}{}{}",
        category,
        match diagnostic.operation() {
            crate::kernel::LoanRefusalOperation::Validate => "validation",
            crate::kernel::LoanRefusalOperation::Plan => "planning",
            crate::kernel::LoanRefusalOperation::Entry => "entry transition",
            crate::kernel::LoanRefusalOperation::Recovery => "recovery",
            crate::kernel::LoanRefusalOperation::Transition => "transition",
            crate::kernel::LoanRefusalOperation::MemoryAccess => "memory access",
        },
        subject,
        ids,
    )
}

pub(super) fn describe_resource_facts(
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if resource_facts.is_empty() {
        return "[]".to_string();
    }
    describe_bounded_list(resource_facts, |resource| {
        describe_resource_fact(resource, parameters, arguments)
    })
}

pub(super) fn describe_resource_fact(
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(range) = resource.memory_view_range() {
        return format!(
            "views {}",
            describe_memory_range(range, parameters, arguments)
        );
    }
    if let Some(range) = resource.memory_own_range() {
        return format!(
            "owns {}",
            describe_memory_range(range, parameters, arguments)
        );
    }
    match resource {
        CResourceFact::Own(CResource::MutexGuard(_), _)
        | CResourceFact::View(CResource::MutexGuard(_)) => "mutex guard".to_string(),
        CResourceFact::Own(CResource::Instance(instance), _)
        | CResourceFact::View(CResource::Instance(instance)) => format!(
            "{} instance {}#{}",
            if resource.is_own() { "owns" } else { "views" },
            instance.name(),
            instance.identity().0
        ),
        CResourceFact::Own(
            CResource::Composite {
                name,
                arguments: resource_arguments,
            }
            | CResource::Token {
                name,
                arguments: resource_arguments,
            },
            quantity,
        ) => {
            let resource =
                format_declared_resource(name, resource_arguments, parameters, arguments);
            if quantity.as_const() == Some(1) {
                format!("owns {resource}")
            } else {
                format!(
                    "owns {resource} (quantity {})",
                    describe_bitvector_with_context(quantity, parameters, arguments)
                )
            }
        }
        CResourceFact::View(
            CResource::Composite {
                name,
                arguments: resource_arguments,
            }
            | CResource::Token {
                name,
                arguments: resource_arguments,
            },
        ) => format!(
            "views {}",
            format_declared_resource(name, resource_arguments, parameters, arguments)
        ),
        CResourceFact::Own(CResource::Iterated(iterated), _)
        | CResourceFact::View(CResource::Iterated(iterated)) => format!(
            "{} {}",
            if resource.is_own() { "owns" } else { "views" },
            describe_iterated_memory(iterated, parameters, arguments)
        ),
        CResourceFact::Own(CResource::Memory(_), _) | CResourceFact::View(CResource::Memory(_)) => {
            unreachable!("memory resources handled above")
        }
    }
}

/// One iterated guarded-ownership fact, spelled as the clause it came from:
/// the bounded index, the guard, and the element range at that index, plus
/// the indices currently taken out.
pub(in crate::surface) fn describe_iterated_memory(
    iterated: &crate::kernel::CIteratedMemory,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let index = Bitvector32Term::Variable(crate::kernel::Variable(u64::MAX - 7));
    let element = iterated.element_range(&index);
    let spelled_index = describe_bitvector_with_context(&index, parameters, arguments);
    let element = format!(
        "{}[{}..{}]",
        describe_pointer(element.base(), parameters, arguments),
        describe_bitvector_with_context(element.start(), parameters, arguments),
        describe_bitvector_with_context(element.end(), parameters, arguments)
    )
    .replace(&spelled_index, "k");
    let guard_base = describe_pointer(iterated.guard().base(), parameters, arguments);
    let mut text = format!(
        "forall k in {}..{} where {}[k] {} {}: {} (the iterated clause of `{}`)",
        describe_bitvector_with_context(iterated.lower(), parameters, arguments),
        describe_bitvector_with_context(iterated.upper(), parameters, arguments),
        guard_base,
        if iterated.guard().holds_when_equal() {
            "=="
        } else {
            "!="
        },
        describe_bitvector_with_context(iterated.guard().value(), parameters, arguments),
        element,
        iterated.owner()
    );
    if !iterated.holes().is_empty() {
        text.push_str(&format!(
            ", with index {} taken out",
            iterated
                .holes()
                .iter()
                .map(|hole| describe_bitvector_with_context(hole, parameters, arguments))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    text
}

fn describe_c_resource(
    resource: &CResource,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match resource {
        CResource::Instance(instance) => {
            format!("instance {}#{}", instance.name(), instance.identity().0)
        }
        CResource::Memory(range) => {
            format!(
                "memory({})",
                describe_memory_range(range, parameters, arguments)
            )
        }
        CResource::Composite {
            name,
            arguments: resource_arguments,
        }
        | CResource::Token {
            name,
            arguments: resource_arguments,
        } => format_declared_resource(name, resource_arguments, parameters, arguments),
        CResource::MutexGuard(_) => "mutex guard".to_string(),
        CResource::Iterated(iterated) => describe_iterated_memory(iterated, parameters, arguments),
    }
}

fn describe_resource_subject(resource: &ResourceSubject) -> String {
    match resource {
        ResourceSubject::Memory(segment) => {
            format!("memory({})", describe_contract_segment(segment))
        }
        ResourceSubject::Declared {
            name, arguments, ..
        } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub(super) fn format_declared_resource(
    name: &str,
    resource_arguments: &[AlgebraicValue],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    format!(
        "{name}({})",
        resource_arguments
            .iter()
            .map(|argument| match argument {
                AlgebraicValue::C(value) => describe_c_value(value, parameters, arguments),
                AlgebraicValue::Integer(value) => describe_integer_term(value),
                AlgebraicValue::Algebraic(value) =>
                    format!("<{} model>", value.algebraic_type.name),
            })
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub(super) fn describe_memory_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(description) = describe_parameter_relative_range(range, parameters, arguments) {
        return description;
    }
    format!(
        "{}[{}..{}]",
        describe_pointer(range.base(), parameters, arguments),
        describe_bitvector_with_context(range.start(), parameters, arguments),
        describe_bitvector_with_context(range.end(), parameters, arguments)
    )
}

pub(super) fn describe_parameter_relative_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let (parameter, base_index) = parameter_relative_base(range, parameters, arguments)?;
    let (start, end) = parameter_relative_endpoints(&base_index, range);
    Some(format!(
        "{}[{}..{}]",
        parameter.name(),
        describe_bitvector_with_context(&start, parameters, arguments),
        describe_bitvector_with_context(&end, parameters, arguments)
    ))
}

/// The parameter a range is spelled against, with the element index of the
/// range's base from that parameter's base.
///
/// Every external pointer parameter shares one block, so any of them can name
/// a range as a symbolic offset from its own base: `b[0..1]` is also
/// `a[(b - a)..(b - a) + 1]`. Prefer the parameter the range sits at a
/// constant offset from, and fall back to the first symbolic one only when no
/// parameter does.
fn parameter_relative_base<'a>(
    range: &CMemoryRange,
    parameters: &'a [syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<(&'a syntax::C0Parameter, Bitvector32Term)> {
    let mut symbolic = None;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(base_index) = diagnostic_pointer_element_index_from_base(
            range.base(),
            base,
            diagnostic_parameter_element_width(parameter),
        ) else {
            continue;
        };
        if base_index.as_const().is_some() {
            return Some((parameter, base_index));
        }
        symbolic.get_or_insert((parameter, base_index));
    }
    symbolic
}

fn parameter_relative_endpoints(
    base_index: &Bitvector32Term,
    range: &CMemoryRange,
) -> (Bitvector32Term, Bitvector32Term) {
    (
        bitvector32_add(base_index.clone(), range.start().clone()),
        bitvector32_add(base_index.clone(), range.end().clone()),
    )
}

/// A note for a missing memory range that a held range of the same base and
/// start would cover if it were long enough. The verdict compared the two
/// ends; say which comparison was not established, so `owns b[0..n]` against
/// `b[0..1]` reads as `1 <= n` (the held range may be empty) rather than as a
/// resource the proof never held.
pub(super) fn describe_missing_range_end_note(
    error: &crate::kernel::CRuntimeError,
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let crate::kernel::CRuntimeError::MissingResource { resource } = error else {
        return String::new();
    };
    let Some(required) = resource
        .memory_own_range()
        .or_else(|| resource.memory_view_range())
    else {
        return String::new();
    };
    let Some(held_fact) = resource_facts.iter().find(|fact| {
        let held = if resource.is_own() {
            fact.memory_own_range()
        } else {
            fact.memory_own_range().or_else(|| fact.memory_view_range())
        };
        held.is_some_and(|held| {
            held.base() == required.base()
                && held.start() == required.start()
                && held.end() != required.end()
        })
    }) else {
        return String::new();
    };
    let held = held_fact
        .memory_own_range()
        .or_else(|| held_fact.memory_view_range())
        .expect("selected a memory range fact");
    let (required_end, held_end) = match parameter_relative_base(required, parameters, arguments) {
        Some((_, base_index)) => (
            parameter_relative_endpoints(&base_index, required).1,
            parameter_relative_endpoints(&base_index, held).1,
        ),
        None => (required.end().clone(), held.end().clone()),
    };
    format!(
        "\n  note: held `{}` covers `{}` only when `{} <= {}`",
        describe_resource_fact(held_fact, parameters, arguments),
        describe_memory_range(required, parameters, arguments),
        describe_bitvector_with_context(&required_end, parameters, arguments),
        describe_bitvector_with_context(&held_end, parameters, arguments),
    )
}

/// The snapshot and pointer a still-unresolved comparison side loads from, if
/// that side is exactly one load. A resolved side is a value and reads
/// nothing.
pub(super) fn unresolved_load(value: &CValue) -> Option<(SharedCMemory, Pointer)> {
    let term = match value {
        CValue::Int8(term) => term,
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term) => term,
        _ => return None,
    };
    match term {
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            Some((memory.clone(), pointer.as_ref().clone()))
        }
        Bitvector32Term::Variable(variable) => {
            crate::kernel::registered_load_origin_for_variable(variable)
        }
        _ => None,
    }
}

/// The model field a comparison side stands for, if that side is exactly one
/// model-field variable. A side that resolved to a value stands for nothing.
///
/// The registry the mint filled is the only route: the field value is stored
/// inside the instance fact, so the term carries no projection to read.
pub(super) fn unresolved_model_field(
    value: &CValue,
) -> Option<crate::kernel::model_fields::ModelFieldOrigin> {
    let variable = crate::kernel::model_fields::algebraic_value_variable(
        &crate::kernel::AlgebraicValue::C(value.clone()),
    )?;
    crate::kernel::model_fields::registered_model_field_origin(variable)
}

/// The explanation for one comparison side that is a model field: it reads the
/// outcome state's model, and the question is whether that is still the model
/// the earlier state held.
///
/// The two points are whole saved states, because a model field's version is
/// the value stored in the instance rather than a point on the memory history.
pub(super) fn describe_model_field_mismatch(
    value: &CValue,
    here: &CState,
    there: &CState,
    since: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let origin = unresolved_model_field(value)?;
    let explanation = resource_tracker::explain_at_states(
        resource_tracker::Resource::ModelField {
            identity: origin.identity,
            children: &[],
            field_index: origin.field_index,
        },
        resource_tracker::StatePoint::at(here),
        resource_tracker::StatePoint::at(there),
    );
    describe_resource_version_mismatch(&explanation, since, parameters, arguments)
}

/// The explanation for a comparison side that is a `count(..)`: its version is
/// the count the state holds, and the question is whether that is still the
/// count the earlier state held.
///
/// The transition that moved it already relates the two counts in the term — the
/// goal evaluated to `old + 1` — so the text states that relation rather than
/// computing a new fact.
pub(super) fn describe_population_mismatch(
    expression: &ContractExpression,
    here: &CState,
    there: &CState,
    since: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let ContractExpression::ResourceCount(clause) = expression else {
        return None;
    };
    let ResourceClause::Declared { name, .. } = clause.as_ref() else {
        return None;
    };
    let population = resource_tracker::sole_population_of_family(here, name)
        .or_else(|| resource_tracker::sole_population_of_family(there, name))?;
    let explanation = resource_tracker::explain_at_states(
        population.as_resource(),
        resource_tracker::StatePoint::at(here),
        resource_tracker::StatePoint::at(there),
    );
    describe_resource_version_mismatch(&explanation, since, parameters, arguments)
}

/// Names the write that stopped a comparison side from being carried across
/// the body: the step the resource tracker's walk stopped at, in the source
/// spelling, with what would settle it.
///
/// A parameter's memory and a file-scope array are separated by a resource
/// the contract holds or by a stated `separate`, never by their names, so a
/// contract that reads a range it declares no resource for is told which
/// write it has to rule out and how.
pub(super) fn describe_unseparated_write(
    value: &CValue,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let (memory, load) = unresolved_load(value)?;
    let explanation = resource_tracker::explain_last_same(
        resource_tracker::Resource::Cell {
            pointer: &load,
            bytes: crate::kernel::load_access_width_or_widest(&memory, &load),
        },
        &resource_tracker::ProgramPoint::at(&memory),
    );
    describe_resource_version_mismatch(
        &explanation,
        "earlier in this function",
        parameters,
        arguments,
    )
    .map(|mismatch| format!("; {mismatch}"))
}

/// A `fold` field initializer that reads a model this state no longer holds.
///
/// `let c = fold(cell(p), { rank: c.rank })` after `unfold(c)` is the shape:
/// the `unfold` consumed the instance, so `c.rank` names no model at the
/// `fold`. The kernel reports only that the identity is absent — it has no
/// spelling for `c` — so the sentence is written here, where the reader's own
/// expression is at hand, and it prints the initializer that verifies.
///
/// Nothing is said unless the state really does not hold the field and the
/// entry state does: a repair is printed only where it works, and where
/// `old(..)` would name nothing either the text says so instead.
pub(super) fn describe_unheld_model_field_initializer(
    initializer: &ContractExpression,
    state: &CState,
    entry_state: &CState,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let access = unheld_model_field_access(initializer, state, false)?;
    // The instance identity a fold writes is the reader's binder, so the
    // registry's spelling is available here too; register it in case this
    // access is the first one lowered.
    crate::kernel::model_fields::register_instance_spelling(access.identity, &access.owner);
    let explanation = resource_tracker::explain_at_states(
        resource_tracker::Resource::ModelField {
            identity: access.identity,
            children: &access.children,
            field_index: access.field_index,
        },
        resource_tracker::StatePoint::at(state),
        resource_tracker::StatePoint::at(entry_state),
    );
    describe_resource_version_mismatch(&explanation, "function entry", parameters, arguments)
}

/// The first model field in `expression` that `state` cannot resolve, skipping
/// the subtrees that resolve somewhere else: `old(..)` and `at(..)` read their
/// own snapshot, so a field they name is not this state's to hold. A shape
/// this bounded walk does not enter contributes nothing, and then the caller
/// falls back to the kernel's own sentence rather than guessing.
fn unheld_model_field_access<'a>(
    expression: &'a ContractExpression,
    state: &CState,
    through_old: bool,
) -> Option<&'a ResourceFieldAccess> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            ContractExpression::ResourceField(access) => {
                if state
                    .resource_instance_at_path(access.identity, &access.children)
                    .and_then(|instance| instance.fields().get(access.field_index))
                    .is_none()
                {
                    return Some(access);
                }
            }
            // A loop invariant reads `old(..)` at the loop's entry, which is
            // the state it is checked against, so there it is not a snapshot
            // of its own.
            ContractExpression::Old(inner) if through_old => pending.push(inner),
            ContractExpression::Old(_) | ContractExpression::At { .. } => {}
            ContractExpression::Negate(inner)
            | ContractExpression::BitwiseNot(inner)
            | ContractExpression::Field { base: inner, .. }
            | ContractExpression::ArrayIndex { base: inner, .. } => pending.push(inner),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right)
            | ContractExpression::Divide(left, right)
            | ContractExpression::Remainder(left, right)
            | ContractExpression::ShiftLeft(left, right)
            | ContractExpression::ShiftRight(left, right)
            | ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right)
            | ContractExpression::Index(left, right)
            | ContractExpression::SequenceConcat(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ContractExpression::AlgebraicConstructor { arguments, .. }
            | ContractExpression::Call { arguments, .. } => pending.extend(arguments),
            ContractExpression::SequenceLiteral(elements) => pending.extend(elements),
            // Every other shape either names no model field or reaches one
            // only through a form this bounded walk does not enter.
            _ => {}
        }
    }
    None
}

/// The refusal for a proposition that reads a field of a resource instance
/// `state` does not hold, usually because `unfold` consumed it. The field's
/// folded value stays nameable: `let { field: name } = unfold(owner);` binds
/// it, as a proof `match` arm binds a constructor payload.
///
/// `through_old` also reads fields under `old(..)`, for a loop invariant,
/// whose `old(..)` names the loop's entry state rather than the function's.
pub(in crate::surface) fn describe_consumed_instance_field_read(
    proposition: &ClickProposition,
    state: &CState,
    through_old: bool,
) -> Option<String> {
    let mut pending = vec![proposition];
    let mut expressions = Vec::new();
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                expressions.push(left);
                expressions.push(right);
            }
            ClickProposition::FloatClassification { expression, .. }
            | ClickProposition::Defined { expression } => expressions.push(expression),
            ClickProposition::Not(inner)
            | ClickProposition::ForAll { body: inner, .. }
            | ClickProposition::Exists { body: inner, .. } => pending.push(inner),
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ClickProposition::RangeAll {
                start, end, body, ..
            }
            | ClickProposition::RangeAny {
                start, end, body, ..
            } => {
                expressions.push(start);
                expressions.push(end);
                pending.push(body);
            }
            ClickProposition::PredicateCall { arguments, .. } => expressions.extend(arguments),
            // A snapshot proposition reads its own state.
            ClickProposition::At { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => {}
        }
    }
    let access = expressions
        .into_iter()
        .find_map(|expression| unheld_model_field_access(expression, state, through_old))?;
    if !access.children.is_empty() {
        return None;
    }
    Some(format!(
        "`{owner}.{field}` reads a field of `{owner}`, which is not held here; when \
         `unfold({owner})` consumed it, name the field's folded value where the instance is \
         unfolded with `let {{ {field}: name }} = unfold({owner});` and write `name` instead",
        owner = access.owner,
        field = access.field
    ))
}

/// The explanation for two evaluated sides that read one address at two
/// program points.
pub(super) fn describe_two_sided_version_mismatch(
    left: &CValue,
    right: &CValue,
    left_point: &str,
    right_point: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let (left_memory, left_load) = unresolved_load(left)?;
    let (right_memory, right_load) = unresolved_load(right)?;
    if left_load != right_load {
        return None;
    }
    let explanation = resource_tracker::explain(
        resource_tracker::Resource::Cell {
            pointer: &left_load,
            bytes: crate::kernel::load_access_width_or_widest(&left_memory, &left_load),
        },
        &resource_tracker::ProgramPoint::at(&left_memory),
        &resource_tracker::ProgramPoint::at(&right_memory),
    );
    // Both labels name real program points, so the sentence is written
    // against the earlier of the two: that is the one the value may have
    // changed *since*.
    let since = if explanation.there_is_earlier() {
        right_point
    } else {
        left_point
    };
    describe_resource_version_mismatch(&explanation, since, parameters, arguments)
}

/// The explanation for a goal and an available fact that spell alike and
/// differ only in which version they read, or for one proposition that reads
/// one resource at two program points.
/// `premise_point` names, as the reader would, the place the matching fact was
/// stated; the text says the resource may have changed since then.
pub(super) fn describe_proposition_version_mismatch(
    goal: &Proposition,
    premises: &[&Proposition],
    premise_point: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    // A goal that reads no resource has no version to differ about. Deciding
    // that first keeps this diagnostic, and the tracker's walk, off the
    // failure path of every proof that never touches memory.
    if !resource_tracker::reads_any_resource(goal) {
        return None;
    }
    if let Some((resource, here, there)) = resource_tracker::internal_version_mismatch(goal) {
        let explanation = resource_tracker::explain(resource.as_resource(), &here, &there);
        return describe_resource_version_mismatch(
            &explanation,
            "the snapshot the other side reads",
            parameters,
            arguments,
        );
    }
    // The structural question — do these two read the same resources at
    // different points — is asked first, so only a premise that answers it
    // is rendered and compared as text.
    let (resource, here, there) = premises
        .iter()
        .filter(|premise| **premise != goal)
        .find_map(|premise| {
            let mismatch = resource_tracker::version_mismatch(goal, premise)?;
            (describe_pure_fact_spelled(premise, parameters, arguments)
                == describe_pure_fact_spelled(goal, parameters, arguments))
            .then_some(mismatch)
        })?;
    let explanation = resource_tracker::explain(resource.as_resource(), &here, &there);
    describe_resource_version_mismatch(&explanation, premise_point, parameters, arguments)
}

/// One user-grade explanation of "these two same-looking terms read different
/// versions of a resource", used by every refusal whose real cause is that,
/// so the wording is identical wherever it is met.
///
/// `since` names, in the reader's own terms, the earlier of the two points
/// the question was about: "function entry", "the start of this iteration", a
/// `mark` label, or the place a fact was stated. The text picks the case that
/// applies, spells the resource and the blocking step with the caller's names,
/// and prints the concrete clause that would settle *that* case — an index
/// inequality for two indexes into one array, a filled-in `separate(..)` for
/// two objects nothing separates. A repair is printed only where it is known
/// to work; where none does, the text says what is missing instead. It prints
/// no memory: at most the blocking step, plus a count of the steps after it.
pub(super) fn describe_resource_version_mismatch(
    explanation: &resource_tracker::Explanation,
    since: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    let (at, stop) = explanation.outcome.blocking_step()?;
    if stop.reason == resource_tracker::StopReason::HistoryEnds {
        return Some(format!(
            "the recorded execution does not connect {since} to here."
        ));
    }
    let mut message = match &explanation.resource {
        resource_tracker::OwnedResource::Block(block) => {
            describe_block_fact_stop(block, &stop.change, parameters, arguments)
        }
        resource_tracker::OwnedResource::Cell { pointer, bytes } => describe_cell_version_stop(
            pointer,
            AccessWidths {
                read: *bytes,
                store: recorded_store_byte_width(at),
            },
            stop,
            since,
            parameters,
            arguments,
        ),
        // No term names a memory footprint, so no goal or premise a refusal
        // compares reads one. There is nothing to say rather than something
        // vague to say.
        resource_tracker::OwnedResource::Ranges(_) | resource_tracker::OwnedResource::AnyMemory => {
            return None;
        }
        resource_tracker::OwnedResource::ModelField {
            identity,
            children,
            field_index,
        } => describe_model_field_version_stop(*identity, children, *field_index, stop, since)?,
        resource_tracker::OwnedResource::Population {
            name,
            arguments: population_arguments,
        } => describe_population_version_stop(
            name,
            population_arguments,
            stop,
            since,
            parameters,
            arguments,
        ),
    };
    if explanation.crossed_after > 0 {
        let steps = explanation.crossed_after;
        let _ = if steps == 1 {
            write!(message, " The one later step does not touch it.")
        } else {
            write!(message, " The {steps} later steps do not touch it.")
        };
    }
    Some(message)
}

/// One model field, and the step that replaced the model it belongs to.
///
/// The field is spelled from the registry the mint filled, so this says
/// `c.rank`; where either half of that name is unknown there is nothing to say,
/// because a half-spelled field would read like source the reader could search
/// for.
fn describe_model_field_version_stop(
    identity: Variable,
    children: &[String],
    field_index: usize,
    stop: &resource_tracker::Stop,
    since: &str,
) -> Option<String> {
    let field = crate::kernel::model_fields::instance_field_spelling(identity, field_index)?;
    // A parent-qualified path is not what the registry names, so it has no
    // spelling of its own and this says nothing rather than the parent's.
    if !children.is_empty() {
        return None;
    }
    let owner = crate::kernel::model_fields::registered_instance_spelling(identity)?;
    let promise = format!("`ensures {field} == old({field})`");
    Some(match &stop.change {
        // A value only this state has lost can still be named where it was
        // held. One neither point holds can be named nowhere, and then the
        // text says what is missing instead of a repair that would not work.
        resource_tracker::Change::NotHeld {
            missing_there: false,
            ..
        } => format!(
            "`{field}` names no model here: `{owner}` was consumed since {since}, so this state \
             holds no field to read. Name the value it had there, `old({field})`."
        ),
        resource_tracker::Change::NotHeld { .. } => format!(
            "`{field}` names no model here, and none at {since} either: nothing holds `{owner}` at \
             either point, so `old({field})` names nothing to fall back on."
        ),
        resource_tracker::Change::ModelReplaced { by } => {
            let cause = match by {
                Some(crate::kernel::model_fields::ModelMint::CallReturn { callee }) => format!(
                    "the call to `{callee}` returned ownership of `{owner}` with a new model, and \
                     `{callee}` promises nothing about this field. If it keeps the field, state \
                     {promise} on `{callee}`."
                ),
                Some(crate::kernel::model_fields::ModelMint::Produced { callee }) => format!(
                    "the call to `{callee}` produced `{owner}`, so its model is fresh here. Only \
                     an {promise} on `{callee}` relates it to an earlier one."
                ),
                Some(crate::kernel::model_fields::ModelMint::LoopHead) => format!(
                    "the loop owns `{owner}`, and a loop head is an arbitrary visit, so it gives \
                     `{owner}` a fresh model. If the body keeps the field, carry it through as \
                     `invariant {field} == old({field});`."
                ),
                Some(crate::kernel::model_fields::ModelMint::Refinement) => format!(
                    "contract/implementation refinement gave `{owner}` an arbitrary model, so only \
                     what both sides state relates the two."
                ),
                // The entry model is the old version, never the replacement,
                // so it is not a cause; `replacing_change` skips it.
                Some(crate::kernel::model_fields::ModelMint::ContractEntry) | None => format!(
                    "the two states store different models for `{owner}`, and no step here says \
                     which replaced which. State {promise} wherever the model is replaced."
                ),
            };
            format!("`{field}` may have changed since {since}: {cause}")
        }
        // A model field's answer is never a memory step: `same_at_states` is
        // the only route to one, and it produces the two arms above.
        _ => return None,
    })
}

/// One counted population, and the transition that moved it.
///
/// The transition relates the two counts arithmetically in the term itself —
/// `old + 1` is what the goal already evaluated to — so the repair is to state
/// that relation. Nothing new is computed here.
fn describe_population_version_stop(
    name: &str,
    resource_arguments: &[AlgebraicValue],
    stop: &resource_tracker::Stop,
    since: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let population = format!(
        "count({})",
        format_declared_resource(name, resource_arguments, parameters, arguments)
    );
    match &stop.change {
        resource_tracker::Change::NotHeld { .. } => format!(
            "`{population}` names no population here: the family is not in scope at both points, \
             so there is no count to compare."
        ),
        _ => format!(
            "`{population}` changed since {since}: a `produces` or `consumes` transition in \
             between moved it. The transition relates the two counts, so state that relation, as \
             `ensures {population} == old({population}) + 1`."
        ),
    }
}

/// A fact about a whole array. The block walk crosses only a step the kernel
/// proves leaves the object alone, and it reads no stated separation at all,
/// so this case has no `separate(..)` to offer and says so rather than
/// sending the reader to write one.
fn describe_block_fact_stop(
    block: &PointerBlock,
    change: &resource_tracker::Change,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let named = describe_memory_block(block, parameters, arguments)
        .map(|name| format!("`{name}`"))
        .unwrap_or_else(|| "this array".to_string());
    format!(
        "a fact about {named} as a whole does not carry across {}. Only a step the kernel proves \
         leaves the whole object alone carries one, and a stated `separate(...)` is not read here.",
        describe_step(change, parameters, arguments)
    )
}

/// The two access widths a separation question is really about, carried to
/// the renderer beside the two addresses.
///
/// Separation is a question about bytes, not addresses
/// (`docs/internals/resource-tracker.md`, "The byte question, which is not one
/// of them"), so a refusal that names only the addresses names half of what
/// was compared. `read` is the width the resource was asked about with, and
/// may be the widest scalar where the load recorded none — over-stating it can
/// only withhold a repair, never invent one. `store` is exact where it is
/// present: it is read off the recorded edge, which carries the value.
#[derive(Clone, Copy)]
struct AccessWidths {
    read: u32,
    store: Option<u32>,
}

/// How many bytes the blocking step wrote.
///
/// `Change::Store` keeps the address and drops the width, and the width is
/// the whole byte question, so it is read back off the recorded edge the walk
/// stopped below — the same edge the tracker classified. `None` for every
/// other step, and for a point that records no edge at all.
fn recorded_store_byte_width(at: Option<&resource_tracker::ProgramPoint>) -> Option<u32> {
    match at?.snapshot().derivation()?.as_ref() {
        crate::kernel::CMemoryDerivation::Store { value, .. } => Some(value.c_type().byte_width()),
        _ => None,
    }
}

/// One cell, and the step that ended the stretch its version was known over.
fn describe_cell_version_stop(
    pointer: &Pointer,
    widths: AccessWidths,
    stop: &resource_tracker::Stop,
    since: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let cell = describe_source_cell(pointer, parameters, arguments);
    // Without the C names — a pure theorem has none — the address has no
    // source spelling, so the sentence says "this read" rather than repeating
    // a verifier-owned one.
    let named = match &cell {
        Some(cell) => format!("`{}`", cell.text()),
        None => "this read".to_string(),
    };
    let certain = stop.reason == resource_tracker::StopReason::Affected;
    let changed = if certain {
        "changed"
    } else {
        "may have changed"
    };
    format!(
        "{named} {changed} since {since}: {}",
        describe_cell_cause(cell.as_ref(), widths, stop, certain, parameters, arguments)
    )
}

/// Why this cell's chain broke, and the clause that would mend it.
fn describe_cell_cause(
    cell: Option<&SourceCell>,
    widths: AccessWidths,
    stop: &resource_tracker::Stop,
    certain: bool,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match &stop.change {
        resource_tracker::Change::Store { pointer } => {
            describe_store_cause(cell, pointer, widths, certain, parameters, arguments)
        }
        resource_tracker::Change::Call { ranges } => {
            describe_havoc_cause("the call in between", cell, ranges, parameters, arguments)
        }
        resource_tracker::Change::Loop {
            ranges: Some(ranges),
        } => describe_havoc_cause("the loop in between", cell, ranges, parameters, arguments),
        resource_tracker::Change::Loop { ranges: None } => {
            "the loop in between may have written it. The loop declares no write set, so nothing \
             can be shown separate from it: carry the fact through it as an invariant instead."
                .to_string()
        }
        resource_tracker::Change::Free { allocation } => {
            match describe_memory_block(&allocation.block, parameters, arguments) {
                Some(freed) => format!(
                    "the allocation at `{freed}` was released in between, and nothing shows it \
                     separate from this cell."
                ),
                None => {
                    "an allocation was released in between, and nothing shows it separate from \
                     this cell."
                        .to_string()
                }
            }
        }
        resource_tracker::Change::ContractRetirement { allocation } => {
            match describe_memory_block(&allocation.block, parameters, arguments) {
                Some(retired) => format!(
                    "the contract in between may have released the allocation at `{retired}`."
                ),
                None => "the contract in between may have released this allocation.".to_string(),
            }
        }
        resource_tracker::Change::Allocation { .. } => {
            "an allocation in between made this storage live.".to_string()
        }
        resource_tracker::Change::AllocationPending => {
            "an allocation in between has no resolved address yet.".to_string()
        }
        resource_tracker::Change::ContractAllocationClaims => {
            "a contract's allocation claims moved in between.".to_string()
        }
        resource_tracker::Change::Declaration { .. } => {
            "a declaration in between added storage to the state.".to_string()
        }
        resource_tracker::Change::LifetimeEnd { .. } => {
            "a local's lifetime ended in between.".to_string()
        }
        resource_tracker::Change::CellsForgotten => {
            "a step in between dropped the cell values it had cached.".to_string()
        }
        resource_tracker::Change::BeginningOfHistory => {
            "the recorded execution reaches no further back.".to_string()
        }
        // A cell's change is always a recorded memory step, so the three
        // saved-state changes are unreachable for this resource; saying that
        // plainly beats inventing a cause.
        resource_tracker::Change::ModelReplaced { .. }
        | resource_tracker::Change::PopulationMoved
        | resource_tracker::Change::NotHeld { .. } => {
            "no recorded step in between names this cell.".to_string()
        }
    }
}

/// A store, and the fact that would tell it apart from this cell: an index
/// inequality when both address one array, a filled-in `separate(..)` when
/// they address two objects. Both are printed with the reader's own terms,
/// and only when the terms are the reader's — an index the lowering owns is
/// spelled `a[…]`, and no inequality is proposed over a name nobody wrote.
///
/// An index inequality is offered only where the indexes really are the
/// undecided part. A store wider than the array's element reaches past the
/// element it names, so differing indexes do not separate it from the
/// neighbour it covers, and asking for `i != j` there sends the reader to
/// state a premise that will not close the goal. That case is answered by
/// [`describe_wide_store_byte_reach`] instead.
fn describe_store_cause(
    cell: Option<&SourceCell>,
    written: &Pointer,
    widths: AccessWidths,
    certain: bool,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let store = describe_source_cell(written, parameters, arguments);
    if certain {
        return match &store {
            Some(store) => format!("the store to `{}` wrote it.", store.text()),
            None => "a store in between wrote it.".to_string(),
        };
    }
    let (Some(cell), Some(store)) = (cell, &store) else {
        // A read through a pointer the function received rather than an object
        // it names has no source spelling, so only one side can be printed.
        // Printing the store is still the whole content of the answer: it is
        // the step the reader has to separate their read from.
        return match &store {
            Some(store) => format!(
                "the store to `{}` may have written it, and nothing tells that address apart \
                 from this read.",
                store.text()
            ),
            None => "a store in between may have written it, and nothing tells the two addresses \
                     apart."
                .to_string(),
        };
    };
    if cell.object == store.object {
        return describe_same_object_store_cause(cell, store, widths);
    }
    let repair = match (cell.element_range(), store.element_range()) {
        (Some(read), Some(written)) => format!(" {}", spelled_separation_repair(&read, &written)),
        _ => format!(
            " If they are separate, require a `separate(memory({}[…]), memory({}[…]))` between \
             them.",
            cell.object, store.object
        ),
    };
    format!(
        "the store to `{}` may have written it, because `{}` may point into `{}`.{repair}",
        store.text(),
        cell.object,
        store.object
    )
}

/// A read and a store that address one object, where the only thing that can
/// tell them apart is where they sit inside it.
///
/// The byte question is asked before the address one: a store the reader
/// cannot separate by index at all must not be answered with an index
/// inequality. Where the store fits inside the element it names, the indexes
/// really are the undecided part and the inequality is the answer.
fn describe_same_object_store_cause(
    cell: &SourceCell,
    store: &SourceCell,
    widths: AccessWidths,
) -> String {
    match (cell.named_index(), store.named_index()) {
        (Some(read), Some(written)) if read != written => {
            if let Some(byte_reach) =
                describe_wide_store_byte_reach(cell, store, read, written, widths)
            {
                return byte_reach;
            }
            format!(
                "the store to `{}` may have written it. If `{read}` and `{written}` differ, state \
                 `{read} != {written}`.",
                store.text()
            )
        }
        (Some(read), _) => format!(
            "the store to `{}` may have written it. Nothing states that its index differs from \
             `{read}`.",
            store.text()
        ),
        _ => format!(
            "the store to `{}` may have written it, and nothing tells the two indexes apart.",
            store.text()
        ),
    }
}

/// [`describe_same_object_store_cause`] driven from the surface tests with
/// the plain data the byte question is asked with: one object, the two
/// element spellings, and the three widths. The renderer's own types stay
/// private; this is the shape a test can state a case in.
#[cfg(test)]
pub(in crate::surface) fn store_cause_between_indexes_for_tests(
    object: &str,
    read_index: &str,
    written_index: &str,
    element_bytes: Option<u32>,
    read_bytes: u32,
    store_bytes: Option<u32>,
) -> String {
    let spelled = |index: &str| SourceCell {
        object: object.to_string(),
        index: CellIndex::Named(index.to_string()),
        element_bytes,
    };
    describe_same_object_store_cause(
        &spelled(read_index),
        &spelled(written_index),
        AccessWidths {
            read: read_bytes,
            store: store_bytes,
        },
    )
}

/// The refusal for a store whose *bytes* reach this cell, as opposed to one
/// whose *address* is merely undecided. `None` where the store fits inside
/// the element it names, which is the case the index inequality answers.
///
/// A store wider than the array's element covers the element it names and the
/// ones above it, so `i != j` leaves `i == j + 1` open and states a premise
/// that does not close the goal. What does separate them is the rule
/// `one_element_gap_separates_bytes` runs
/// (`src/kernel/reasoning/memory_resolution.rs`): an address ladder
/// establishes a gap of one element, a bare disequality leaves the direction
/// open so both accesses must fit in it, and a strict order fixes the
/// direction so only the *lower* access must — the upper one extends away
/// from the gap. So the repair is the strict order that puts the read below
/// the store, and it is printed only where the read fits in one element,
/// because that is the only case the rule clears. Where the read is wider
/// than an element too — including where its width is the widest-scalar
/// fallback rather than a recorded one — no order is offered and the text
/// says what an order would have to establish.
fn describe_wide_store_byte_reach(
    cell: &SourceCell,
    store: &SourceCell,
    read_index: &str,
    written_index: &str,
    widths: AccessWidths,
) -> Option<String> {
    let element = cell.element_bytes.filter(|bytes| *bytes > 0)?;
    // One object is one element width; comparing the two spellings is cheap
    // insurance against a pair that reached here through different bases.
    if store.element_bytes != cell.element_bytes {
        return None;
    }
    let store_bytes = widths.store?;
    if store_bytes <= element {
        return None;
    }
    let spanned = store_bytes.div_ceil(element);
    let cause = format!(
        "the store to `{}` writes {store_bytes} bytes where `{}` has {element}-byte elements, so \
         it covers the {spanned} elements from `{}` up and `{read_index} != {written_index}` \
         rules out only the first of them.",
        store.text(),
        store.object,
        store.text()
    );
    Some(if widths.read <= element {
        format!(
            "{cause} State `{read_index} < {written_index}`, which puts `{}` below every byte the \
             store writes.",
            cell.text()
        )
    } else {
        format!(
            "{cause} Only a stated order between the indexes can separate them, and it has to put \
             an access of at most {element} bytes below the other."
        )
    })
}

/// A call or a loop, which declares the ranges it may write. The repair is a
/// separation from that write set, and it is spelled out when the step
/// declares exactly one range and the cell has a source spelling.
fn describe_havoc_cause(
    step: &str,
    cell: Option<&SourceCell>,
    ranges: &[CMemoryRange],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let spelled = ranges
        .iter()
        .map(|range| describe_source_range(range, parameters, arguments))
        .collect::<Option<Vec<_>>>()
        .filter(|spelled| !spelled.is_empty());
    let Some(spelled) = spelled else {
        return format!(
            "{step} may have written it, and the ranges it may write are not shown separate from \
             it."
        );
    };
    let cell_range = cell.and_then(SourceCell::element_range);
    if let ([written], Some(read)) = (spelled.as_slice(), cell_range.as_ref()) {
        return format!(
            "{step} may write `{written}`, which is not shown separate from it. {}",
            spelled_separation_repair(read, written)
        );
    }
    format!(
        "{step} may write {}, and none of them is shown separate from it.",
        bounded_range_list(&spelled)
    )
}

/// The repair for two objects nothing separates, when both ranges have a
/// source spelling: the `separate(..)` to state, and the `views` clause that
/// says the same thing without one.
///
/// A contract's transferred clauses and its borrowed `views` clauses denote
/// disjoint memory at entry
/// (`kernel::contract_entry_partition_facts`,
/// `docs/internals/resource-tracker.md`, "The entry partition"), so a
/// function that already transfers the written range separates it from every
/// range it lends by declaring the read as a `views` clause. Both halves are
/// printed only where they verify the situation they are printed for, which
/// is why the second one names its condition rather than asserting it: this
/// renderer sees two addresses, not the contract's clause list, and the
/// entry partition does not reach a range transferred only inside a folded
/// composite. Every range that reaches here is spelled through a parameter
/// or a file-scope declaration — `SourceCell::element_range` yields nothing
/// for a local — so both clauses are ones the reader can write.
fn spelled_separation_repair(read: &str, written: &str) -> String {
    format!(
        "If they are separate, require `separate(memory({read}), memory({written}))`; where the \
         contract already transfers `{written}` with `owns` or `consumes`, declaring \
         `views {read}` says the same."
    )
}

/// At most three written ranges, so a wide write set stays one short clause.
fn bounded_range_list(ranges: &[String]) -> String {
    const SHOWN: usize = 3;
    let listed = ranges
        .iter()
        .take(SHOWN)
        .map(|range| format!("`{range}`"))
        .collect::<Vec<_>>()
        .join(", ");
    match ranges.len().checked_sub(SHOWN) {
        Some(rest) if rest > 0 => format!("{listed} and {rest} more"),
        _ => listed,
    }
}

/// The recorded step the walk stopped at, as a noun phrase a sentence can be
/// built around. No recorded step carries a source span today, so it is
/// described rather than quoted; `docs/internals/resource-tracker.md` says
/// what a line number would take.
fn describe_step(
    change: &resource_tracker::Change,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match change {
        resource_tracker::Change::Store { pointer } => {
            match describe_source_cell(pointer, parameters, arguments) {
                Some(store) => format!("the store to `{}`", store.text()),
                None => "a store".to_string(),
            }
        }
        resource_tracker::Change::Call { .. } => "the call".to_string(),
        resource_tracker::Change::Loop { .. } => "the loop".to_string(),
        resource_tracker::Change::Free { allocation } => {
            match describe_memory_block(&allocation.block, parameters, arguments) {
                Some(freed) => format!("the release of `{freed}`"),
                None => "a released allocation".to_string(),
            }
        }
        resource_tracker::Change::ContractRetirement { allocation } => {
            match describe_memory_block(&allocation.block, parameters, arguments) {
                Some(retired) => format!("the contract possibly releasing `{retired}`"),
                None => "a contract possibly releasing an allocation".to_string(),
            }
        }
        resource_tracker::Change::Allocation { .. } => "an allocation".to_string(),
        resource_tracker::Change::AllocationPending => {
            "an allocation with no resolved address".to_string()
        }
        resource_tracker::Change::ContractAllocationClaims => {
            "a contract's allocation claims moving".to_string()
        }
        resource_tracker::Change::Declaration { .. } => "a declaration".to_string(),
        resource_tracker::Change::LifetimeEnd { .. } => "a local's lifetime ending".to_string(),
        resource_tracker::Change::CellsForgotten => {
            "a step that dropped its cached cell values".to_string()
        }
        resource_tracker::Change::BeginningOfHistory => {
            "the start of the recorded execution".to_string()
        }
        resource_tracker::Change::ModelReplaced { .. } => "a replaced model".to_string(),
        resource_tracker::Change::PopulationMoved => "a population transition".to_string(),
        resource_tracker::Change::NotHeld { .. } => {
            "a resource this state does not hold".to_string()
        }
    }
}

/// Where an address sits inside the object that holds it.
enum CellIndex {
    /// The element index, spelled with the caller's own names.
    Named(String),
    /// The address is the object itself: a struct field, a declaration.
    Whole,
    /// The address is inside the object, at an index only the lowering has a
    /// name for. The reader is shown `a[…]` rather than a kernel variable.
    Unnamed,
}

/// An address as the source writes it, split into the object it names and the
/// element index inside it, so a repair can name either part: `a` and `m` for
/// `a[m]`, `g` and `0` for `g[0]`.
struct SourceCell {
    object: String,
    index: CellIndex,
    /// The width of one element of the object the index counts in, where the
    /// spelling came from a declared pointer or array type. `None` where the
    /// address was spelled through a block name rather than a typed base, and
    /// then no byte question is asked of it: a width nobody declared is not
    /// one a refusal may reason from.
    element_bytes: Option<u32>,
}

impl SourceCell {
    fn text(&self) -> String {
        match &self.index {
            CellIndex::Named(index) => format!("{}[{index}]", self.object),
            CellIndex::Whole => self.object.clone(),
            CellIndex::Unnamed => format!("{}[…]", self.object),
        }
    }

    fn named_index(&self) -> Option<&str> {
        match &self.index {
            CellIndex::Named(index) => Some(index),
            CellIndex::Whole | CellIndex::Unnamed => None,
        }
    }

    /// The one-element range holding exactly this cell, as `memory(..)` takes
    /// it: `a[0]` is `a[0..1]` and `a[m]` is `a[m..m + 1]`. Only a literal or
    /// a plain name is pasted in; a compound index would need a parenthesised
    /// form this has not been shown to get right, and a repair that has not
    /// been shown to work is not offered.
    fn element_range(&self) -> Option<String> {
        let CellIndex::Named(index) = &self.index else {
            return None;
        };
        if let Ok(start) = index.parse::<i64>() {
            // A negative element index is not a range `separate` would take,
            // and a clause that would not parse is not a repair.
            return start
                .checked_add(1)
                .filter(|_| start >= 0)
                .map(|end| format!("{}[{start}..{end}]", self.object));
        }
        let plain = !index.is_empty()
            && index.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !index.starts_with(|c: char| c.is_ascii_digit());
        plain.then(|| format!("{}[{index}..{index} + 1]", self.object))
    }
}

/// An address as the source writes it — `a[m]`, `g[0]`, `p->next` — or
/// nothing when the C names this diagnostic was given recover none. Unlike
/// [`describe_pointer`], the index is spelled with the caller's own names,
/// and a name that could only be a verifier-owned one is refused instead of
/// shown.
fn describe_source_cell(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<SourceCell> {
    // Two parameters can point into one block, and then every one of them
    // can express the address -- `b[j]` is also `a[(b - a) + j]`. The
    // shortest spelling is the one written through the parameter the address
    // actually belongs to, and picking it is deterministic.
    let mut best: Option<SourceCell> = None;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(field) =
            describe_parameter_struct_field_pointer(pointer, parameter, base.pointer())
        {
            return Some(SourceCell {
                object: field,
                index: CellIndex::Whole,
                element_bytes: None,
            });
        }
        let element_width = diagnostic_parameter_element_width(parameter);
        let Some(index) = diagnostic_pointer_element_index_from_base(pointer, base, element_width)
        else {
            continue;
        };
        let spelled = SourceCell {
            object: parameter.name().to_string(),
            index: if bitvector_is_source_spelled(&index, parameters, arguments) {
                CellIndex::Named(describe_bitvector_with_context(
                    &index, parameters, arguments,
                ))
            } else {
                CellIndex::Unnamed
            },
            element_bytes: u32::try_from(element_width).ok(),
        };
        if best
            .as_ref()
            .is_none_or(|best| prefer_source_cell(&spelled, best))
        {
            best = Some(spelled);
        }
    }
    if best.is_some() {
        return best;
    }
    let declared = describe_memory_block(&pointer.block, parameters, arguments)?;
    match &pointer.offset {
        // A local's block holds one declared object, and the name the reader
        // wrote for it *is* the address: `q`, not `q[0]`, which would read as a
        // store through `q` rather than to it. A local array's element zero
        // loses its index this way, which costs an index-inequality repair the
        // reader could not have used anyway -- the array is one object, so the
        // two spellings name the same storage either way.
        PointerOffsetTerm::Constant(0) if pointer.block.starts_with("local:") => Some(SourceCell {
            object: declared,
            index: CellIndex::Whole,
            element_bytes: None,
        }),
        PointerOffsetTerm::Constant(0) => Some(SourceCell {
            object: declared,
            index: CellIndex::Named("0".to_string()),
            element_bytes: None,
        }),
        PointerOffsetTerm::Constant(_) => Some(SourceCell {
            object: format!("{declared}+{}", describe_pointer_offset(&pointer.offset)),
            index: CellIndex::Whole,
            element_bytes: None,
        }),
        // Any other offset is a term the lowering owns; the object is still
        // the reader's, so it is named and the index is not.
        _ => Some(SourceCell {
            object: declared,
            index: CellIndex::Unnamed,
            element_bytes: None,
        }),
    }
}

/// A spelling the reader can act on beats one they cannot, and among equals
/// the shortest wins. Deterministic either way.
fn prefer_source_cell(candidate: &SourceCell, best: &SourceCell) -> bool {
    match (
        candidate.named_index().is_some(),
        best.named_index().is_some(),
    ) {
        (true, false) => true,
        (false, true) => false,
        _ => candidate.text().len() < best.text().len(),
    }
}

/// A memory range as the source writes it, or nothing when its base or its
/// bounds have no spelling in the caller's own names.
fn describe_source_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(base_index) = diagnostic_pointer_element_index_from_base(
            range.base(),
            base,
            diagnostic_parameter_element_width(parameter),
        ) else {
            continue;
        };
        let start = bitvector32_add(base_index.clone(), range.start().clone());
        let end = bitvector32_add(base_index, range.end().clone());
        if !bitvector_is_source_spelled(&start, parameters, arguments)
            || !bitvector_is_source_spelled(&end, parameters, arguments)
        {
            continue;
        }
        return Some(format!(
            "{}[{}..{}]",
            parameter.name(),
            describe_bitvector_with_context(&start, parameters, arguments),
            describe_bitvector_with_context(&end, parameters, arguments)
        ));
    }
    if range.base().offset != PointerOffsetTerm::Constant(0)
        || !bitvector_is_source_spelled(range.start(), parameters, arguments)
        || !bitvector_is_source_spelled(range.end(), parameters, arguments)
    {
        return None;
    }
    let declared = describe_memory_block(&range.base().block, parameters, arguments)?;
    Some(format!(
        "{declared}[{}..{}]",
        describe_bitvector_with_context(range.start(), parameters, arguments),
        describe_bitvector_with_context(range.end(), parameters, arguments)
    ))
}

/// True when every variable in this term has one of the caller's own names. A
/// kernel variable — a loop counter, a lowering temporary — has none, and a
/// term that mentions one is not shown to the reader at all: a repair written
/// over a name nobody wrote is not a repair.
fn bitvector_is_source_spelled(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> bool {
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::collect_bitvector_variables(term, &mut variables);
    variables.iter().all(|variable| {
        describe_parameter_bitvector(&Bitvector32Term::Variable(*variable), parameters, arguments)
            .is_some()
    })
}

/// The whole object a block names, spelled as the source declares it: a
/// parameter whose argument points into it, or a file-scope declaration.
fn describe_memory_block(
    block: &PointerBlock,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        if let CExpression::Value(CValue::Pointer(base)) = argument
            && &base.pointer().block == block
        {
            return Some(parameter.name().to_string());
        }
    }
    match block {
        // A block's spelling carries where the storage lives, which is the
        // verifier's business; the reader wrote only the name. `local:` covers
        // the re-declaration and call-frame forms too (`local:lifetime:2:q`,
        // `local:frame:3:__return`), whose last segment is that name.
        PointerBlock::Concrete(name) => Some(
            name.strip_prefix("global:")
                .or_else(|| {
                    name.rsplit(':')
                        .next()
                        .filter(|_| name.starts_with("static:") || name.starts_with("local:"))
                })
                .unwrap_or(name)
                .to_string(),
        ),
        // Every other block is a verifier-owned lowering artifact; naming it
        // would tell the reader nothing they wrote.
        _ => None,
    }
}

pub(super) fn describe_pointer(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    // Two parameters can point into one block, and then every one of them can
    // express the address -- `b[j]` is also `a[(b - a) + j]`. As in
    // [`describe_source_cell`], the shortest spelling is the one written
    // through the parameter the address actually belongs to, and picking it is
    // deterministic.
    let mut best: Option<String> = None;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(field) =
            describe_parameter_struct_field_pointer(pointer, parameter, base.pointer())
        {
            return field;
        }
        if let Some(index) = diagnostic_pointer_element_index_from_base(
            pointer,
            base,
            diagnostic_parameter_element_width(parameter),
        ) {
            let spelled = if index == Bitvector32Term::Constant(0) {
                parameter.name().to_string()
            } else {
                format!("{}[{}]", parameter.name(), describe_bitvector(&index))
            };
            if best.as_ref().is_none_or(|best| spelled.len() < best.len()) {
                best = Some(spelled);
            }
        }
    }
    if let Some(best) = best {
        return best;
    }
    match &pointer.block {
        // External argument blocks are verifier-owned lowering artifacts. Do
        // not expose their block names or offsets in user-facing diagnostics.
        PointerBlock::ExternalArgument => "the pointer value at this program point".to_string(),
        _ => format!(
            "{}@{}",
            pointer.block,
            describe_pointer_offset(&pointer.offset)
        ),
    }
}

/// Reconstructs the source spelling of a pointer loaded from a pointer-to-
/// struct parameter.  Field accesses are lowered to a memory load followed by
/// a pointer offset, so the kernel no longer carries the original `p->field`
/// AST node in the resource fact.  The parameter's parsed layout is the
/// source-level metadata needed to recover that spelling without printing the
/// lowered block, load, or version terms.
fn describe_parameter_struct_field_pointer(
    pointer: &Pointer,
    parameter: &syntax::C0Parameter,
    base: &Pointer,
) -> Option<String> {
    let layout = parameter
        .pointee_struct_layout()
        .or_else(|| parameter.struct_layout())?;
    let PointerOffsetTerm::Int32Scaled { value, byte_width } = &pointer.offset else {
        return None;
    };
    let loaded_at = match value.as_ref() {
        Bitvector32Term::MemoryLoad(_, loaded_at) => loaded_at.as_ref().clone(),
        Bitvector32Term::Variable(variable) => {
            crate::kernel::registered_load_for_variable(variable)?.1
        }
        _ => return None,
    };
    if pointer.block != base.block {
        return None;
    }
    layout.fields().iter().find_map(|(name, field)| {
        let field_type = field.c_type();
        let pointee_type = field_type.pointee_type()?;
        let pointee_width = diagnostic_c0_type_byte_width(pointee_type, field.byte_width());
        if pointee_width != *byte_width {
            return None;
        }
        let field_offset = diagnostic_pointer_element_index_from_base(&loaded_at, base, 1)?;
        (field_offset == Bitvector32Term::Constant(field.offset_bytes()))
            .then(|| format!("{}->{name}", parameter.name()))
    })
}

fn diagnostic_c0_type_byte_width(c_type: C0Type, pointer_width: u32) -> i64 {
    match c_type {
        C0Type::Bool | C0Type::Char | C0Type::UInt8 => 1,
        C0Type::Int8 => 1,
        C0Type::Int16 | C0Type::UInt16 => 2,
        C0Type::Int32 | C0Type::UInt32 => 4,
        C0Type::Int64 | C0Type::UInt64 => 8,
        _ if c_type.is_pointer() => i64::from(pointer_width),
        _ => i64::from(pointer_width),
    }
}

pub(super) fn diagnostic_parameter_element_width(parameter: &syntax::C0Parameter) -> i64 {
    match parameter.c_type() {
        C0Type::Void => 0,
        C0Type::Bool => 1,
        C0Type::VoidPointer | C0Type::VoidPointerPointer => 8,
        C0Type::CharPointer
        | C0Type::CharArray(_)
        | C0Type::UInt8Pointer
        | C0Type::UInt8Array(_) => 1,
        C0Type::Int8 | C0Type::Int8Array(_) => 1,
        C0Type::Int16 | C0Type::UInt16 | C0Type::Int16Array(_) | C0Type::UInt16Array(_) => 2,
        C0Type::Int32
        | C0Type::Char
        | C0Type::UInt8
        | C0Type::UInt32
        | C0Type::Int32Pointer
        | C0Type::UInt32Pointer
        | C0Type::Int32Array(_)
        | C0Type::UInt32Array(_) => 4,
        C0Type::Int64 | C0Type::UInt64 | C0Type::Int64Array(_) | C0Type::UInt64Array(_) => 8,
        C0Type::Float32 | C0Type::Float32Array(_) => 4,
        C0Type::Float64 | C0Type::Float64Array(_) => 8,
        C0Type::Int8Pointer | C0Type::Int8PointerPointer => 8,
        C0Type::Int16Pointer
        | C0Type::UInt16Pointer
        | C0Type::Int64Pointer
        | C0Type::UInt64Pointer
        | C0Type::Int16PointerPointer
        | C0Type::UInt16PointerPointer
        | C0Type::Int32PointerPointer
        | C0Type::CharPointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::UInt32PointerPointer
        | C0Type::Int64PointerPointer
        | C0Type::UInt64PointerPointer
        | C0Type::Float32Pointer
        | C0Type::Float64Pointer
        | C0Type::Float32PointerPointer
        | C0Type::Float64PointerPointer => 8,
        C0Type::FunctionPointer(_) => 8,
        C0Type::PointerArray(_, _) => 8,
    }
}

pub(super) fn diagnostic_pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: i64,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width),
                diagnostic_element_index_from_pointer_offset(&base.offset, byte_width),
            ) {
                Some(bitvector32_subtract(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

pub(super) fn diagnostic_element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
    byte_width: i64,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % byte_width == 0 => {
            let index = offset / byte_width;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: actual_width,
        } if *actual_width == byte_width => Some(value.as_ref().clone()),
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            diagnostic_element_index_from_pointer_offset(left, byte_width)?,
            diagnostic_element_index_from_pointer_offset(right, byte_width)?,
        )),
        _ => None,
    }
}

pub(super) fn describe_c_value(
    value: &CValue,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match value {
        CValue::Void => "void".to_string(),
        CValue::Bool(value) => format!(
            "{}bool",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::Int8(value) => {
            format!(
                "{}i8",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::Int16(value) => {
            format!(
                "{}i16",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::Int32(value) => describe_bitvector_with_context(value, parameters, arguments),
        CValue::UInt8(value) => {
            format!(
                "{}u8",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::UInt32(value) => {
            format!(
                "{}u32",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::UInt16(value) => {
            format!(
                "{}u16",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        // A 64-bit constant already carries its suffix.
        CValue::Int64(value) => {
            let inner = describe_bitvector_with_context(value, parameters, arguments);
            if inner.ends_with("i64") {
                inner
            } else {
                format!("{inner}i64")
            }
        }
        CValue::UInt64(value) => {
            let inner = describe_bitvector_with_context(value, parameters, arguments);
            if inner.ends_with("u64") {
                inner
            } else {
                format!("{inner}u64")
            }
        }
        CValue::Float32(value) => format!(
            "{}f32",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::Float64(value) => format!(
            "{}f64",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::Pointer(pointer) => describe_pointer(pointer, parameters, arguments),
    }
}

pub(super) fn describe_contract_segment(segment: &ContractSegment) -> String {
    let base = describe_c_expression(&segment.base);
    let current = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => {
            let rendered_base = describe_contract_expression(base);
            format!(
                "{rendered_base}[{}..{}]",
                describe_contract_expression(start),
                describe_contract_expression(end)
            )
        }
        ContractSegmentSurface::Field {
            address,
            base: surface_base,
            name,
            ..
        } => match surface_base {
            Some(surface_base) => {
                format!(
                    "{}{}->{name}",
                    if *address { "&" } else { "" },
                    describe_contract_expression(surface_base)
                )
            }
            None => format!("{}{base}->{name}", if *address { "&" } else { "" }),
        },
        ContractSegmentSurface::Object(_) => format!("object({base})"),
    };
    match segment.state {
        ContractSegmentState::Current => current,
        ContractSegmentState::Old => format!("old({current})"),
    }
}

pub(super) fn describe_c_expression(expression: &CExpression) -> String {
    match expression {
        CExpression::Value(value) => describe_c_value(value, &[], &[]),
        CExpression::Variable(name) => name.clone(),
        CExpression::FunctionAddress(name) => format!("&{name}"),
        CExpression::Cast {
            expression,
            target_type,
            pointee_struct,
            ..
        } => {
            if let Some(struct_name) = pointee_struct {
                return format!(
                    "((struct {struct_name} *){})",
                    describe_c_expression(expression)
                );
            }
            let spelling = match target_type {
                CType::Int8 => "int8".to_string(),
                CType::Int16 => "int16".to_string(),
                CType::Int32 => "int32".to_string(),
                CType::UInt8 => "uint8".to_string(),
                CType::UInt16 => "uint16".to_string(),
                CType::UInt32 => "uint32".to_string(),
                CType::Int64 => "int64".to_string(),
                CType::UInt64 => "uint64".to_string(),
                _ => format!("{target_type:?}"),
            };
            // Contract expressions use the `(type) expression` cast syntax.
            // Wrap the complete cast so it remains a single term when it is
            // embedded in a generated comparison or another proposition.
            format!("(({spelling}){})", describe_c_expression(expression))
        }
        CExpression::FloatNegate(expression) => format!("-{}", describe_c_expression(expression)),
        CExpression::FloatClassification {
            expression,
            classification,
        } => format!(
            "is{classification:?}({})",
            describe_c_expression(expression)
        ),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => format!(
            "{} ? {} : {}",
            describe_c_expression(condition),
            describe_c_expression(then_branch),
            describe_c_expression(else_branch)
        ),
        CExpression::AddressOf(target) => format!("&{}", describe_c_expression(target)),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            format!("byte_offset({}, {bytes})", describe_c_expression(pointer))
        }
        CExpression::LessThan(left, right) => describe_binary_c_expression(left, "<", right),
        CExpression::LessEqual(left, right) => describe_binary_c_expression(left, "<=", right),
        CExpression::GreaterThan(left, right) => describe_binary_c_expression(left, ">", right),
        CExpression::GreaterEqual(left, right) => describe_binary_c_expression(left, ">=", right),
        CExpression::Equal(left, right) => describe_binary_c_expression(left, "==", right),
        CExpression::NotEqual(left, right) => describe_binary_c_expression(left, "!=", right),
        CExpression::Not(expression) => format!("!{}", describe_c_expression(expression)),
        CExpression::And(left, right) => describe_binary_c_expression(left, "&&", right),
        CExpression::Or(left, right) => describe_binary_c_expression(left, "||", right),
        CExpression::Add(left, right) => describe_binary_c_expression(left, "+", right),
        CExpression::Subtract(left, right) => describe_binary_c_expression(left, "-", right),
        CExpression::Multiply(left, right) => describe_binary_c_expression(left, "*", right),
        CExpression::Divide(left, right) => describe_binary_c_expression(left, "/", right),
        CExpression::Remainder(left, right) => describe_binary_c_expression(left, "%", right),
        CExpression::ShiftLeft(left, right) => describe_binary_c_expression(left, "<<", right),
        CExpression::ShiftRight(left, right) => describe_binary_c_expression(left, ">>", right),
        CExpression::BitwiseAnd(left, right) => describe_binary_c_expression(left, "&", right),
        CExpression::BitwiseOr(left, right) => describe_binary_c_expression(left, "|", right),
        CExpression::BitwiseXor(left, right) => describe_binary_c_expression(left, "^", right),
        CExpression::BitwiseNot(expression) => format!("~{}", describe_c_expression(expression)),
        CExpression::Load(pointer) => format!("*{}", describe_c_expression(pointer)),
        CExpression::TypedLoad {
            pointer,
            value_type,
            ..
        } => {
            let name = match value_type {
                CType::Void => "load_void",
                CType::Bool => "load_bool",
                CType::VoidPointer => "load_void_pointer",
                CType::VoidPointerPointer => "load_void_pointer_pointer",
                CType::Int8 => "load_int8",
                CType::Int16 => "load_int16",
                CType::Int32 => "load_int32",
                CType::UInt8 => "load_uint8",
                CType::UInt16 => "load_uint16",
                CType::UInt32 => "load_uint32",
                CType::Int64 => "load_int64",
                CType::UInt64 => "load_uint64",
                CType::Float32 => "load_float",
                CType::Float64 => "load_double",
                CType::Int8Pointer => "load_int8_pointer",
                CType::Int16Pointer => "load_int16_pointer",
                CType::UInt16Pointer => "load_uint16_pointer",
                CType::Int32Pointer => "load_int32_pointer",
                CType::UInt8Pointer => "load_uint8_pointer",
                CType::UInt32Pointer => "load_uint32_pointer",
                CType::Int64Pointer => "load_int64_pointer",
                CType::UInt64Pointer => "load_uint64_pointer",
                CType::Int8PointerPointer => "load_int8_pointer_pointer",
                CType::Int16PointerPointer => "load_int16_pointer_pointer",
                CType::UInt16PointerPointer => "load_uint16_pointer_pointer",
                CType::Int32PointerPointer => "load_int32_pointer_pointer",
                CType::UInt8PointerPointer => "load_uint8_pointer_pointer",
                CType::UInt32PointerPointer => "load_uint32_pointer_pointer",
                CType::Int64PointerPointer => "load_int64_pointer_pointer",
                CType::UInt64PointerPointer => "load_uint64_pointer_pointer",
                CType::Float32Pointer => "load_float_pointer",
                CType::Float64Pointer => "load_double_pointer",
                CType::Float32PointerPointer => "load_float_pointer_pointer",
                CType::Float64PointerPointer => "load_double_pointer_pointer",
                CType::FunctionPointer(_) => "load_function_pointer",
                CType::Int8Array(_) => {
                    return format!("*{}", describe_c_expression(pointer));
                }
                CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int64Array(_)
                | CType::UInt64Array(_)
                | CType::Float32Array(_)
                | CType::Float64Array(_) => {
                    return format!("*{}", describe_c_expression(pointer));
                }
                CType::PointerArray(_, _) => {
                    return format!("*{}", describe_c_expression(pointer));
                }
            };
            format!("{name}({})", describe_c_expression(pointer))
        }
        CExpression::Index(base, index) => {
            format!(
                "{}[{}]",
                describe_c_expression(base),
                describe_c_expression(index)
            )
        }
    }
}

pub(super) fn describe_binary_c_expression(
    left: &CExpression,
    operator: &str,
    right: &CExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_c_expression(left),
        describe_c_expression(right)
    )
}

/// How much of one statement's own C spelling a diagnostic may carry.
const MAX_STATEMENT_HEAD_BYTES: usize = 512;

/// Names a statement the way its C reads, without its body.
///
/// `Debug` on a statement is an implementation dump: a `While` node carries
/// its whole body, every lowered invariant and effect check, every resource
/// spec, and the snapshots inside them, so its size has no relation to what
/// the reader of a refusal needs. What a refusal needs is which statement the
/// cursor is on, and for a loop or a branch, the guard that produced the
/// successors it is complaining about.
pub(super) fn describe_c_statement_head(statement: &CStatement) -> String {
    let head = match statement {
        CStatement::Skip => ";".to_string(),
        CStatement::Break => "break;".to_string(),
        CStatement::Continue => "continue;".to_string(),
        CStatement::Goto { target } => format!("goto target({});", target.0),
        CStatement::ForStep {
            step,
            continue_after,
            ..
        } => {
            if *continue_after {
                format!("continue; (with {})", describe_c_statement_head(step))
            } else {
                describe_c_statement_head(step)
            }
        }
        CStatement::Declare { name, .. } => format!("declaration of `{name}`"),
        CStatement::DeclareAggregate { name, .. } => format!("aggregate declaration of `{name}`"),
        CStatement::CopyAggregate { target, source, .. } => format!(
            "{} = {};",
            describe_c_expression(target),
            describe_c_expression(source)
        ),
        CStatement::Assign { name, expression } => {
            format!("{name} = {};", describe_c_expression(expression))
        }
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => format!(
            "{target} = {function_name}({});",
            describe_c_expression_list(arguments)
        ),
        CStatement::Call {
            function_name,
            arguments,
        } => format!(
            "{function_name}({});",
            describe_c_expression_list(arguments)
        ),
        CStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
        } => format!(
            "{target} = {}({});",
            if *zeroed { "calloc" } else { "malloc" },
            describe_c_expression(bytes)
        ),
        CStatement::HeapFree { pointer } => {
            format!("free({});", describe_c_expression(pointer))
        }
        CStatement::Assert { condition, label } => format!(
            "assert{}({});",
            label
                .as_ref()
                .map(|label| format!(" {label}"))
                .unwrap_or_default(),
            describe_c_expression(condition)
        ),
        CStatement::Seq(first, _) => describe_c_statement_head(first),
        CStatement::Return(expression) => {
            format!("return {};", describe_c_expression(expression))
        }
        CStatement::Throw(expression) => {
            format!("throw {};", describe_c_expression(expression))
        }
        CStatement::TryCatchInt32 { binding, .. } => {
            format!("try ... catch (int {binding})")
        }
        CStatement::Store { pointer, value } => format!(
            "*{} = {};",
            describe_c_expression(pointer),
            describe_c_expression(value)
        ),
        CStatement::TypedStore { pointer, value, .. } => format!(
            "*{} = {};",
            describe_c_expression(pointer),
            describe_c_expression(value)
        ),
        CStatement::Update {
            target,
            operator,
            operand,
        } => format!(
            "{} {}= {};",
            describe_c_expression(target),
            describe_c_update_operator(*operator),
            describe_c_expression(operand)
        ),
        CStatement::If { condition, .. } => {
            format!("if ({})", describe_c_guard(condition))
        }
        CStatement::While {
            condition,
            do_while,
            ..
        } => {
            if *do_while {
                format!("do ... while ({})", describe_c_guard(condition))
            } else {
                format!("while ({})", describe_c_guard(condition))
            }
        }
        CStatement::Switch { expression, .. } => {
            format!("switch ({})", describe_c_guard(expression))
        }
    };
    truncate_utf8_with_suffix(&head, MAX_STATEMENT_HEAD_BYTES, "…")
}

/// A guard already sits inside the parentheses the statement writes, so drop
/// the outermost pair the expression printer adds around a binary operator.
fn describe_c_guard(condition: &CExpression) -> String {
    let rendered = describe_c_expression(condition);
    let Some(inner) = rendered
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return rendered;
    };
    // Only strip a pair that really encloses the whole expression: `(a) + (b)`
    // starts and ends with a parenthesis without being parenthesized.
    let mut depth = 0usize;
    for character in inner.chars() {
        match character {
            '(' => depth += 1,
            ')' => match depth.checked_sub(1) {
                Some(next) => depth = next,
                None => return rendered,
            },
            _ => {}
        }
    }
    if depth == 0 {
        inner.to_string()
    } else {
        rendered
    }
}

fn describe_c_expression_list(expressions: &[CExpression]) -> String {
    expressions
        .iter()
        .map(describe_c_expression)
        .collect::<Vec<_>>()
        .join(", ")
}

fn describe_c_update_operator(operator: CUpdateOperator) -> &'static str {
    match operator {
        CUpdateOperator::Add => "+",
        CUpdateOperator::Subtract => "-",
        CUpdateOperator::Multiply => "*",
        CUpdateOperator::Divide => "/",
        CUpdateOperator::Remainder => "%",
        CUpdateOperator::ShiftLeft => "<<",
        CUpdateOperator::ShiftRight => ">>",
        CUpdateOperator::BitwiseAnd => "&",
        CUpdateOperator::BitwiseOr => "|",
        CUpdateOperator::BitwiseXor => "^",
    }
}

pub(super) fn describe_contract_expression(expression: &ContractExpression) -> String {
    if matches!(expression, ContractExpression::Add(_, _)) {
        return describe_add_contract_expression(expression);
    }
    match expression {
        ContractExpression::IntegerLiteral(value) => value.clone(),
        ContractExpression::ResourceField(access) => {
            let mut parts = vec![access.owner.as_str()];
            parts.extend(access.children.iter().map(String::as_str));
            parts.push(access.field.as_str());
            parts.join(".")
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => {
            let type_arguments = if algebraic_type.arguments.is_empty() {
                String::new()
            } else {
                format!(
                    "<{}>",
                    algebraic_type
                        .arguments
                        .iter()
                        .map(describe_click_type)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            format!(
                "{}{type_arguments}::{variant}({})",
                algebraic_type.name,
                arguments
                    .iter()
                    .map(describe_contract_expression)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        ContractExpression::AlgebraicVariable { name, .. } | ContractExpression::Binding(name) => {
            name.clone()
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => format!(
            "match {} {{ {} }}",
            describe_contract_expression(scrutinee),
            arms.iter()
                .map(|arm| format!(
                    "{}::{}({}) => {}",
                    arm.type_name,
                    arm.variant,
                    arm.bindings.join(", "),
                    describe_contract_expression(&arm.body)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ContractExpression::SequenceLiteral(elements) => format!(
            "[{}]",
            elements
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ContractExpression::SequenceConcat(left, right) => {
            describe_binary_contract_expression(left, "++", right)
        }
        ContractExpression::QualifiedC { name, .. } => name.clone(),
        ContractExpression::CFragment(expression) => describe_c_expression(expression),
        ContractExpression::Field { base, field, .. } => {
            format!("{}->{field}", describe_contract_expression(base))
        }
        ContractExpression::CBinding(name) => format!("c({name})"),
        ContractExpression::ResourceWildcard => "_".to_string(),
        ContractExpression::ResourceCount(resource) => {
            // Population patterns name the resource, not the permission of
            // the observation that supplied it. `count(view r(...))` is not
            // syntax, and count lowering ignores that access annotation.
            match resource.as_ref() {
                ResourceClause::Declared {
                    name, arguments, ..
                } => format!(
                    "count({name}({}))",
                    arguments
                        .iter()
                        .map(describe_contract_expression)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                _ => format!("count({})", describe_resource_clause(resource)),
            }
        }
        ContractExpression::Old(expression) => {
            format!("old({})", describe_contract_expression(expression))
        }
        ContractExpression::At {
            selector,
            expression,
        } => format!(
            "at({}, {})",
            describe_snapshot_selector(selector),
            describe_contract_expression(expression)
        ),
        ContractExpression::Negate(expression) => {
            format!("-{}", describe_contract_expression(expression))
        }
        ContractExpression::Add(_, _) => unreachable!("addition is rendered iteratively above"),
        ContractExpression::Subtract(left, right) => {
            describe_binary_contract_expression(left, "-", right)
        }
        ContractExpression::Multiply(left, right) => {
            describe_binary_contract_expression(left, "*", right)
        }
        ContractExpression::Divide(left, right) => {
            describe_binary_contract_expression(left, "/", right)
        }
        ContractExpression::Remainder(left, right) => {
            describe_binary_contract_expression(left, "%", right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            describe_binary_contract_expression(left, "<<", right)
        }
        ContractExpression::ShiftRight(left, right) => {
            describe_binary_contract_expression(left, ">>", right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            describe_binary_contract_expression(left, "&", right)
        }
        ContractExpression::BitwiseOr(left, right) => {
            describe_binary_contract_expression(left, "|", right)
        }
        ContractExpression::BitwiseXor(left, right) => {
            describe_binary_contract_expression(left, "^", right)
        }
        ContractExpression::BitwiseNot(expression) => {
            format!("~{}", describe_contract_expression(expression))
        }
        // Qualified C array indices have already been flattened by the
        // parser. Offset the decayed pointer explicitly so reparsing does
        // not interpret this as an incomplete multidimensional subscript.
        ContractExpression::Index(base, index)
            if matches!(base.as_ref(), ContractExpression::QualifiedC { .. }) =>
        {
            format!(
                "({} + {})[0]",
                describe_contract_expression(base),
                describe_contract_expression(index)
            )
        }
        ContractExpression::Index(base, index) => format!(
            "{}[{}]",
            describe_contract_expression(base),
            describe_contract_expression(index)
        ),
        ContractExpression::ArrayIndex { base, indexes, .. } => format!(
            "{}{}",
            describe_contract_expression(base),
            indexes
                .iter()
                .map(|index| format!("[{}]", describe_c_expression(index)))
                .collect::<String>()
        ),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => format!(
            // This describer also prints expanded proof text, so a
            // conditional must come back as the syntax that wrote it. The
            // parentheses are what let the result sit where a term is
            // expected, as in `result == (if c { a } else { b })`.
            "(if {} {{ {} }} else {{ {} }})",
            describe_click_proposition(condition),
            describe_contract_expression(then_branch),
            describe_contract_expression(else_branch)
        ),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => format!(
            "({}..{}).fold({}, |{accumulator}, {item}| {{ {} }})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_contract_expression(initial),
            describe_contract_expression(body)
        ),
        ContractExpression::Let {
            click_type: Some(ClickType::Integer),
            ..
        } => {
            // Retain the type when printing checked evidence and flatten a
            // chain of lexical aliases into one parenthesized expression.
            let mut output = String::from("(");
            let mut body = expression;
            while let ContractExpression::Let {
                name,
                click_type: Some(ClickType::Integer),
                value,
                body: next,
            } = body
            {
                output.push_str(&format!(
                    "let {name}: Integer = {}; ",
                    describe_let_value(value)
                ));
                body = next;
            }
            output.push_str(&describe_let_value(body));
            output.push(')');
            output
        }
        ContractExpression::Let {
            name, value, body, ..
        } => format!(
            "(let {name} = {}; {})",
            describe_let_value(value),
            describe_let_value(body)
        ),
        ContractExpression::Call { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn describe_add_contract_expression(expression: &ContractExpression) -> String {
    enum Frame<'a> {
        Visit(&'a ContractExpression),
        Build,
    }

    let mut frames = vec![Frame::Visit(expression)];
    let mut rendered = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Visit(ContractExpression::Add(left, right)) => {
                frames.push(Frame::Build);
                frames.push(Frame::Visit(right));
                frames.push(Frame::Visit(left));
            }
            Frame::Visit(expression) => rendered.push(describe_contract_expression(expression)),
            Frame::Build => {
                let right = rendered.pop().expect("rendered addition right operand");
                let left = rendered.pop().expect("rendered addition left operand");
                rendered.push(format!("({left} + {right})"));
            }
        }
    }
    rendered.pop().expect("rendered addition expression")
}

/// Keep generated let bindings source-printable for long left-associated
/// addition chains. The binding value is a top-level expression, so flattening
/// only `+` nodes preserves precedence while avoiding artificial nesting.
fn describe_let_value(value: &ContractExpression) -> String {
    if !matches!(value, ContractExpression::Add(_, _)) {
        return describe_contract_expression(value);
    }
    let mut pending = vec![value];
    let mut terms = Vec::new();
    while let Some(expression) = pending.pop() {
        match expression {
            ContractExpression::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            expression => terms.push(describe_contract_expression(expression)),
        }
    }
    terms.join(" + ")
}

pub(super) fn describe_binary_contract_expression(
    left: &ContractExpression,
    operator: &str,
    right: &ContractExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_contract_expression(left),
        describe_contract_expression(right)
    )
}

/// The `aligned(p, n)` sugar behind `address(p) & (n - 1) == 0`, so a
/// generated or expanded alignment fact renders in its source spelling.
fn aligned_sugar(proposition: &ClickProposition) -> Option<(&CExpression, u64)> {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = proposition
    else {
        return None;
    };
    aligned_comparison_sugar(left, right)
}

/// The same sugar for an alignment fact read at one snapshot, whose sides
/// are each qualified `at(S, address(p) & (n - 1)) == at(S, 0u64)`, as a
/// function-entry alignment fact is when it is cited after execution. It
/// renders as `at(S, aligned(p, n))`. The pointer-to-`uint64` conversion
/// inside has no cast spelling in Click (only `address(p)` or `aligned`),
/// so rendering the qualified sides expression by expression would emit an
/// unparseable `(uint64)p`.
fn snapshot_aligned_sugar(
    proposition: &ClickProposition,
) -> Option<(&SnapshotSelector, &CExpression, u64)> {
    let ClickProposition::Comparison {
        left: ContractExpression::At {
            selector,
            expression: left,
        },
        operator: ComparisonOperator::Equal,
        right,
    } = proposition
    else {
        return None;
    };
    let right = match right {
        ContractExpression::At {
            selector: right_selector,
            expression,
        } if right_selector == selector => expression.as_ref(),
        ContractExpression::At { .. } => return None,
        right => right,
    };
    let (pointer, alignment) = aligned_comparison_sugar(left, right)?;
    Some((selector, pointer, alignment))
}

fn aligned_comparison_sugar<'a>(
    left: &'a ContractExpression,
    right: &ContractExpression,
) -> Option<(&'a CExpression, u64)> {
    let ContractExpression::BitwiseAnd(address, mask) = left else {
        return None;
    };
    let ContractExpression::CFragment(CExpression::Value(CValue::UInt64(zero))) = right else {
        return None;
    };
    if zero.uint64_as_const() != Some(0) {
        return None;
    }
    let ContractExpression::CFragment(CExpression::Cast {
        expression: pointer,
        target_type: CType::UInt64,
        ..
    }) = address.as_ref()
    else {
        return None;
    };
    let ContractExpression::CFragment(CExpression::Value(CValue::UInt64(mask))) = mask.as_ref()
    else {
        return None;
    };
    let alignment = mask.uint64_as_const()?.checked_add(1)?;
    alignment
        .is_power_of_two()
        .then_some((pointer.as_ref(), alignment))
}

pub(super) fn describe_click_proposition(proposition: &ClickProposition) -> String {
    if let Some((pointer, alignment)) = aligned_sugar(proposition) {
        return format!("aligned({}, {alignment})", describe_c_expression(pointer));
    }
    if let Some((selector, pointer, alignment)) = snapshot_aligned_sugar(proposition) {
        return format!(
            "at({}, aligned({}, {alignment}))",
            describe_snapshot_selector(selector),
            describe_c_expression(pointer)
        );
    }
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => format!(
            "{} {operator} {}",
            describe_contract_expression(left),
            describe_contract_expression(right)
        ),
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => format!(
            "{}({})",
            match classification {
                syntax::C0FloatClassification::Finite => "isfinite",
                syntax::C0FloatClassification::Infinite => "isinf",
                syntax::C0FloatClassification::Zero => "iszero",
                syntax::C0FloatClassification::Subnormal => "issubnormal",
                syntax::C0FloatClassification::Nan => "isnan",
            },
            describe_contract_expression(expression)
        ),
        ClickProposition::Separate { left, right } => format!(
            "separate({}, {})",
            describe_resource_subject(left),
            describe_resource_subject(right)
        ),
        ClickProposition::Contains { parent, child } => format!(
            "contains({}, {})",
            describe_resource_subject(parent),
            describe_resource_subject(child)
        ),
        ClickProposition::Loadable { segment } => {
            format!("viewable({})", describe_contract_segment(segment))
        }
        ClickProposition::Defined { expression } => {
            format!("defined({})", describe_contract_expression(expression))
        }
        ClickProposition::At {
            selector,
            proposition,
        } => format!(
            "at({}, {})",
            describe_snapshot_selector(selector),
            describe_click_proposition(proposition)
        ),
        ClickProposition::And(left, right) => describe_binary_click_proposition(left, "&&", right),
        ClickProposition::Or(left, right) => describe_binary_click_proposition(left, "||", right),
        ClickProposition::Not(proposition) => {
            format!("!{}", describe_click_proposition(proposition))
        }
        ClickProposition::Implies(left, right) => {
            describe_binary_click_proposition(left, "=>", right)
        }
        ClickProposition::ForAll {
            click_type,
            name,
            body,
            ..
        } => format!(
            "forall ({name}: {}) {{ {} }}",
            describe_click_type(click_type),
            describe_click_proposition(body)
        ),
        ClickProposition::Exists {
            click_type,
            name,
            body,
            ..
        } => format!(
            "exists ({name}: {}) {{ {} }}",
            describe_click_type(click_type),
            describe_click_proposition(body)
        ),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        } => format!(
            "({}..{}).all({item} => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_click_proposition(body)
        ),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
            ..
        } => format!(
            "({}..{}).any({item} => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_click_proposition(body)
        ),
        ClickProposition::PredicateCall { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub(super) fn describe_binary_click_proposition(
    left: &ClickProposition,
    operator: &str,
    right: &ClickProposition,
) -> String {
    format!(
        "({} {operator} {})",
        describe_click_proposition(left),
        describe_click_proposition(right)
    )
}

pub(super) fn describe_snapshot_selector(selector: &SnapshotSelector) -> String {
    match selector {
        SnapshotSelector::ProgramPoint(point) => describe_program_point_ref(point),
        SnapshotSelector::Mark(name) => name.clone(),
    }
}

pub(super) fn describe_program_point_ref(point: &ProgramPointRef) -> String {
    let kind = match point.kind {
        ProgramPointKind::Entry => "entry",
        ProgramPointKind::Exit => "exit",
    };
    format!("{}.{}", describe_code_region_ref(&point.region), kind)
}

pub(super) fn describe_code_region_ref(region: &CodeRegionRef) -> String {
    match region {
        CodeRegionRef::Function => "function".to_string(),
        CodeRegionRef::Loop(index) => format!("loop({index})"),
        CodeRegionRef::Statement(index) => format!("statement({index})"),
        CodeRegionRef::Label(name) => name.clone(),
    }
}

pub(super) fn describe_bitvector(term: &Bitvector32Term) -> String {
    describe_bitvector_with_context(term, &[], &[])
}

pub(super) fn describe_bitvector_with_context(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return name;
    }
    match term {
        Bitvector32Term::Constant(value) => format!("{}", *value as i32),
        Bitvector32Term::Int64Constant(value) => format!("{value}i64"),
        Bitvector32Term::UInt64Constant(value) => format!("{value}u64"),
        // A diagnostic prints the load represented by a load variable,
        // never the kernel variable's id.
        Bitvector32Term::Variable(variable)
            if crate::kernel::is_load_variable(variable)
                && crate::kernel::registered_load_for_variable(variable).is_some() =>
        {
            let (_, pointer) = crate::kernel::registered_load_for_variable(variable)
                .expect("checked registered above");
            format!(
                "load({})",
                describe_pointer(&pointer, parameters, arguments)
            )
        }
        // And a model-field variable prints as the field it is. The value is
        // stored inside the instance fact, so there is nothing in the term to
        // recover it from; the mint registered it.
        Bitvector32Term::Variable(variable)
            if crate::kernel::model_fields::model_field_spelling(*variable).is_some() =>
        {
            crate::kernel::model_fields::model_field_spelling(*variable)
                .expect("checked registered above")
        }
        Bitvector32Term::Variable(variable) => format!("v{}", variable.0),
        Bitvector32Term::Add(left, right) => {
            describe_binary_bitvector_with_context(left, "+", right, parameters, arguments)
        }
        Bitvector32Term::Subtract(left, right) => {
            describe_binary_bitvector_with_context(left, "-", right, parameters, arguments)
        }
        Bitvector32Term::Multiply(left, right) => {
            describe_binary_bitvector_with_context(left, "*", right, parameters, arguments)
        }
        Bitvector32Term::Divide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::Remainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            describe_binary_bitvector_with_context(left, "<<", right, parameters, arguments)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            describe_binary_bitvector_with_context(left, "&", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            describe_binary_bitvector_with_context(left, "|", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            describe_binary_bitvector_with_context(left, "^", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseNot(value) => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::Float32Negate(value) | Bitvector32Term::Float64Negate(value) => {
            format!(
                "-{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        }
        | Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => {
            let symbol = match operator {
                CFloatBinaryOperator::Add => "+",
                CFloatBinaryOperator::Subtract => "-",
                CFloatBinaryOperator::Multiply => "*",
                CFloatBinaryOperator::Divide => "/",
            };
            describe_binary_bitvector_with_context(left, symbol, right, parameters, arguments)
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value) => format!(
            "cast64({})",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        Bitvector32Term::UInt32From64(value) => format!(
            "truncate32({})",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        Bitvector32Term::Int64Add(left, right) | Bitvector32Term::UInt64Add(left, right) => {
            describe_binary_bitvector_with_context(left, "+", right, parameters, arguments)
        }
        Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::UInt64Subtract(left, right) => {
            describe_binary_bitvector_with_context(left, "-", right, parameters, arguments)
        }
        Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::UInt64Multiply(left, right) => {
            describe_binary_bitvector_with_context(left, "*", right, parameters, arguments)
        }
        Bitvector32Term::Int64Divide(left, right) | Bitvector32Term::UInt64Divide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::UInt64Remainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right) => {
            describe_binary_bitvector_with_context(left, "<<", right, parameters, arguments)
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            describe_binary_bitvector_with_context(left, "&", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right) => {
            describe_binary_bitvector_with_context(left, "|", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            describe_binary_bitvector_with_context(left, "^", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseNot(value) | Bitvector32Term::UInt64BitwiseNot(value) => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => format!(
            "if {} then {} else {}",
            describe_condition(condition),
            describe_bitvector_with_context(then_term, parameters, arguments),
            describe_bitvector_with_context(else_term, parameters, arguments)
        ),
        // A fold body is an arbitrary term over its own binders, so it has no
        // shorter source spelling; render it through the bounded proposition
        // printer rather than dumping the developer structure.
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => format!(
            "fold({}..{}, init={}, acc=v{}, item=v{}, body={})",
            describe_bitvector_with_context(start, parameters, arguments),
            describe_bitvector_with_context(end, parameters, arguments),
            describe_bitvector_with_context(initial, parameters, arguments),
            accumulator.0,
            item.0,
            describe_bitvector_with_context(body, parameters, arguments)
        ),
        Bitvector32Term::PureFunctionApplication {
            name,
            arguments: values,
        } => format!(
            "{}({})",
            name,
            values
                .iter()
                .map(|argument| {
                    describe_bitvector_with_context(argument, parameters, arguments)
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Bitvector32Term::ClickFunctionApplication { name, .. } => {
            format!("{name}(<typed Click arguments>)")
        }
        Bitvector32Term::AlgebraicMatch { .. } => "match <algebraic value> { ... }".to_string(),
        Bitvector32Term::MemoryLoad(_, pointer) => {
            format!("load({})", describe_pointer(pointer, parameters, arguments))
        }
        Bitvector32Term::PointerAddress(pointer) => {
            format!(
                "address({})",
                describe_pointer(pointer, parameters, arguments)
            )
        }
        Bitvector32Term::IntegerToMachine { .. } => "integer-to-machine".to_string(),
    }
}

pub(super) fn describe_parameter_bitvector(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        match argument {
            CExpression::Value(CValue::Int32(value))
                if value == term && parameter.c_type() == C0Type::Int32 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt8(value))
                if value == term && matches!(parameter.c_type(), C0Type::Char | C0Type::UInt8) =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::Int8(value))
                if value == term && parameter.c_type() == C0Type::Int8 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::Int16(value))
                if value == term && parameter.c_type() == C0Type::Int16 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt16(value))
                if value == term && parameter.c_type() == C0Type::UInt16 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt32(value))
                if value == term && parameter.c_type() == C0Type::UInt32 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::Int64(value))
                if value == term && parameter.c_type() == C0Type::Int64 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt64(value))
                if value == term && parameter.c_type() == C0Type::UInt64 =>
            {
                return Some(parameter.name().to_string());
            }
            _ => {}
        }
    }
    None
}

pub(super) fn describe_binary_bitvector_with_context(
    left: &Bitvector32Term,
    operator: &str,
    right: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    format!(
        "({} {operator} {})",
        describe_bitvector_with_context(left, parameters, arguments),
        describe_bitvector_with_context(right, parameters, arguments)
    )
}

pub(super) fn describe_pointer_offset(offset: &PointerOffsetTerm) -> String {
    match offset {
        PointerOffsetTerm::Constant(value) => value.to_string(),
        PointerOffsetTerm::Variable(variable) => format!("off{}", variable.0),
        PointerOffsetTerm::Add(left, right) => format!(
            "({} + {})",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            format!("{} * {byte_width}", describe_bitvector(value))
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let signedness = if *unsigned { "uint64" } else { "int64" };
            format!("{signedness}({}) * {byte_width}", describe_bitvector(value))
        }
    }
}

/// Renders an exact-arithmetic comparison through the bounded term printer.
///
/// An `IntegerTerm` can carry a pure-function application or an algebraic
/// elimination, so its `Debug` reaches the whole instantiated datatype schema
/// graph the way a proposition's does.
fn describe_integer_comparison(
    left: &crate::kernel::SharedIntegerTerm,
    operator: &str,
    right: &crate::kernel::SharedIntegerTerm,
) -> String {
    format!(
        "{} {operator} {}",
        describe_integer_term(left),
        describe_integer_term(right)
    )
}

fn describe_integer_term(term: &crate::kernel::IntegerTerm) -> String {
    crate::surface::proof_diagnostics::render::render_integer_term(term)
}

pub(super) fn describe_condition(condition: &ConditionTerm) -> String {
    match condition {
        ConditionTerm::AlgebraicEqual(_, _) => "algebraic equality".to_string(),
        ConditionTerm::IntegerLessThan(left, right) => {
            describe_integer_comparison(left, "<", right)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            describe_integer_comparison(left, "<=", right)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            describe_integer_comparison(left, ">", right)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            describe_integer_comparison(left, ">=", right)
        }
        ConditionTerm::IntegerEqual(left, right) => describe_integer_comparison(left, "==", right),
        ConditionTerm::IntegerNotEqual(left, right) => {
            describe_integer_comparison(left, "!=", right)
        }
        ConditionTerm::Constant(value) => value.to_string(),
        ConditionTerm::Variable(variable) => format!("cond{}", variable.0),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            describe_binary_condition(left, "<", right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            describe_binary_condition(left, "<=", right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            describe_binary_condition(left, ">", right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            describe_binary_condition(left, ">=", right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            describe_binary_condition(left, "==", right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            format!(
                "overflow({} + {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            format!(
                "overflow({} - {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            format!(
                "overflow({} * {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            format!(
                "overflow({} / {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            format!(
                "overflow({} << {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
            describe_binary_condition(left, "<", right)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            describe_binary_condition(left, "<=", right)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            describe_binary_condition(left, ">", right)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            describe_binary_condition(left, ">=", right)
        }
        ConditionTerm::Bitvector64Equal(left, right) => {
            describe_binary_condition(left, "==", right)
        }
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            format!(
                "overflow({} + {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            format!(
                "overflow({} - {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            format!(
                "overflow({} * {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            format!(
                "overflow({} / {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            format!(
                "overflow({} << {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Float32(float_condition) => describe_float_condition(float_condition),
        ConditionTerm::Float64(float_condition) => describe_float_condition(float_condition),
        ConditionTerm::PointerOffsetEqual(left, right) => format!(
            "{} == {}",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        ConditionTerm::PointerEqual(left, right) => {
            format!(
                "{} == {}",
                describe_pointer(left, &[], &[]),
                describe_pointer(right, &[], &[])
            )
        }
    }
}

/// A fact spelled with its operands through the C parameter names, where the
/// kind-level `describe_pure_fact` says only "int32 equality is true". For a
/// message that must show two lowered terms side by side, such as a rewrite
/// whose equality was not found in its goal.
pub(super) fn describe_pure_fact_spelled(
    fact: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match fact {
        Proposition::ConditionIs(condition, value) => format!(
            "{} is {value}",
            describe_condition_with_context(condition, parameters, arguments)
        ),
        other => describe_pure_fact(other, parameters, arguments),
    }
}

/// [`describe_condition`] with machine operands spelled through the C
/// parameter names; shapes with no parameter-named operands fall back to
/// the context-free rendering.
pub(super) fn describe_condition_with_context(
    condition: &ConditionTerm,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let binary = |left: &Bitvector32Term, operator: &str, right: &Bitvector32Term| {
        format!(
            "{} {operator} {}",
            describe_bitvector_with_context(left, parameters, arguments),
            describe_bitvector_with_context(right, parameters, arguments)
        )
    };
    match condition {
        ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector64Equal(left, right) => binary(left, "==", right),
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right) => binary(left, "<", right),
        ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => binary(left, "<=", right),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => binary(left, ">", right),
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => binary(left, ">=", right),
        ConditionTerm::PointerEqual(left, right) => format!(
            "{} == {}",
            describe_pointer(left, parameters, arguments),
            describe_pointer(right, parameters, arguments)
        ),
        other => describe_condition(other),
    }
}

pub(super) fn describe_binary_condition(
    left: &Bitvector32Term,
    operator: &str,
    right: &Bitvector32Term,
) -> String {
    format!(
        "{} {operator} {}",
        describe_bitvector(left),
        describe_bitvector(right)
    )
}

fn describe_float_condition(condition: &CFloatCondition) -> String {
    match condition {
        CFloatCondition::Comparison {
            operator,
            left,
            right,
        } => {
            let operator = match operator {
                CComparisonOperator::Equal => "==",
                CComparisonOperator::NotEqual => "!=",
                CComparisonOperator::LessThan => "<",
                CComparisonOperator::LessEqual => "<=",
                CComparisonOperator::GreaterThan => ">",
                CComparisonOperator::GreaterEqual => ">=",
            };
            describe_binary_condition(left, operator, right)
        }
        CFloatCondition::Classification {
            classification,
            value,
        } => format!("is{classification:?}({})", describe_bitvector(value)),
    }
}
