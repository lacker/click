//! Surface Click specification syntax, checking, and proof orchestration.
//!
//! Surface Click is the shared specification language for C, C++, and Rust.
//! Target-language frontends belong under `crate::languages`; proof checking
//! uses the shared kernel.

use std::collections::{BTreeMap, BTreeSet};
mod program_values;
use crate::kernel::InstanceId;
use crate::kernel::RetainedProgramValue;
use program_values::ProgramValueBindings;
use std::fmt;

use crate::instrumentation::{self, TacticEvent, VerificationEvent};
use crate::kernel::proof::PropositionSource;
use crate::kernel::{
    Address, AddressBase, AddressOffset, AlgebraicValue, BitvectorEqualityDerivationStep,
    CheckedFunctionExecution, CheckedFunctionProposition,
    ComparisonOperator as KernelComparisonOperator, CompositeResourceDefinition, ConditionOutcome,
    ConditionTerm, ExecutionBudget, ExecutionEnvironment, ExecutionPureFact, ExecutionSemantics,
    ExecutionState, ExpressionOutcome, FunctionContract, FunctionContractClaim,
    FunctionContractClaimKey, FunctionContractClaimTarget, FunctionContractExecutionMode,
    FunctionExecutionCandidates, FunctionOutcome, FunctionSpecification, LoopEarlyExit, LoopEffect,
    LoopEffectCheck, LoopEffectSpan, LoopFinalExitCandidate, LoopInvariantCheck, LoopReturnExit,
    MachineTerm, MemoryRange, MemorySegment, ProgramExpression, ProgramFunction, ProgramStatement,
    ProgramType, ProgramValue, ProofObligation, Proposition, PropositionDerivation,
    PureFactContext, Resource, ResourceAccessMode as KernelResourceAccessMode, ResourceContext,
    ResourceContextValidityError, ResourceFact, ResourceFamily, ResourceSpec, ResourceStateSource,
    ResourceTransferRole, Sort, SpecAlgebraicExpression, SpecExpression, SpecPoint,
    SpecPredicateArgument, SpecProposition, SpecResource, StatementOutcome, SymbolicExecution,
    SymbolicMemory, Term, TerminationRefusal, Theorem, UnsuitableCallback, Variable,
    VerifiedLoopRule, VerifiedPureTheorem as KernelVerifiedPureTheorem,
    assume_universally_quantified_pure_implication, contract_refinement_context, int32,
    loop_invariants_hold_at_entry, program_assign, program_condition_fact_memories,
    program_declare, program_do_while_with_invariant_and_effect_checks, program_function,
    program_function_contract_refinement_arguments, program_function_entry_state,
    program_function_termination_plan, program_if, program_pointer_offsets_proven_equal_for_effect,
    program_seq, program_while_with_invariant_and_effect_checks, prove_int32_le_antisymmetric,
    prove_owned_resource_quantity_nonnegative, prove_program_condition_fact_transport,
    prove_program_function_contract_refinement,
    prove_symbolic_execution_statement_verification_paths_with_environment_and_loop_rule_using_budget,
    prove_symbolic_loop_exit_with_proven_phases_using_budget,
    prove_symbolic_program_condition_evaluation, prove_universally_quantified_pure_implication,
    prove_universally_quantified_pure_implication_by_int32_rewrites, resources_directly_match,
    substitute_int32_variable_in_proposition,
};
use crate::languages::c::syntax::{self, CExpression, LongRank};
use crate::languages::interface::InterfaceType;
use crate::persistent::PersistentMap;

fn contract_expression_function_address(expression: &ContractExpression) -> Option<&str> {
    match expression {
        ContractExpression::ProgramExpression(ProgramExpression::FunctionAddress(name)) => {
            Some(name)
        }
        ContractExpression::ProgramExpression(ProgramExpression::AddressOf(expression)) => {
            match expression.as_ref() {
                ProgramExpression::Variable(name) => name.named(),
                _ => None,
            }
        }
        _ => None,
    }
}

mod checking;
mod claim_labels;
mod diagnostics;
mod expansion;
mod generics;
pub(crate) use generics::primitive_instance_type;
mod integer_conversions;
mod integer_truncation;
mod lambdas;
mod lowering;
mod modules;
mod names;
mod parser;
mod pointer_result_types;
pub use crate::languages::{claim_label_matches, display_source_names, source_display_name};
pub(crate) mod planning;
pub(crate) mod proof_diagnostics;
mod source_registry;
mod struct_values;
mod structural_clauses;
pub use structural_clauses::StructuralClauses;
mod surface_propositions;
use integer_conversions::*;
use integer_truncation::*;
pub use surface_propositions::SurfacePropositionMap;
mod printing;
mod proof;
pub(crate) mod pure_fact_list;
mod scoped_names;
mod validation;
mod verification;

pub use crate::source::SourceContainer;
use checking::*;
pub(crate) use expansion::click_import_sites_in_container;
pub use expansion::{
    ClaimExpansion, ClaimLocationError, ClaimLocationScope, ClickImportSite, ContractProofClaim,
    NormalizeSourceSite, ProofSourceIndex, SelectedTacticExpansion, SmartTacticCandidate,
    SmartTacticSelectionError, SmartTacticSourceSite, SourceClaim, SourcePosition,
    c_select_smart_tactic, c_smart_tactic_source_sites, c_tactic_source_position, claim_at,
    click_declaration_source_position, click_import_sites, expand_c_claim_source,
    expand_c_claim_source_by_label, expand_c_prepared_claim_source_by_label,
    expand_c_prepared_tactic_source_at, expand_c_tactic_source_at, expand_c_tactics_source_at,
    expand_claim_by_label, expand_program_prepared_claim_source_by_label,
    expand_program_prepared_tactic_source_at, expand_project_claim_source_by_label,
    expand_project_tactic_source_at, expand_project_tactics_source_at, expand_tactics_source_at,
    expand_verified_function_claim_source_by_label, first_normalize_in_claim,
    normalize_source_sites, project_select_smart_tactic, project_smart_tactic_source_sites,
    project_tactic_source_position, project_tactic_source_positions, select_smart_tactic,
    selected_c_target, selected_project_c_target, selected_project_thread_runtime,
    selected_thread_runtime, smart_tactic_source_sites, tactic_source_position,
    verifying_source_paths,
};
use expansion::{
    ExpansionCapture, NestedTacticCapture, ProofSite, VerificationTarget, verification_target_at,
    verification_target_at_context,
};
use lowering::*;
pub use modules::resolve_click_project;

/// Whether a `.click` source is a declaration module: it declares only
/// imports, specification types, predicates, pure functions, and resources,
/// so it owns no claim and is verified only through the sidecars that import
/// it. Directory targets do not select such a file as an entry.
pub fn click_source_is_declaration_module(source: &str) -> bool {
    parser::declares_only_definitions(source)
}
use parser::ContractLetBinding;
pub use printing::{format_proof_certificate, format_proof_tactics};
use proof::*;
pub(crate) use pure_fact_list::PureFactList;
use source_registry::*;
#[cfg(test)]
#[cfg(test)]
use validation::proof_theorem_definitions;
use validation::{
    combined_click_function_definitions, combined_external_function_blocks,
    combined_predicate_definitions, combined_resource_definitions, contains_at_expression,
    contains_old_expression, describe_interface_type, describe_resource_clause,
    proposition_contains_at_expression, proposition_contains_liveness_claim,
    proposition_contains_old_expression, proposition_contains_resource_count,
    standard_library_theorem_definitions, standard_library_theorem_index,
};
pub(in crate::surface) use verification::ProgramSourceContext;
pub(in crate::surface) use verification::*;
pub use verification::{
    IncrementalSelection, ModelAssumption, ModelFamily, ProgramInputs, ProjectVerificationSummary,
    ProofArtifactIdentity, SorryAdmission, SummarizedVerification, c_external_dependencies,
    c_incremental_selection, c_prepared_external_dependencies, c_project_function_names,
    c_source_function_names, parse, project_selected_proof_names, project_summary,
    take_sorry_admissions, verify_c_prepared_project, verify_c_prepared_sources,
    verify_c_prepared_sources_functions, verify_c_project, verify_c_sources, verify_c_sources_at,
    verify_c_sources_functions, verify_click_theorems, verify_program_prepared_project,
    verify_project_at, verify_project_functions, verify_project_theorem,
    verify_project_with_summary, verify_sources_at, verify_standard_library, with_allow_sorry,
};
mod proof_trace;
pub use proof::{
    check_audit_claim, without_implicit_solve, without_implicit_solve_for_claim,
    without_proof_search, without_proof_search_for_claim,
};
pub use proof_trace::with_proof_trace;

/// Render one accepted checked path while `with_proof_trace` is active.
/// The selected tactic, when supplied, must occur on that path.
pub fn accepted_proof_trace(
    tactic_location: &dyn Fn(&str, &[usize]) -> Option<(String, crate::source::SourcePosition)>,
    branch_arm: &dyn Fn(&str, &[usize], &crate::source::SourcePosition) -> Option<usize>,
    have_body_contains: &dyn Fn(&str, &[usize], &crate::source::SourcePosition) -> bool,
    target: Option<&crate::source::SourcePosition>,
) -> Option<String> {
    let _typed = proof_diagnostics::render::TypedNotationScope::enter();
    let mut labels = proof_diagnostics::render::MemoryStateLabels::ambient();
    proof_trace::render_accepted(
        &mut labels,
        tactic_location,
        branch_arm,
        have_body_contains,
        target,
    )
    .map(|mut trace| {
        proof_trace::append_legend(&mut trace, &mut labels);
        trace
            .lines()
            .map(|line| line.strip_prefix("  ").unwrap_or(line))
            .collect::<Vec<_>>()
            .join("\n")
    })
}

/// Maximum UTF-8 bytes in an ordinary verifier error message. Set
/// `CLICK_FULL_DIAGNOSTICS=1` when an engine investigation needs unbounded
/// internal state.
pub const DEFAULT_DIAGNOSTIC_BYTE_LIMIT: usize = 16 * 1024;
pub const FULL_DIAGNOSTICS_ENV: &str = "CLICK_FULL_DIAGNOSTICS";

/// Apply the ordinary diagnostic byte limit after all context is assembled.
/// Explicit proof traces must be appended separately, after this boundary.
pub fn bound_diagnostic_message(message: String) -> String {
    diagnostics::bound_error_message(message)
}

/// User-visible word spellings recognized by Surface Click, including
/// contextual syntax words and compatibility-only spellings. Documentation
/// coverage compares this registry bidirectionally with its public inventory.
pub const SURFACE_CLICK_WORDS: &[&str] = &[
    "abstract",
    "address",
    "aligned",
    "all",
    "and",
    "any",
    "apply",
    "arithmetic",
    "as",
    "assumption",
    "at",
    "auto",
    "back_edge",
    "both",
    "branch",
    "outcomes",
    "by",
    "byte_offset",
    "call",
    "cases",
    "close",
    "close_invariants",
    "constructs",
    "consumes",
    "contains",
    "contract",
    "contradiction",
    "count",
    "decreases",
    "defined",
    "diverges",
    "else",
    "ensures",
    "ensuring",
    "executes",
    "entry",
    "enum",
    "enumerate",
    "exact",
    "execute",
    "execute_until",
    "exists",
    "exit",
    "fact",
    "false",
    "field",
    "fold",
    "forall",
    "fn",
    "function",
    "have",
    "if",
    "import",
    "implies",
    "program",
    "in",
    "induct",
    "initialize",
    "instantiate",
    "int32",
    "intro",
    "invariant",
    "known",
    "let",
    "load",
    "loop",
    "maintain",
    "mark",
    "match",
    "memory",
    "mode",
    "normalize",
    "not",
    "object",
    "observe",
    "obtain",
    "of",
    "old",
    "with",
    "or",
    "owns",
    "predicate",
    "prop",
    "preserve",
    "produces",
    "read",
    "read_event",
    "requires",
    "resource",
    "region",
    "rewrite",
    "same_allocation",
    "little_endian",
    "separate",
    "float32_from_bits",
    "float64_from_bits",
    "sizeof",
    "solve",
    "sorry",
    "spec",
    "statement",
    "step",
    "step_until",
    "struct",
    "tactic",
    "target",
    "theorem",
    "then",
    "transport",
    "uint8",
    "unfold",
    "uninitialized",
    "using",
    "verifying",
    "viewable",
    "views",
    "void",
    "where",
    "witness",
    "write",
    "true",
    "termination",
    "termination_local",
    "termination_strict",
    "termination_body",
    "termination_returns",
    "termination_divergence",
    "termination_callbacks",
    "strict",
    "normal",
    "check_termination_local",
    "check_termination_component",
    "check_termination_callbacks",
];

/// Stable identifiers for the documented Surface Click declaration,
/// contract, proposition, expression, and operator families. Individual word
/// forms are tracked separately in [`SURFACE_CLICK_WORDS`].
pub const SURFACE_CLICK_FORMS: &[&str] = &[
    "algebraic-constructor",
    "algebraic-declaration",
    "all",
    "and",
    "any",
    "at",
    "at-expression",
    "exact-expression",
    "region-allocation",
    "region-footprint",
    "region-parameter",
    "string-literal-reference",
    "read-event-result",
    "auto",
    "bool",
    "by",
    "c-fragment",
    "contains-proposition",
    "contract",
    "decreases",
    "defined",
    "diverges",
    "effect",
    "ensures",
    "exists",
    "fold",
    "forall",
    "function",
    "if-expression",
    "import",
    "iterated-ownership",
    "implies",
    "lambda",
    "lambda-application",
    "proposition-value",
    "let-where",
    "match-expression",
    "not",
    "old",
    "operator-bit-and",
    "operator-bit-not",
    "operator-bit-or",
    "operator-bit-xor",
    "operator-divide",
    "operator-eq",
    "operator-field",
    "operator-ge",
    "operator-gt",
    "operator-index",
    "operator-in",
    "operator-le",
    "operator-lt",
    "operator-minus",
    "operator-multiply",
    "operator-ne",
    "operator-plus",
    "operator-range",
    "operator-remainder",
    "operator-shift-left",
    "operator-shift-right",
    "or",
    "predicate",
    "predicate-call",
    "read",
    "requires",
    "resource",
    "resource-clause",
    "resource-witness",
    "same-object",
    "separate",
    "tactic",
    "target",
    "theorem",
    "verifying",
    "viewable",
    "write",
    "termination",
    "termination-goals",
];

/// The `click::` path of a Click library module identity:
/// `library/c/string.interface.click` is `click::c::string`.
fn library_module_path(identity: &str) -> String {
    let relative = identity
        .strip_prefix("library/")
        .and_then(|path| {
            path.strip_suffix(".interface.click")
                .or_else(|| path.strip_suffix(".click"))
        })
        .unwrap_or(identity);
    format!("click::{}", relative.replace('/', "::"))
}

/// The primitive types the Click library declares with `type`, like
/// `uint32` is to the kernel: each has no definition, only the library's
/// bodyless functions over it and the axioms relating them. Only a library
/// module declares one, and only one listed here.
pub(crate) const LIBRARY_PRIMITIVE_TYPES: &[&str] = &["Vec"];

/// The name a loop's invariants and proof read its pass count by: the number
/// of passes the loop has completed.
pub(crate) const LOOP_ITERATIONS_NAME: &str = "iterations";

/// The spelling of a loop's pass count past the loop: `loop(i).iterations`.
pub(crate) fn loop_iterations_spelling(index: usize) -> String {
    format!("loop({index}).{LOOP_ITERATIONS_NAME}")
}

/// The Rust accessors a proof reads a loop's iterator through, as written
/// after `iter.`: a call such as `len()` or a public field such as `start`.
pub(crate) const RUST_ITERATOR_ACCESSORS: [&str; 13] = [
    "len()",
    "count",
    "as_slice()",
    "start",
    "end",
    "start()",
    "end()",
    "is_empty()",
    "v",
    "v.len()",
    "rem",
    "rem.len()",
    "chunk_size",
];

/// The accessors of an iterator of `kind`, which are Rust's own:
/// `ExactSizeIterator::len`, `slice::Iter::as_slice`, a `Range`'s `start`
/// and `end` fields, a `RangeInclusive`'s `start()`, `end()`, and `is_empty()`, and a
/// `ChunksExact`'s fields `v`, `rem` and `chunk_size`.
pub(crate) fn rust_iterator_accessors(
    kind: crate::languages::interface::RustIteratorKind,
) -> &'static [&'static str] {
    match kind {
        crate::languages::interface::RustIteratorKind::Slice => &["len()", "as_slice()"],
        crate::languages::interface::RustIteratorKind::Enumerate => {
            &["len()", "as_slice()", "count"]
        }
        crate::languages::interface::RustIteratorKind::Range => &["start", "end", "len()"],
        crate::languages::interface::RustIteratorKind::RangeInclusive => {
            &["start()", "end()", "is_empty()"]
        }
        // A crate's own iterator is a struct the program holds: a proof
        // reads its fields through the local, `iter.n`.
        crate::languages::interface::RustIteratorKind::User => &[],
        crate::languages::interface::RustIteratorKind::Chunks => {
            &["v", "v.len()", "rem", "rem.len()", "chunk_size", "len()"]
        }
    }
}

/// `iter.<accessor>` of `iterator`, read from the state the importer keeps
/// for it. `iter.as_slice()` reads as a slice parameter does, its data.
pub(crate) fn rust_iterator_method(
    iterator: &crate::languages::interface::RustLoopIterator,
    accessor: &str,
) -> Result<ContractExpression, String> {
    use crate::languages::interface::RustIteratorKind as K;
    let expression = match (iterator.kind, accessor) {
        // A slice iterator is the slice it still covers: `iter.as_slice()`
        // reads as a slice parameter does, its data, and `iter.len()` is
        // its length. An enumeration also counts what it has yielded.
        (K::Slice | K::Enumerate, "len()" | "as_slice()") => {
            let fields = iterator
                .slice_fields
                .as_ref()
                .ok_or("missing slice iterator fields")?;
            ProgramExpression::Variable(if accessor == "len()" {
                fields.length.clone()
            } else {
                fields.pointer.clone()
            })
        }
        (K::Enumerate, "count") => ProgramExpression::Variable(
            iterator
                .count_binding
                .clone()
                .ok_or("missing count binding for enumerated iterator")?,
        ),
        (K::Range, "start" | "end" | "len()")
        | (K::RangeInclusive, "start()" | "end()" | "is_empty()") => {
            let [start, end] = iterator
                .range_bounds
                .clone()
                .ok_or("missing range bounds")?
                .map(ProgramExpression::Variable);
            match accessor {
                "start" | "start()" => start,
                "end" | "end()" => end,
                "len()" => ProgramExpression::Subtract(Box::new(end), Box::new(start)),
                _ => {
                    return proposition_bool_value(ClickProposition::Comparison {
                        left: ContractExpression::ProgramExpression(start),
                        operator: ComparisonOperator::GreaterThan,
                        right: ContractExpression::ProgramExpression(end),
                    });
                }
            }
        }
        // A slice field reads as a slice parameter does: `iter.v` is its
        // data and `iter.v.len()` its length.
        (K::Chunks, "v" | "v.len()" | "rem" | "rem.len()" | "chunk_size" | "len()") => {
            let fields = iterator
                .chunk_fields
                .as_ref()
                .ok_or("missing chunk iterator fields")?;
            let field = match accessor {
                "v" => &fields.remaining,
                "v.len()" => &fields.remaining_length,
                "rem" => &fields.remainder,
                "rem.len()" => &fields.remainder_length,
                "chunk_size" => &fields.size,
                _ => {
                    return Ok(ContractExpression::ProgramExpression(
                        ProgramExpression::Divide(
                            Box::new(ProgramExpression::Variable(fields.remaining_length.clone())),
                            Box::new(ProgramExpression::Variable(fields.size.clone())),
                        ),
                    ));
                }
            };
            ProgramExpression::Variable(field.clone())
        }
        _ => {
            return Err(format!(
                "`iter.{accessor}` is not an accessor of this loop's {} iterator{}",
                match iterator.kind {
                    K::Slice => "slice",
                    K::Enumerate => "enumerated",
                    K::Range => "range",
                    K::RangeInclusive => "inclusive range",
                    K::User => "crate",
                    K::Chunks => "`chunks_exact`",
                },
                match rust_iterator_accessors(iterator.kind) {
                    [] => " (it has none yet)".to_string(),
                    accessors => format!(
                        "; it has {}",
                        accessors
                            .iter()
                            .map(|accessor| format!("`iter.{accessor}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                }
            ));
        }
    };
    Ok(ContractExpression::ProgramExpression(expression))
}

/// The Rust spelling of the importer's iterator state variable `name` in a
/// function whose loops advance `iterators`: `loop(i).iter.len()` for loop
/// `i`'s remaining length, `loop(i).iter.as_slice()` for its cursor, and
/// bare `iter.len()` for the iterator of `current`, the loop whose phases
/// are being checked.
pub(crate) fn rust_iterator_spelling(
    iterators: &[Option<crate::languages::interface::RustLoopIterator>],
    current: Option<usize>,
    name: &crate::kernel::BindingName,
) -> Option<String> {
    let variable = ContractExpression::ProgramExpression(ProgramExpression::Variable(name.clone()));
    let accessor_of = |iterator: &crate::languages::interface::RustLoopIterator| {
        rust_iterator_accessors(iterator.kind)
            .iter()
            .find(|accessor| {
                rust_iterator_method(iterator, accessor).ok().as_ref() == Some(&variable)
            })
    };
    if let Some(index) = current
        && let Some(Some(iterator)) = iterators.get(index)
        && let Some(accessor) = accessor_of(iterator)
    {
        return Some(format!("iter.{accessor}"));
    }
    iterators.iter().enumerate().find_map(|(index, iterator)| {
        let accessor = accessor_of(iterator.as_ref()?)?;
        Some(format!("loop({index}).iter.{accessor}"))
    })
}

/// The proof names a loop's iterator gives inside loop `loop_index` of the
/// Rust function `signature`: `iter.len()` and `iter.as_slice()`, when that
/// loop advances one.
pub(crate) fn loop_iterator_bindings(
    signature: &FunctionSignature,
    loop_index: usize,
) -> Vec<(String, ContractExpression)> {
    let Some(iterator) = signature
        .rust_loop_iterators()
        .get(loop_index)
        .cloned()
        .flatten()
    else {
        return Vec::new();
    };
    rust_iterator_accessors(iterator.kind)
        .iter()
        .filter_map(|accessor| {
            Some((
                format!("iter.{accessor}"),
                rust_iterator_method(&iterator, accessor).ok()?,
            ))
        })
        .collect()
}

/// Whether a bare `name` is a Click value, `result` or a loop's
/// `iterations`, so a program binding of that name is written `program::name`.
pub(crate) fn is_click_value_name(name: impl Into<crate::kernel::BindingName>) -> bool {
    let name = name.into();
    let Some(name) = name.named() else {
        return false;
    };
    name == "result" || name == LOOP_ITERATIONS_NAME
}

/// Whether `name` is a loop's pass count as the parser spells it.
pub(crate) fn is_loop_iterations_spelling(name: &str) -> bool {
    name.strip_prefix("loop(")
        .and_then(|rest| rest.strip_suffix(").iterations"))
        .is_some_and(|index| !index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit()))
}

/// The Click library modules loaded implicitly with every sidecar, as
/// `(identity, source)` pairs in declaration order. Each module is parsed
/// with the declarations of the modules before it.
const CLICK_LIBRARY_MODULES: &[(&str, &str)] = &[
    (
        "library/separation.click",
        include_str!("../library/separation.click"),
    ),
    (
        "library/primitives.click",
        include_str!("../library/primitives.click"),
    ),
    ("library/nat.click", include_str!("../library/nat.click")),
    ("library/list.click", include_str!("../library/list.click")),
    (
        "library/option.click",
        include_str!("../library/option.click"),
    ),
    (
        "library/result.click",
        include_str!("../library/result.click"),
    ),
    (
        "library/permutation.click",
        include_str!("../library/permutation.click"),
    ),
    (
        "library/bytes.click",
        include_str!("../library/bytes.click"),
    ),
    (
        "library/c/builtins.interface.click",
        include_str!("../library/c/builtins.interface.click"),
    ),
    (
        "library/integer.click",
        include_str!("../library/integer.click"),
    ),
    (
        "library/float_order.click",
        include_str!("../library/float_order.click"),
    ),
    (
        "library/c/string.interface.click",
        include_str!("../library/c/string.interface.click"),
    ),
    (
        "library/c/stdarg.click",
        include_str!("../library/c/stdarg.click"),
    ),
    (
        "library/c/stdio.click",
        include_str!("../library/c/stdio.click"),
    ),
    (
        "library/cpp/vector_state.click",
        include_str!("../library/cpp/vector_state.click"),
    ),
    (
        "library/cpp/span_state.click",
        include_str!("../library/cpp/span_state.click"),
    ),
    (
        "library/rust/i8.click",
        include_str!("../library/rust/i8.click"),
    ),
    (
        "library/rust/i16.click",
        include_str!("../library/rust/i16.click"),
    ),
    (
        "library/rust/i32.click",
        include_str!("../library/rust/i32.click"),
    ),
    (
        "library/rust/i64.click",
        include_str!("../library/rust/i64.click"),
    ),
    (
        "library/rust/isize.click",
        include_str!("../library/rust/isize.click"),
    ),
    (
        "library/rust/u8.click",
        include_str!("../library/rust/u8.click"),
    ),
    (
        "library/rust/u16.click",
        include_str!("../library/rust/u16.click"),
    ),
    (
        "library/rust/u32.click",
        include_str!("../library/rust/u32.click"),
    ),
    (
        "library/rust/u64.click",
        include_str!("../library/rust/u64.click"),
    ),
    (
        "library/rust/usize.click",
        include_str!("../library/rust/usize.click"),
    ),
    (
        "library/rust/option.click",
        include_str!("../library/rust/option.click"),
    ),
    (
        "library/rust/result.click",
        include_str!("../library/rust/result.click"),
    ),
    (
        "library/rust/vec.click",
        include_str!("../library/rust/vec.click"),
    ),
    (
        "library/rust/slice.click",
        include_str!("../library/rust/slice.click"),
    ),
];

/// Emits one non-overlapping verifier phase on every exit path, including an
/// early `?`; see [`instrumentation::VerificationPhase`].
type VerificationTimingPhase = instrumentation::VerificationPhase;

fn check_verification_deadline() -> Result<(), ClickError> {
    if instrumentation::deadline_exceeded() {
        Err(ClickError::new(format!(
            "verification budget exhausted inside {}",
            instrumentation::deadline_context()
        )))
    } else {
        Ok(())
    }
}

/// A callee's execution name as its sidecar spells it: a
/// translation-unit-local function's `#inline:` or `#file-static:` suffix
/// removed.
pub(in crate::surface) fn call_source_spelling(callee: &str) -> &str {
    ["#inline:", "#file-static:"]
        .iter()
        .find_map(|suffix| callee.split_once(suffix).map(|(source, _)| source))
        .unwrap_or(callee)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFile {
    /// Physical struct strides retained for generic theorem instantiation.
    struct_sizes: std::sync::Arc<BTreeMap<String, u32>>,
    /// Unique source spelling to C execution identity, shared by specification lowering.
    program_function_names: std::sync::Arc<BTreeMap<String, String>>,
    imports: Vec<ImportDeclaration>,
    /// Click library modules this file imports with `import click::...;`, as
    /// their `library/` identities, once each in source order.
    library_imports: Vec<String>,
    verifying_sources: Vec<String>,
    /// The C implementation target this file selects with a `target`
    /// directive. `None` selects the default target.
    c_target: Option<crate::languages::c::target::CTarget>,
    /// Explicit trusted thread-runtime profile. Absent means ordinary C
    /// verification grants no create/join semantics.
    thread_runtime: crate::languages::c::thread_runtime::CThreadRuntime,
    algebraic_type_definitions: Vec<AlgebraicTypeDefinition>,
    predicate_definitions: Vec<PredicateDefinition>,
    click_function_definitions: Vec<ClickFunctionDefinition>,
    resource_definitions: Vec<ResourceDefinition>,
    theorem_definitions: Vec<TheoremDefinition>,
    contract_definitions: Vec<ContractDefinition>,
    function_blocks: Vec<FunctionBlock>,
    termination_proof: Option<Vec<ProofTactic>>,
    termination_span: Option<(crate::source::SourcePosition, crate::source::SourcePosition)>,
    /// User-defined tactics: contracts over the proof state, each proved once
    /// and then applied as one simple step.
    tactic_definitions: Vec<TacticDefinition>,
    /// Canonical project-relative owner of every declaration in this resolved
    /// file. Surface names are intentionally unqualified in the first module
    /// delivery; the owner keeps the internal identity qualified without
    /// changing the language spelling.
    declaration_owners: BTreeMap<DeclarationIdentity, String>,
    /// The module whose proofs this resolved file selects. Imported modules
    /// contribute declarations, never executable proof targets.
    entry_module: Option<String>,
    /// Where the parser read the entry module's declarations and proofs, so
    /// a tool addresses the source through what the parser read.
    source_spans: std::sync::Arc<parser::SourceSpans>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportDeclaration {
    path: String,
    position: crate::source::SourcePosition,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum DeclarationIdentity {
    AlgebraicType(String),
    Predicate(String),
    Function(String),
    Resource(String),
    Theorem(String),
    Contract(String),
    ProgramFunction(String),
    Tactic(String),
}

impl std::fmt::Display for DeclarationIdentity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (kind, name) = match self {
            Self::AlgebraicType(name) => ("type", name),
            Self::Predicate(name) => ("predicate", name),
            Self::Function(name) => ("function", name),
            Self::Resource(name) => ("resource", name),
            Self::Theorem(name) => ("theorem", name),
            Self::Contract(name) => ("contract", name),
            Self::ProgramFunction(name) => ("C function", name),
            Self::Tactic(name) => ("tactic", name),
        };
        write!(f, "{kind} `{name}`")
    }
}

/// One canonical source file in a resolved local specification graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickModuleSource {
    identity: String,
    source: String,
    imports: Vec<String>,
    /// Lines of the module's file that precede `source`: zero for a sidecar,
    /// and the lines before the ```click block body for an mdtest.
    /// Diagnostics add it so they name the line a person edits.
    line_offset: usize,
}

impl ClickModuleSource {
    pub fn new(
        identity: impl Into<String>,
        source: impl Into<String>,
        imports: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            identity: identity.into(),
            source: source.into(),
            imports: imports.into_iter().collect(),
            line_offset: 0,
        }
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub fn line_offset(&self) -> usize {
        self.line_offset
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn imports(&self) -> &[String] {
        &self.imports
    }
}

/// Immutable, canonical specification inputs for one entry module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickProject {
    entry: String,
    modules: Vec<ClickModuleSource>,
    c_profile: Option<CProjectProfile>,
    /// C bundle sources extracted from a larger file, by bundle path, so
    /// their diagnostics name that file and line. Empty for C files on disk.
    c_source_containers: BTreeMap<String, crate::source::SourceContainer>,
}

/// One project-wide C implementation selection. Files loaded without a
/// project config retain the historical sidecar directives and defaults.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CProjectProfile {
    pub target: Option<crate::languages::c::target::CTarget>,
    pub runtime: Option<crate::languages::c::thread_runtime::CThreadRuntime>,
}

impl ClickProject {
    pub fn new(
        entry: impl Into<String>,
        modules: impl IntoIterator<Item = ClickModuleSource>,
    ) -> Self {
        Self {
            entry: entry.into(),
            modules: modules.into_iter().collect(),
            c_profile: None,
            c_source_containers: BTreeMap::new(),
        }
    }

    /// Records that the C bundle source `path` is a block of a larger file,
    /// such as a ```c fence of an mdtest. Locations in that source are then
    /// reported as lines of the container. This changes diagnostics only.
    pub fn with_c_source_container(
        mut self,
        path: impl Into<String>,
        container: crate::source::SourceContainer,
    ) -> Self {
        self.c_source_containers.insert(path.into(), container);
        self
    }

    pub fn c_source_containers(&self) -> &BTreeMap<String, crate::source::SourceContainer> {
        &self.c_source_containers
    }

    pub fn with_c_profile(mut self, profile: CProjectProfile) -> Self {
        self.c_profile = Some(profile);
        self
    }

    pub fn c_profile(&self) -> Option<&CProjectProfile> {
        self.c_profile.as_ref()
    }

    pub fn entry(&self) -> &str {
        &self.entry
    }

    pub fn modules(&self) -> &[ClickModuleSource] {
        &self.modules
    }

    pub fn entry_source(&self) -> Option<&str> {
        self.modules
            .iter()
            .find(|module| module.identity == self.entry)
            .map(|module| module.source.as_str())
    }

    /// Places the entry module after `line_offset` lines of its file, as the
    /// ```click block of an mdtest. This changes diagnostics only.
    pub fn with_entry_line_offset(mut self, line_offset: usize) -> Self {
        if let Some(entry) = self
            .modules
            .iter_mut()
            .find(|module| module.identity == self.entry)
        {
            entry.line_offset = line_offset;
        }
        self
    }

    /// Returns the same loaded graph with only the entry module text replaced.
    /// Rewrite tools use this to re-check an expansion against unchanged imports.
    pub fn with_entry_source(&self, source: impl Into<String>) -> Self {
        let source = source.into();
        let mut rewritten = self.clone();
        if let Some(entry) = rewritten
            .modules
            .iter_mut()
            .find(|module| module.identity == rewritten.entry)
        {
            entry.source = source;
        }
        rewritten
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AlgebraicTypeDefinition {
    name: String,
    type_parameters: Vec<String>,
    variants: Vec<AlgebraicVariantDefinition>,
    /// A Click library primitive type, `type Vec<T>;`: no constructors, no
    /// `match` and no induction. The kernel reads each instance as a distinct
    /// rigid type, so nothing follows from its having no written variants.
    primitive: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AlgebraicVariantDefinition {
    name: String,
    fields: Vec<AlgebraicFieldType>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AlgebraicFieldType {
    Parameter(String),
    /// A pointer to the type parameter's values, `T*`: at an instance, the
    /// pointer type of `T`'s C representation, as a generic function's `T*`
    /// parameter is. A slice's data is one.
    ParameterPointer(String),
    Integer,
    /// A C value type. `struct_name` is the pointee's struct tag when the
    /// field is declared `struct tag*`; every C pointer shares one kernel
    /// type, so the tag is the only record of which layout a matched
    /// constructor binding of this field denotes.
    ///
    /// `object_class` is the class of the object a pointer field designates
    /// (`design/effective-types.md`), from the declared pointee exactly as a
    /// pointer parameter's declaration gives it. A symbolic value of the
    /// field carries it, so a pointer read from a model keeps its
    /// strict-aliasing and loop object-class checks.
    C {
        interface_type: InterfaceType,
        struct_name: Option<String>,
        object_class: Option<crate::kernel::effective_type::CAccessClass>,
    },
    Algebraic {
        name: String,
        arguments: Vec<AlgebraicFieldType>,
    },
}

impl AlgebraicFieldType {
    /// The struct tag a matched-arm binding of this field is a base for, or
    /// `None` when the field is not a C struct pointer.
    pub fn struct_pointer_name(&self) -> Option<&str> {
        match self {
            Self::C {
                interface_type,
                struct_name,
                ..
            } if interface_type.is_pointer() => struct_name.as_deref(),
            _ => None,
        }
    }

    /// How this field's type reads in a diagnostic about a match-arm binding.
    pub fn describe(&self) -> String {
        match self {
            Self::Parameter(name) => name.clone(),
            Self::ParameterPointer(name) => format!("{name}*"),
            Self::Integer => "Integer".to_string(),
            Self::C {
                struct_name: Some(name),
                ..
            } => format!("struct {name}*"),
            Self::C { interface_type, .. } => describe_interface_type(*interface_type),
            Self::Algebraic { name, .. } => name.clone(),
        }
    }
}

/// A value type in the Click specification language. C types are one family
/// of Click types; specification-only algebraic datatypes are another.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ClickType {
    /// A specification-only resource descriptor; it carries no ownership.
    Resource,
    /// A declaration-scoped type parameter. Generic logical declarations are
    /// instantiated to concrete types at applications, or rigid arbitrary
    /// types when checking theorem declarations, before crossing into Kernel Click.
    Parameter(String),
    Program(InterfaceType),
    /// A C pointer type whose generic payload retains its declared struct.
    CObjectPointer {
        interface_type: InterfaceType,
        struct_name: String,
    },
    /// An exact, specification-only signed integer with no C representation.
    Integer,
    /// A specification proposition, distinct from a C Bool value.
    Proposition,
    Algebraic(AlgebraicTypeApplication),
    /// A pure specification function; never a C function pointer.
    Function {
        parameters: Vec<ClickType>,
        result: Box<ClickType>,
    },
}

impl ClickType {
    pub fn interface_type(&self) -> Option<InterfaceType> {
        match self {
            Self::Resource => None,
            Self::Parameter(_) => None,
            Self::Program(interface_type) | Self::CObjectPointer { interface_type, .. } => {
                Some(*interface_type)
            }
            Self::Integer | Self::Proposition => None,
            Self::Algebraic(_) | Self::Function { .. } => None,
        }
    }
}

/// Whether a C value of type `name` is a spec value: a Rust enum's, or a
/// library primitive type's, a Rust `Vec<u32>`, rather than an abstract
/// type parameter's.
pub(in crate::surface) fn holds_spec_value(name: crate::kernel::TypeParameterName) -> bool {
    name.is_enum() || generics::primitive_instance_of(name.name()).is_some()
}

impl AlgebraicTypeApplication {
    pub(crate) fn concrete(name: impl Into<String>) -> Self {
        Self {
            rigid: false,
            name: name.into(),
            arguments: Vec::new(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn arguments(&self) -> &[ClickType] {
        &self.arguments
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AlgebraicTypeApplication {
    /// Internal rigid type parameter, never a datatype with zero constructors.
    rigid: bool,
    name: String,
    arguments: Vec<ClickType>,
}

impl AlgebraicTypeApplication {
    /// The `spec enum` a C value of `interface_type` holds, when it holds a Rust
    /// enum's: an enum parameter or result is that enum's value.
    pub(in crate::surface) fn of_enum_interface_type(
        interface_type: InterfaceType,
    ) -> Option<Self> {
        // A Rust `Vec<u32>` is the library's primitive `Vec<uint32>`.
        if let Some(ClickType::Algebraic(application)) =
            generics::primitive_instance_value_type(&ClickType::Program(interface_type))
        {
            return Some(application);
        }
        match interface_type {
            InterfaceType::Parameter(enum_type) if enum_type.is_enum() => Some(Self {
                rigid: false,
                name: enum_type.name().to_string(),
                arguments: enum_type
                    .algebraic_type()
                    .arguments
                    .iter()
                    .map(|argument| match argument {
                        crate::kernel::AlgebraicValueType::Program(interface_type) => {
                            Some(ClickType::Program(
                                crate::surface::generics::interface_type_from_program_type(
                                    *interface_type,
                                ),
                            ))
                        }
                        // A crate enum payload, `Result<u32, ParseError>`'s
                        // error, is that enum's `spec enum`.
                        crate::kernel::AlgebraicValueType::Algebraic { name, arguments }
                            if arguments.is_empty() =>
                        {
                            Some(ClickType::Algebraic(Self {
                                rigid: false,
                                name: name.clone(),
                                arguments: Vec::new(),
                            }))
                        }
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?,
            }),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AlgebraicMatchArm {
    type_name: String,
    variant: String,
    bindings: Vec<SurfaceBinder>,
    body: ContractExpression,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateDefinition {
    name: String,
    type_parameters: Vec<String>,
    parameters: Vec<FunctionParameter>,
    body: ClickProposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFunctionDefinition {
    name: String,
    type_parameters: Vec<String>,
    parameters: Vec<FunctionParameter>,
    return_type: ClickType,
    /// The class of the object a returned pointer designates, from the
    /// declared return type as a C function's declaration gives it
    /// (`design/effective-types.md`).
    return_object_class: Option<crate::kernel::effective_type::CAccessClass>,
    decreases: Option<ContractExpression>,
    /// `None` for a library primitive operation, `function len<T>(v:
    /// Vec<T>) -> uint64;`: an uninterpreted function, known only through
    /// the library's axioms. Only library modules declare one.
    body: Option<ContractExpression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceDefinition {
    name: String,
    parameters: Vec<FunctionParameter>,
    /// Named resource references; declaration alone does not grant ownership.
    resource_parameters: Vec<ResourceClause>,
    composite_body: Option<CompositeResourceBody>,
    field_schema: Option<crate::kernel::ResourceFieldSchema>,
    /// Declared `authorized resource`: the family takes part in population
    /// accounting, so `authority(...)` and `count(...)` may name it.
    authorized: bool,
    /// An `abstract resource` that declares fields: its instances carry
    /// fields, but it has no body, so no proof folds, unfolds, or observes
    /// one. Only a trusted contract produces or consumes an instance.
    sealed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompositeResourceBody {
    children: Vec<ResourceChildBody>,
    fields: Vec<ResourceFieldDefinition>,
    matched: Option<ResourceMatchBody>,
    condition: Option<ClickProposition>,
    contains: Vec<ResourceClause>,
    facts: Vec<ClickProposition>,
    /// Existential witnesses (`let next: struct node* where P;`). The
    /// `where` proposition is also one of `facts`; the witness name is in
    /// scope for every later clause of the body.
    witnesses: Vec<ResourceWitness>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceChildBody {
    name: String,
    /// The child's own declared resource. It is the parent's definition for a
    /// directly recursive child and another declared resource otherwise; its
    /// parameters and fields are what the child's arguments and field
    /// equations are checked against.
    resource: String,
    identity: crate::kernel::InstanceId,
    arguments: Vec<ContractExpression>,
    field_bindings: Vec<crate::kernel::ResourceChildField>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceMatchBody {
    field: String,
    arms: Vec<ResourceMatchArm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceMatchArm {
    type_name: String,
    variant: String,
    bindings: Vec<String>,
    body: CompositeResourceBody,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceFieldDefinition {
    name: String,
    click_type: ClickType,
}

impl ResourceFieldDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn click_type(&self) -> &ClickType {
        &self.click_type
    }
}

/// A pointer the body of a composite resource asserts to exist.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceWitness {
    name: String,
    interface_type: InterfaceType,
}

impl ResourceWitness {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct TheoremDefinition {
    /// A Click library `axiom`: trusted, never proved. Only a library module
    /// declares one, about the library's primitive operations.
    axiom: bool,
    /// `T*` supplies a declared element type, not original-object provenance.
    generic_pointer_parameters: BTreeSet<String>,
    /// Where the parser read this theorem's clauses.
    body: parser::DeclarationBody,
    name: String,
    type_parameters: Vec<String>,
    parameters: Vec<FunctionParameter>,
    executes: Option<TheoremExecution>,
    requires: Vec<Requirement>,
    ensures: Vec<EnsureClause>,
    /// For each entry of `ensures`, the written clause it names in claim
    /// labels: its kind and its position among the theorem's clauses of
    /// that kind. Empty when the theorem was built without a source.
    ensure_claim_ids: Vec<claim_labels::ClaimClauseId>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TheoremExecution {
    callback: String,
    parameters: Vec<FunctionParameter>,
    /// The conclusion's `as { parameter: name }` map, in the target contract's
    /// declaration order: one introduced instance name per target proof
    /// parameter. The target's own parameter spelling never enters the proof
    /// block, so this is the only way an instance is named there.
    target_instances: Vec<(String, String)>,
}

/// A named behavioral interface for a function pointer. The embedded block
/// deliberately reuses ordinary C-function contract syntax; unlike a
/// `FunctionBlock`, it is not attached to a C definition and carries no proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractDefinition {
    proof_parameters: Option<Vec<ResourceClause>>,
    /// Value parameters, `let amount: int32;`, in declaration order. They are
    /// the last parameters of the block's signature and are not part of the
    /// function type the contract applies to.
    value_parameters: Vec<String>,
    function_block: FunctionBlock,
}

/// A user-defined tactic: a contract over the proof state, with no C body.
///
/// Its clauses are a function contract's (`consumes`, `produces`, `owns`,
/// `views`, `requires`, `ensures`, `decreases`), and its `by` block proves
/// them once at a fixed execution point. An application is one simple step
/// that consumes and produces resource instances and adds the `ensures`
/// facts, leaving memory and C state unchanged.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TacticDefinition {
    function_block: FunctionBlock,
}

impl TacticDefinition {
    pub(in crate::surface) fn new(function_block: FunctionBlock) -> Self {
        Self { function_block }
    }

    pub fn name(&self) -> &str {
        self.function_block.signature().name()
    }

    /// The tactic's contract and proof, in the shape of a function block
    /// whose signature returns `void`.
    pub fn function_block(&self) -> &FunctionBlock {
        &self.function_block
    }

    pub(in crate::surface) fn function_block_mut(&mut self) -> &mut FunctionBlock {
        &mut self.function_block
    }
}

/// `step(Contract)`, or `step(Contract, { handle: instance, ... })` for a
/// contract whose body declares resource handles. Entries keep the order
/// written; the checker matches them to the contract's handles by name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractApplication {
    name: String,
    arguments: Vec<ContractResourceArgument>,
}

/// One `handle: instance` entry of a named-contract application.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractResourceArgument {
    /// The contract's handle name, written on the left of the entry.
    handle: String,
    /// The caller's instance name.
    name: String,
    resource_name: String,
    identity: InstanceId,
}

/// One entry of a call step's binder map: a binder the callee declared, and
/// the caller instance it is bound to. The `produces` form reuses the same
/// shape, with `instance` the name introduced by `let`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallBinderBinding {
    /// The callee's binder name, written on the left of the map entry.
    binder: String,
    /// The binder number the callee's own contract gave that binder.
    binder_identity: crate::kernel::ResourceBinder,
    /// The caller's resource name.
    instance: String,
    /// The binder number of the caller's resource; the callee's clause for
    /// `binder` says whether it names an instance or a mutex authority.
    identity: crate::kernel::ResourceBinder,
    /// The resource a produced instance is, from the callee's contract;
    /// `None` for an instance the caller supplies.
    family: Option<String>,
    /// For an instance a `step(callee, { ... })` produces, the proof-local
    /// names its resource arguments read, `name.parameter` for each of the
    /// callee's parameters in order: the step binds each to the frontier
    /// call's argument.
    call_arguments: Vec<String>,
}

impl CallBinderBinding {
    pub fn binder(&self) -> &str {
        &self.binder
    }

    pub fn instance(&self) -> &str {
        &self.instance
    }

    pub(crate) fn binder_identity(&self) -> crate::kernel::ResourceBinder {
        self.binder_identity
    }

    pub(crate) fn identity(&self) -> crate::kernel::ResourceBinder {
        self.identity
    }

    pub(crate) fn resolve_identity(
        &self,
        state: &ExecutionState,
    ) -> Option<crate::kernel::ResourceBinder> {
        let Some((_, path)) = self.instance.split_once('.') else {
            return Some(self.identity);
        };
        let path = path.split('.').map(str::to_owned).collect::<Vec<_>>();
        state
            .resource_instance_at_path(self.identity.instance()?, &path)
            .map(|instance| crate::kernel::ResourceBinder::Instance(instance.identity()))
    }

    pub(crate) fn family(&self) -> Option<&str> {
        self.family.as_deref()
    }

    pub(crate) fn call_arguments(&self) -> &[String] {
        &self.call_arguments
    }
}

/// One checked C call with every interface instance binder bound explicitly.
/// `step(callee, { ... })` names an ordinary callee, whose arguments are the
/// frontier call's; `step(Contract, { ... })` selects a named interface for
/// the current call. A user tactic application, `name(args, { ... })`,
/// shares the shape with its written arguments. Produced
/// instances and the C value are named explicitly by
/// `let { result: value, binder: resource, ... } = step(...)`.
/// The pattern only selects names for outputs of the checked transition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallBinderTransport {
    callee: String,
    /// Select this named interface at the current C call; arguments come from C.
    named_contract: bool,
    /// `step(callee, { ... })`: the step names its C function, and the call's
    /// arguments are the call at the frontier, which must call `callee`.
    frontier: bool,
    arguments: Vec<ContractExpression>,
    binders: Vec<CallBinderBinding>,
    produced: Vec<CallBinderBinding>,
    /// Runtime binders that name a resource type, with the type written.
    type_arguments: Vec<(String, Variable, ResourceClause)>,
    /// The values the call map gives the callee's `let` value parameters,
    /// `{ n: k }`, each with the parameter it names.
    value_arguments: Vec<(String, ContractExpression)>,
    result: Option<String>,
}

impl CallBinderTransport {
    pub fn callee(&self) -> &str {
        &self.callee
    }

    pub fn is_named_contract(&self) -> bool {
        self.named_contract
    }

    /// Whether the step takes its call's arguments from the frontier call,
    /// `step(callee, { ... })`.
    pub fn is_frontier(&self) -> bool {
        self.frontier
    }

    pub fn type_arguments(&self) -> &[(String, Variable, ResourceClause)] {
        &self.type_arguments
    }

    /// The transport with each written resource type replaced by `map`'s
    /// result, as declaration expansion resolves resource clauses.
    pub(crate) fn try_map_type_arguments(
        mut self,
        mut map: impl FnMut(ResourceClause) -> Result<ResourceClause, ClickError>,
    ) -> Result<Self, ClickError> {
        self.type_arguments = self
            .type_arguments
            .into_iter()
            .map(|(name, identity, resource)| Ok((name, identity, map(resource)?)))
            .collect::<Result<_, ClickError>>()?;
        Ok(self)
    }

    pub fn value_arguments(&self) -> &[(String, ContractExpression)] {
        &self.value_arguments
    }

    /// `binder: instance` and `binder: Type(args)` entries in written order
    /// of kind: instances first, then resource types.
    fn map_entries(&self) -> Vec<String> {
        self.binders
            .iter()
            .map(|binding| format!("{}: {}", binding.binder, binding.instance))
            .chain(self.type_arguments.iter().map(|(name, _, resource)| {
                format!("{name}: {}", printing::format_resource_call(resource))
            }))
            .chain(self.value_arguments.iter().map(|(name, value)| {
                format!(
                    "{name}: {}",
                    diagnostics::describe_contract_expression(value)
                )
            }))
            .collect()
    }

    pub fn arguments(&self) -> &[ContractExpression] {
        &self.arguments
    }

    pub fn binders(&self) -> &[CallBinderBinding] {
        &self.binders
    }

    pub fn produced(&self) -> &[CallBinderBinding] {
        &self.produced
    }

    /// The proof-local name this step gives the call's C value, independently
    /// of its produced resource instances.
    pub fn result(&self) -> Option<&str> {
        self.result.as_deref()
    }
}

impl CallBinderTransport {
    /// The transport spelled as a tactic application: `name(args)`, then the
    /// binder map when there is one, after a `let` output pattern when the
    /// tactic produces instances.
    pub fn tactic_spelling(&self) -> String {
        let mut spelling = String::new();
        if !self.produced.is_empty() {
            spelling.push_str("let { ");
            for (index, produced) in self.produced.iter().enumerate() {
                if index != 0 {
                    spelling.push_str(", ");
                }
                spelling.push_str(&format!("{}: {}", produced.binder, produced.instance));
            }
            spelling.push_str(" } = ");
        }
        spelling.push_str(&self.callee);
        spelling.push('(');
        for (index, argument) in self.arguments.iter().enumerate() {
            if index != 0 {
                spelling.push_str(", ");
            }
            spelling.push_str(&diagnostics::describe_contract_expression(argument));
        }
        let entries = self.map_entries();
        if !entries.is_empty() {
            if !self.arguments.is_empty() {
                spelling.push_str(", ");
            }
            spelling.push_str(&format!("{{ {} }}", entries.join(", ")));
        }
        spelling.push(')');
        spelling
    }
}

impl std::fmt::Display for CallBinderTransport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.produced.is_empty() || self.result.is_some() {
            write!(f, "let {{ ")?;
            if let Some(result) = &self.result {
                write!(f, "result: {result}")?;
            }
            for (index, produced) in self.produced.iter().enumerate() {
                if index != 0 || self.result.is_some() {
                    write!(f, ", ")?;
                }
                write!(f, "{}: {}", produced.binder, produced.instance)?;
            }
            write!(f, " }} = ")?;
        }
        if self.named_contract || self.frontier {
            let entries = self.map_entries();
            return if entries.is_empty() {
                write!(f, "step({})", self.callee)
            } else {
                write!(f, "step({}, {{ {} }})", self.callee, entries.join(", "))
            };
        }
        write!(f, "step({}(", self.callee)?;
        for (index, argument) in self.arguments.iter().enumerate() {
            if index != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", diagnostics::describe_contract_expression(argument))?;
        }
        write!(f, ")")?;
        // An application with written arguments retains its legacy form.
        let entries = self.map_entries();
        if entries.is_empty() {
            write!(f, ", {{}}")?;
        } else {
            write!(f, ", {{ {} }}", entries.join(", "))?;
        }
        write!(f, ")")
    }
}

impl From<String> for ContractApplication {
    fn from(name: String) -> Self {
        Self {
            name,
            arguments: Vec::new(),
        }
    }
}

impl From<&str> for ContractApplication {
    fn from(name: &str) -> Self {
        name.to_string().into()
    }
}

impl std::fmt::Display for ContractApplication {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.arguments.is_empty() {
            write!(f, ", {{ ")?;
            for (index, argument) in self.arguments.iter().enumerate() {
                if index != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}: {}", argument.handle, argument.name)?;
            }
            write!(f, " }}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClickFunctionType {
    value_parameter: bool,
    type_parameters: Vec<String>,
    parameters: Vec<FunctionParameter>,
    return_type: ClickType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionBlock {
    /// Where the parser read this block's clauses.
    body: parser::DeclarationBody,
    /// C objects visible in this declaration, supplied by the source frontend.
    program_object_names: std::sync::Arc<BTreeSet<String>>,
    signature: FunctionSignature,
    external: bool,
    /// Internal source grouping for an `executes` theorem's call and return.
    /// The kernel still checks the complete ordinary statement sequence.
    one_call_proof: bool,
    /// This block is a user-defined tactic's contract, certified as a
    /// procedure whose body runs no code. Its write frame is empty: the
    /// procedure writes nothing, so an application leaves memory unchanged.
    tactic_procedure: bool,
    requires: Vec<Requirement>,
    /// For each entry of `requires`, the 0-based index of the clause the
    /// author wrote it in. An aggregate clause (an embedded struct field)
    /// is flattened into one requirement per segment while parsing; this is
    /// what lets a diagnostic number clauses the way the source does.
    /// Empty when the block was built without a source (tests), in which
    /// case each requirement counts as its own clause.
    requirement_source_clauses: Vec<usize>,
    decreases: Option<FunctionDecrease>,
    /// The other members of this function's recursive C component, supplied
    /// by the source frontend; empty outside a component of two or more.
    recursion_peers: Vec<String>,
    structural_clauses: StructuralClauses,
    constructs: Vec<ResourceClause>,
    ensures: Vec<EnsureClause>,
    exceptional_ensures: Vec<EnsureClause>,
    /// As `requirement_source_clauses`, for `ensures`.
    ensure_source_clauses: Vec<usize>,
    /// For each entry of `ensures`, the written clause it names in claim
    /// labels: its kind (`ensures`, `owns`, or `produces`) and its position
    /// among the block's clauses of that kind. Members of a flattened
    /// aggregate clause share their clause's id. Empty when the block was
    /// built without a source; labels then read the kind off each clause.
    ensure_claim_ids: Vec<claim_labels::ClaimClauseId>,
    /// Shared: every frontier `loop` binds its clause into a copy of this
    /// block, and the grouped proof is the whole claim's script.
    grouped_proof: Option<std::sync::Arc<SourceProof>>,
    /// The struct each opaque `void *` parameter is cast to in this block's
    /// clauses and proof, by parameter name. A block casts a parameter to at
    /// most one struct; proof synthesis reads memory through the parameter
    /// with that layout, as it does for a declared struct-pointer parameter.
    parameter_struct_casts: BTreeMap<String, String>,
    /// The scalar fields of each struct parameter's layout, and of each
    /// local struct pointer's, by name. Printing only: `click expand` writes a read at a field's
    /// offset as the field place.
    parameter_field_places: BTreeMap<crate::kernel::BindingName, Vec<FieldPlace>>,
    /// The scalar fields of each struct those places point to, by struct
    /// name, transitively. Printing only, as above.
    pointee_field_places: BTreeMap<String, Vec<FieldPlace>>,
    /// How many of the signature's parameters, at its end, are the value
    /// parameters its `let n: type;` declarations introduce. They are not C
    /// parameters: a call supplies them from the instance a clause selects
    /// or the call map names, and the body is proved for every value.
    witness_count: usize,
    /// The block's `allocates(result, n)`: the returned allocation is one
    /// the call creates, a block no earlier pointer reaches.
    allocates_result: bool,
}

/// Turns the source clause of each flattened clause into its position among
/// the distinct source clauses, with their count. A clause with no recorded
/// source counts as its own clause.
fn source_positions(sources: impl Iterator<Item = Option<usize>>) -> Vec<(usize, usize)> {
    let sources = sources.collect::<Vec<_>>();
    let mut ordinals = Vec::with_capacity(sources.len());
    let mut distinct: Vec<usize> = Vec::new();
    for (flattened, source) in sources.iter().enumerate() {
        let key = source.unwrap_or(usize::MAX - flattened);
        let ordinal = match distinct.iter().position(|seen| *seen == key) {
            Some(ordinal) => ordinal,
            None => {
                distinct.push(key);
                distinct.len() - 1
            }
        };
        ordinals.push(ordinal);
    }
    let count = distinct.len();
    ordinals
        .into_iter()
        .map(|ordinal| (ordinal, count))
        .collect()
}

/// A C function's `decreases` measure.
///
/// Decision D6: the clause is one expression, and functions and resources
/// share one namespace, so the parser cannot tell which kind of measure it
/// read. It stores [`FunctionDecrease::Unresolved`], and declared-resource
/// expansion — the pass that knows every declared resource and every contract
/// binder — classifies it into one of the resolved forms below.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FunctionDecrease {
    /// The parsed expression, before resolution decides what it names.
    Unresolved(ContractExpression),
    Numeric(ContractExpression),
    /// A tuple of numeric components, `decreases (m, n);`, ranked
    /// lexicographically as a loop's tuple is.
    Lexicographic(Vec<ContractExpression>),
    Resource(ResourceClause),
    /// A contract resource binder named without arguments, as in
    /// `owns t: tree_at(root); decreases t;`.
    Binder(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSignature {
    return_type: InterfaceType,
    /// Declared nominal type of a pointer result, independent of its C carrier.
    return_struct_name: Option<String>,
    return_pointee_constant: bool,
    return_reference: bool,
    name: String,
    /// Translation unit selected by a file-qualified C contract head.
    c_source: Option<String>,
    parameters: Vec<FunctionParameter>,
    /// The payload type of the function's declared exceptional outcome.
    /// This surface slice currently accepts only `throws int32`.
    exceptional_type: Option<InterfaceType>,
    /// Whether the signature declares `diverges`: the function may not
    /// return. Termination is opt-in today, so the marker changes no
    /// judgment; it withholds the whole-function termination evidence a
    /// `decreases` clause would otherwise request.
    diverges: bool,
    /// Byte spans declared by sized array parameter spellings
    /// (`int32 p[2]`), used to certify requirement side-obligations.
    declared_loadable_bytes: Vec<(String, u32)>,
    /// How a diagnostic spells this function's places, from how its
    /// signature is written.
    rust_spelling: RustSignatureSpelling,
}

/// A Rust sidecar's `fn` signature: its slice parameters, each passed as a
/// pointer and a `name_len` length, which a diagnostic and `click expand`
/// print as `name.len()`. `None` for a signature in the C-shaped spelling.
/// Presentation only: the Rust and C-shaped spellings of one declaration are
/// equal.
/// It also carries the iterator each of the function's loops advances,
/// which a proof names `iter` and `loop(i).iter`.
#[derive(Clone, Debug, Default)]
pub(crate) struct RustSignatureSpelling(
    Option<Vec<String>>,
    std::sync::Arc<[Option<crate::languages::interface::RustLoopIterator>]>,
);

impl RustSignatureSpelling {
    pub(crate) fn rust(slice_parameters: Vec<String>) -> Self {
        Self(Some(slice_parameters), std::sync::Arc::from([]))
    }

    pub(crate) fn slice_parameters(&self) -> Option<&[String]> {
        self.0.as_deref()
    }

    pub(crate) fn loop_iterators(
        &self,
    ) -> &std::sync::Arc<[Option<crate::languages::interface::RustLoopIterator>]> {
        &self.1
    }
}

impl PartialEq for RustSignatureSpelling {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for RustSignatureSpelling {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionParameter {
    slice_length: Option<crate::kernel::BindingName>,
    click_type: ClickType,
    name: String,
    struct_name: Option<String>,
    function_pointer_signature: Option<crate::languages::interface::CallbackInterface>,
    constant: bool,
    pointee_constant: bool,
    /// Whether the source declares the parameter as a reference. Its name
    /// then denotes the referent; `click_type` is the pointer that carries it.
    reference: bool,
}

/// A scalar field of a struct as a typed read finds it: the read of
/// `value_type` at `offset_bytes` is the field `name`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct FieldPlace {
    name: String,
    offset_bytes: u32,
    value_type: ProgramType,
    pointee_constant: bool,
    /// For a pointer to a struct, that struct: a read through the loaded
    /// pointer names the struct's fields, `p->next->second`.
    pointee_struct: Option<String>,
    /// For an array of scalars, its element width and length: a read of
    /// element `k` names `field[k]`, and `value_type` is the element's.
    array: Option<(u32, u32)>,
}

/// The fields of `layout` a typed read can name: its scalar fields, and
/// those of a struct nested in it, `inner.x`, at their offset from the
/// start of `layout`, and its arrays of scalars, each one place whose
/// elements a read names by index. A union is not one place and is left out.
pub(in crate::surface) fn scalar_field_places(
    layout: &crate::languages::interface::RecordLayout,
    layouts: &impl syntax::StructLayouts,
) -> Vec<FieldPlace> {
    // Each nested struct is entered once per field that holds it, so the
    // places are as many as the scalar members the layout has. A struct
    // cannot contain itself by value; the depth bound is for a malformed
    // layout map and never for a real one.
    fn collect(
        layout: &crate::languages::interface::RecordLayout,
        layouts: &impl syntax::StructLayouts,
        prefix: &str,
        base: u32,
        depth: usize,
        places: &mut Vec<FieldPlace>,
    ) {
        for (name, field) in layout.fields() {
            if field.union_name().is_some() || field.is_long_double() {
                continue;
            }
            // A symbolic layout's fields are at `offsetof` terms, which
            // these byte places do not hold.
            let Some(field_offset) = field.offset().bytes() else {
                continue;
            };
            let name = format!("{prefix}{name}");
            let offset_bytes = base + field_offset;
            if field.array_element_width().is_some() {
                let element = match field.interface_type() {
                    InterfaceType::Int32Array(length) => Some((ProgramType::Int32, 4, length)),
                    InterfaceType::UInt32Array(length) => Some((ProgramType::UInt32, 4, length)),
                    InterfaceType::UInt8Array(length) => Some((ProgramType::UInt8, 1, length)),
                    _ => None,
                };
                if let Some((value_type, width, length)) = element
                    && field.struct_name().is_none()
                {
                    places.push(FieldPlace {
                        name,
                        offset_bytes,
                        value_type,
                        pointee_constant: false,
                        pointee_struct: None,
                        array: Some((width, length)),
                    });
                }
                continue;
            }
            // A struct held by value is entered; a pointer to one is a
            // scalar place like any other pointer field.
            match field.struct_name() {
                Some(nested) if !field.interface_type().is_pointer() => {
                    if let Some(nested) = layouts.struct_layout(nested)
                        && depth < 8
                    {
                        collect(
                            nested,
                            layouts,
                            &format!("{name}."),
                            offset_bytes,
                            depth + 1,
                            places,
                        );
                    }
                }
                _ => places.push(FieldPlace {
                    name,
                    offset_bytes,
                    value_type: field.interface_type().to_kernel_type(),
                    pointee_constant: field.pointee_is_constant(),
                    pointee_struct: field
                        .struct_name()
                        .filter(|_| field.interface_type().is_pointer())
                        .map(str::to_string),
                    array: None,
                }),
            }
        }
    }
    let mut places = Vec::new();
    collect(layout, layouts, "", 0, 0, &mut places);
    places
}

/// The field places of every struct a pointer field of `places` reaches,
/// transitively, by struct name: what a read through a loaded pointer,
/// `p->next->second`, can name. Each struct is laid out once.
pub(in crate::surface) fn pointee_field_places<'a>(
    places: impl IntoIterator<Item = &'a Vec<FieldPlace>>,
    layouts: &impl syntax::StructLayouts,
) -> BTreeMap<String, Vec<FieldPlace>> {
    let mut reached = BTreeMap::new();
    let mut pending = places
        .into_iter()
        .flatten()
        .filter_map(|place| place.pointee_struct.clone())
        .collect::<Vec<_>>();
    while let Some(name) = pending.pop() {
        if reached.contains_key(&name) {
            continue;
        }
        let Some(layout) = layouts.struct_layout(&name) else {
            continue;
        };
        let fields = scalar_field_places(layout, layouts);
        pending.extend(
            fields
                .iter()
                .filter_map(|place| place.pointee_struct.clone()),
        );
        reached.insert(name, fields);
    }
    reached
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    LoadableSegment { segment: ContractSegment },
    Resource(ResourceClause),
    Proposition(ClickProposition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnsureClause {
    /// Value aliases visible where this claim and its proof were written.
    proof_bindings: Vec<(String, Option<ClickType>, ContractExpression)>,
    name: Option<String>,
    ensure: Ensure,
    proof: SourceProof,
    /// A resource ensure desugared from `owns`: the function returns what it
    /// was lent, so the clause is evaluated at entry, not at exit.
    borrowed: bool,
    /// Source requirement index (before aggregate expansion) selected by `from`.
    view_source: Option<usize>,
    /// A resource ensure nested in a contract `if`. The condition is a
    /// pre-state proposition; the clause is present in the post-state only
    /// when that proposition is established at the call boundary.
    condition: Option<ClickProposition>,
}

/// A loop or function region's clause. Its contents are shared by its
/// copies: a proof binds every earlier loop's clause into the function block
/// at each `loop` tactic, and copying the clauses whole made each loop pay
/// for the loops before it. Writing a field of a shared clause copies it.
#[derive(Clone, Eq, PartialEq)]
pub struct StructuralClause(std::sync::Arc<StructuralClauseData>);

impl std::ops::Deref for StructuralClause {
    type Target = StructuralClauseData;

    fn deref(&self) -> &StructuralClauseData {
        &self.0
    }
}

impl std::ops::DerefMut for StructuralClause {
    fn deref_mut(&mut self) -> &mut StructuralClauseData {
        std::sync::Arc::make_mut(&mut self.0)
    }
}

impl From<StructuralClauseData> for StructuralClause {
    fn from(data: StructuralClauseData) -> Self {
        Self(std::sync::Arc::new(data))
    }
}

impl std::fmt::Debug for StructuralClause {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let data = &self.0;
        formatter
            .debug_struct("StructuralClause")
            .field("region", &data.region)
            .field("label", &data.label)
            .field("decreases", &data.decreases)
            .field("diverges", &data.diverges)
            .field("items", &data.items)
            .field("scope", &data.scope)
            .field("resources", &data.resources)
            .field("initialize_proof", &data.initialize_proof)
            .field("preserve_proof", &data.preserve_proof)
            .field("otherwise_proof", &data.otherwise_proof)
            .finish()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralClauseData {
    region: CodeRegion,
    label: Option<String>,
    decreases: Option<TerminationMeasure>,
    /// Whether the head declares `loop diverges`: this loop may not exit.
    /// It excludes a `decreases` clause and requires the enclosing function
    /// to be declared `diverges` too.
    diverges: bool,
    items: Vec<StructuralItem>,
    /// The proof locals in scope where a frontier loop clause was written: a
    /// proof `match` arm's bindings, `let { ... } = unfold(...)` names, call-result
    /// binders. The clause keeps its written spelling, which expansion
    /// prints; every lowering reads it through [`StructuralClause::resolved`].
    scope: BinderMap<ContractExpression>,
    /// Resource clauses declared beside the invariants. They give the region
    /// the write and read authority of a callee contract: the body executes
    /// owning exactly these resources, and the loop's write footprint is the
    /// memory they own.
    resources: Vec<ResourceClause>,
    initialize_proof: Option<SourceProof>,
    preserve_proof: Option<SourceProof>,
    otherwise_proof: Option<SourceProof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TerminationMeasure {
    components: Vec<ContractExpression>,
    /// The components as written, when resolving a loop clause's proof
    /// scope rewrote them. A proof-local name such as a `let { field: name }
    /// = unfold(...)` binder is replaced by the value it names, but the
    /// termination plan reads the written clause, so the loop head keeps the
    /// written spelling to name the component by.
    written: Option<Vec<Option<ContractExpression>>>,
}

impl TerminationMeasure {
    pub(crate) fn new(components: Vec<ContractExpression>) -> Self {
        Self {
            components,
            written: None,
        }
    }

    pub fn components(&self) -> &[ContractExpression] {
        &self.components
    }

    /// The written spelling of component `index` when resolving the proof
    /// scope changed it.
    pub(in crate::surface) fn rewritten_component_source(
        &self,
        index: usize,
    ) -> Option<&ContractExpression> {
        self.written.as_ref()?.get(index)?.as_ref()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum CodeRegion {
    Function,
    Loop(usize),
    Statement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralItem {
    claim: ClickProposition,
    /// The label the invariant was written with, `invariant name: P;`.
    name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ensure {
    Proposition(ClickProposition),
    Resource(ResourceClause),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ResourceClause {
    /// A resource owned or viewed exactly when its contract condition holds.
    /// Initially exposed in loop contracts, using ordinary resource assertions.
    Conditional {
        condition: ClickProposition,
        resource: Box<ResourceClause>,
    },
    Named {
        binding: ResourceInstanceBinding,
        resource: Box<ResourceClause>,
    },
    ViewMemory(ContractSegment),
    OwnMemory(ContractSegment),
    /// A source-level aggregate place expanded into its typed leaf memory
    /// ranges. The kernel resource algebra remains a collection of ordinary
    /// typed memory facts; this node preserves the fact that one contract
    /// clause requested the complete aggregate.
    MemoryAggregate {
        access: ResourceAccessMode,
        segments: Vec<ContractSegment>,
    },
    Quantified {
        quantity: ContractExpression,
        resource: Box<ResourceClause>,
    },
    Declared {
        access: ResourceAccessMode,
        kind: ResourceKind,
        name: String,
        arguments: Vec<ContractExpression>,
        /// Checked field shape when this declaration is used as a resource type.
        /// This does not name an occurrence or provide any field observations.
        type_schema: Option<crate::kernel::ResourceFieldSchema>,
        /// Resource types passed as arguments, independently of named instances.
        resource_type_arguments: Vec<ResourceClause>,
        resource_arguments: Vec<ResourceInstanceBinding>,
        parameter_types: Vec<InterfaceType>,
    },
    /// `forall (k: int32) where lo <= k and k < hi { if g[k] == v { owns
    /// base[..]; } }` in a resource body: iterated guarded ownership. Only a
    /// resource body may contain one; see `lowering/iterated_lowering.rs`.
    Iterated(Box<IteratedResourceClause>),
}

/// A proof step on iterated guarded ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IteratedTactic {
    Unfold(Box<IteratedTarget>),
    Fold(Box<IteratedTarget>),
}

/// An index or the whole (`[..]`) iterated clause of a resource. A saved
/// point selects the resource arguments only; guards use the current state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IteratedTarget {
    resource: ResourceClause,
    point: Option<ProgramPointSelector>,
    index: Option<ContractExpression>,
}

impl IteratedTactic {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Unfold(_) => "unfold",
            Self::Fold(_) => "fold",
        }
    }
}

/// One iterated guarded-ownership clause as written. The shape the kernel
/// needs (index bounds, element stride and offsets, guard cell and value) is
/// derived from these by `crate::surface::lowering::iterated_clause_shape`,
/// which validation runs once per definition.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct IteratedResourceClause {
    /// The resource definition whose body declares the clause.
    pub(crate) owner: String,
    /// The index binder, as written.
    pub(crate) binder: SurfaceBinder,
    /// The `where` proposition bounding the index.
    pub(crate) range: ClickProposition,
    /// The optional `if` guard selecting which indices are held.
    pub(crate) guard: Option<ClickProposition>,
    /// The element range at index `binder`.
    pub(crate) element: ContractSegment,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ResourceInstanceBinding {
    unnamed: bool,
    /// The spelling of a lexical binder or, for an unnamed instance, its
    /// resource application for presentation.
    name: String,
    /// What the binder names comes from its resource: an instance, or a
    /// mutex authority for a named mutex live, use or guard clause.
    identity: crate::kernel::ResourceBinder,
    children: Vec<String>,
    schema: Option<crate::kernel::ResourceFieldSchema>,
    fields: Option<crate::kernel::ResourceFieldValues>,
    /// Present only on an explicit proof-side resource construction.
    fold_fields: Option<Vec<(String, ContractExpression)>>,
    /// Explicit child slot, surface name, and instance identity. Shared to
    /// keep recursive tactic syntax small.
    child_bindings: Option<std::sync::Arc<[(String, String, crate::kernel::InstanceId)]>>,
}

impl ResourceInstanceBinding {
    /// The instance this binding names. A binding of a named mutex live,
    /// use or guard authority names no instance, so a use that needs one
    /// (a field, a fold or unfold, a child, an instance argument) is refused.
    pub(crate) fn instance(&self) -> Result<crate::kernel::InstanceId, ClickError> {
        self.identity.instance().ok_or_else(|| {
            ClickError::new(format!(
                "`{}` names a mutex authority, not a resource instance",
                self.name
            ))
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ResourceFieldAccess {
    owner: String,
    resource_name: String,
    identity: crate::kernel::InstanceRef,
    children: Vec<String>,
    field: String,
    field_index: usize,
    click_type: Option<ClickType>,
}

impl ResourceFieldAccess {
    fn projected_name(&self) -> Option<String> {
        (!self.children.is_empty()
            || self.field_index == crate::kernel::ResourceFieldProjection::WITNESS)
            .then(|| self.field.clone())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum ResourceSubject {
    /// A resource descriptor evaluated in a recorded state.
    At {
        selector: ProgramPointSelector,
        resource: Box<ResourceSubject>,
    },
    Star(Box<ResourceSubject>, Box<ResourceSubject>),
    Emp,
    Instance {
        name: String,
        identity: crate::kernel::InstanceId,
        /// `at(point, name)`: the instance as it was held at that recorded
        /// state, for an instance the current state no longer holds.
        at: Option<ProgramPointSelector>,
    },
    Footprint(CodeRegionRef),
    Parameter {
        name: String,
        index: usize,
    },
    Captured {
        value: crate::kernel::Resource,
        source: Box<ResourceSubject>,
    },
    Memory(ContractSegment),
    /// A saved pointer base with bounds evaluated in the surrounding state.
    SavedMemory {
        base: ContractExpression,
        start: ContractExpression,
        /// None names one cell at `start`, without computing `start + 1`.
        end: Option<ContractExpression>,
    },
    Declared {
        kind: ResourceKind,
        name: String,
        arguments: Vec<ContractExpression>,
        parameter_types: Vec<InterfaceType>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ResourceAccessMode {
    Own,
    View,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ResourceKind {
    Composite,
    Token,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum SurfaceProposition {
    /// Assert a proposition-valued expression, such as a lambda application.
    Value(SurfaceTerm),
    Comparison {
        left: SurfaceTerm,
        operator: ComparisonOperator,
        right: SurfaceTerm,
    },
    FloatClassification {
        expression: SurfaceTerm,
        classification: syntax::CFloatClassification,
    },
    Separate {
        left: ResourceSubject,
        right: ResourceSubject,
    },
    Contains {
        parent: ResourceSubject,
        child: ResourceSubject,
    },
    ResourceViewable {
        resource: ResourceSubject,
    },
    Loadable {
        segment: ContractSegment,
    },
    /// `defined(e)`: the definedness special form. Unlike the point
    /// selectors `old`, `at` and `exact`, which are `SurfaceTerm`s, it is a
    /// proposition, and it lowers `e` keeping native address checks
    /// (`checking_definedness`). See `docs/reference/glossary.md#special-forms`.
    Defined {
        expression: SurfaceTerm,
    },
    /// `at(point, P)`: the `at` special form in proposition position, the
    /// whole proposition `P` stated at `point`. `SurfaceTerm::At` is the term
    /// position.
    At {
        selector: ProgramPointSelector,
        proposition: Box<SurfaceProposition>,
    },
    And(Box<SurfaceProposition>, Box<SurfaceProposition>),
    Or(Box<SurfaceProposition>, Box<SurfaceProposition>),
    Not(Box<SurfaceProposition>),
    Implies(Box<SurfaceProposition>, Box<SurfaceProposition>),
    ForAll {
        click_type: ClickType,
        /// The hygienic name used while lowering the body.
        name: SurfaceBinder,
        /// The source spelling retained when hygiene changes `name`.
        written_name: Option<String>,
        body: Box<SurfaceProposition>,
    },
    Exists {
        click_type: ClickType,
        /// The hygienic name used while lowering the body.
        name: SurfaceBinder,
        /// The source spelling retained when hygiene changes `name`.
        written_name: Option<String>,
        body: Box<SurfaceProposition>,
    },
    RangeAll {
        start: SurfaceTerm,
        end: SurfaceTerm,
        /// The hygienic name used while lowering the body.
        item: SurfaceBinder,
        /// The source spelling retained when hygiene changes `item`.
        written_item: Option<String>,
        body: Box<SurfaceProposition>,
    },
    RangeAny {
        start: SurfaceTerm,
        end: SurfaceTerm,
        /// The hygienic name used while lowering the body.
        item: SurfaceBinder,
        /// The source spelling retained when hygiene changes `item`.
        written_item: Option<String>,
        body: Box<SurfaceProposition>,
    },
    PredicateCall {
        name: String,
        arguments: Vec<SurfaceTerm>,
    },
    /// `is_a<T>(p)`: the object `p` points to is a `T`. It holds exactly
    /// where the proof has type evidence for `p`, such as a resource body's
    /// typed call or a typed parameter, and lowers to that evidence's fact.
    IsA {
        class: crate::kernel::effective_type::CAccessClass,
        pointer: SurfaceTerm,
    },
}

/// Compatibility name for [`SurfaceProposition`].
pub use self::SurfaceProposition as ClickProposition;

impl Clone for SurfaceProposition {
    fn clone(&self) -> Self {
        clone_click_proposition_iteratively(self)
    }
}

fn clone_click_proposition_atom(proposition: &ClickProposition) -> ClickProposition {
    match proposition {
        ClickProposition::Value(expression) => ClickProposition::Value(expression.clone()),

        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ClickProposition::Comparison {
            left: left.clone(),
            operator: *operator,
            right: right.clone(),
        },
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => ClickProposition::FloatClassification {
            expression: expression.clone(),
            classification: *classification,
        },
        ClickProposition::Separate { left, right } => ClickProposition::Separate {
            left: left.clone(),
            right: right.clone(),
        },
        ClickProposition::ResourceViewable { resource } => ClickProposition::ResourceViewable {
            resource: resource.clone(),
        },
        ClickProposition::Contains { parent, child } => ClickProposition::Contains {
            parent: parent.clone(),
            child: child.clone(),
        },
        ClickProposition::Loadable { segment } => ClickProposition::Loadable {
            segment: segment.clone(),
        },
        ClickProposition::Defined { expression } => ClickProposition::Defined {
            expression: expression.clone(),
        },
        ClickProposition::IsA { class, pointer } => ClickProposition::IsA {
            class: class.clone(),
            pointer: pointer.clone(),
        },
        ClickProposition::PredicateCall { name, arguments } => ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: arguments.clone(),
        },
        ClickProposition::At { .. }
        | ClickProposition::And(..)
        | ClickProposition::Or(..)
        | ClickProposition::Not(..)
        | ClickProposition::Implies(..)
        | ClickProposition::ForAll { .. }
        | ClickProposition::Exists { .. }
        | ClickProposition::RangeAll { .. }
        | ClickProposition::RangeAny { .. } => {
            unreachable!("structural propositions are cloned by the iterative traversal")
        }
    }
}

#[cfg(test)]
thread_local! {
    /// How many nodes [`clone_click_proposition_iteratively`] has copied on
    /// this thread: the scaling regressions' measure of copying.
    pub(crate) static CLICK_PROPOSITION_NODES_COPIED: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// The specification `bool` literal `true` or `false`: a C `bool` value,
/// exactly `1` or `0`.
pub(crate) fn bool_literal(value: bool) -> ContractExpression {
    ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::bool_constant(
        value,
    )))
}

/// The value of a `bool` literal written as `true` or `false`.
pub(crate) fn bool_literal_value(expression: &ContractExpression) -> Option<bool> {
    match expression {
        ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Bool(
            value,
        ))) => value.bool_constant_value(),
        _ => None,
    }
}

/// A `bool` value claimed as a proposition: `value == true`.
pub(crate) fn bool_truth(value: ContractExpression) -> ClickProposition {
    ClickProposition::Comparison {
        left: value,
        operator: ComparisonOperator::Equal,
        right: bool_literal(true),
    }
}

/// The truth value of a proposition written where a `bool` value is
/// expected. A claim `value == true` is `value` itself. Any other
/// proposition `p` is `if p { true } else { false }`, with each connective
/// opened into conditionals that test one atom, because a specification
/// conditional's value selects on one condition: `p and q` is
/// `if p { if q { true } else { false } } else { false }`, and `or`, `not`
/// and `implies` likewise. Opening a connective can repeat a branch, so the
/// result is bounded; a proposition past the bound is refused.
pub(crate) fn proposition_bool_value(
    proposition: ClickProposition,
) -> Result<ContractExpression, String> {
    const BOOL_VALUE_CONDITIONALS: usize = 256;
    fn branch(
        condition: ClickProposition,
        then_branch: ContractExpression,
        else_branch: ContractExpression,
        conditionals: &mut usize,
    ) -> Result<ContractExpression, String> {
        *conditionals += 1;
        if *conditionals > BOOL_VALUE_CONDITIONALS {
            return Err(format!(
                "a proposition used as a `bool` value opens into more than \
                 {BOOL_VALUE_CONDITIONALS} conditionals; name part of it with a `Bool` function"
            ));
        }
        match condition {
            ClickProposition::And(left, right) => {
                let then_branch = branch(*right, then_branch, else_branch.clone(), conditionals)?;
                branch(*left, then_branch, else_branch, conditionals)
            }
            ClickProposition::Or(left, right) => {
                let else_branch = branch(*right, then_branch.clone(), else_branch, conditionals)?;
                branch(*left, then_branch, else_branch, conditionals)
            }
            ClickProposition::Implies(left, right) => {
                let consequent = branch(*right, then_branch.clone(), else_branch, conditionals)?;
                branch(*left, consequent, then_branch, conditionals)
            }
            ClickProposition::Not(body) => branch(*body, else_branch, then_branch, conditionals),
            condition => Ok(ContractExpression::If {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            }),
        }
    }
    match proposition {
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } if bool_literal_value(&right) == Some(true) => Ok(left),
        // A written `true` or `false` is that literal value.
        ClickProposition::Value(literal) if bool_literal_value(&literal).is_some() => Ok(literal),
        proposition => branch(proposition, bool_literal(true), bool_literal(false), &mut 0),
    }
}

pub(crate) fn clone_click_proposition_iteratively(
    proposition: &ClickProposition,
) -> ClickProposition {
    enum Frame<'a> {
        Visit(&'a ClickProposition),
        BuildAt(ProgramPointSelector),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            click_type: ClickType,
            name: SurfaceBinder,
            written_name: Option<String>,
        },
        BuildExists {
            click_type: ClickType,
            name: SurfaceBinder,
            written_name: Option<String>,
        },
        BuildRangeAll {
            start: ContractExpression,
            end: ContractExpression,
            item: SurfaceBinder,
            written_item: Option<String>,
        },
        BuildRangeAny {
            start: ContractExpression,
            end: ContractExpression,
            item: SurfaceBinder,
            written_item: Option<String>,
        },
    }

    let mut frames = vec![Frame::Visit(proposition)];
    let mut values = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Visit(proposition) => {
                #[cfg(test)]
                CLICK_PROPOSITION_NODES_COPIED.with(|copied| copied.set(copied.get() + 1));
                match proposition {
                    ClickProposition::At {
                        selector,
                        proposition,
                    } => {
                        frames.push(Frame::BuildAt(selector.clone()));
                        frames.push(Frame::Visit(proposition));
                    }
                    ClickProposition::And(left, right) => {
                        frames.push(Frame::BuildAnd);
                        frames.push(Frame::Visit(right));
                        frames.push(Frame::Visit(left));
                    }
                    ClickProposition::Or(left, right) => {
                        frames.push(Frame::BuildOr);
                        frames.push(Frame::Visit(right));
                        frames.push(Frame::Visit(left));
                    }
                    ClickProposition::Not(body) => {
                        frames.push(Frame::BuildNot);
                        frames.push(Frame::Visit(body));
                    }
                    ClickProposition::Implies(left, right) => {
                        frames.push(Frame::BuildImplies);
                        frames.push(Frame::Visit(right));
                        frames.push(Frame::Visit(left));
                    }
                    ClickProposition::ForAll {
                        click_type,
                        name,
                        written_name,
                        body,
                    } => {
                        frames.push(Frame::BuildForAll {
                            click_type: click_type.clone(),
                            name: name.clone(),
                            written_name: written_name.clone(),
                        });
                        frames.push(Frame::Visit(body));
                    }
                    ClickProposition::Exists {
                        click_type,
                        name,
                        written_name,
                        body,
                    } => {
                        frames.push(Frame::BuildExists {
                            click_type: click_type.clone(),
                            name: name.clone(),
                            written_name: written_name.clone(),
                        });
                        frames.push(Frame::Visit(body));
                    }
                    ClickProposition::RangeAll {
                        start,
                        end,
                        item,
                        written_item,
                        body,
                    } => {
                        frames.push(Frame::BuildRangeAll {
                            start: start.clone(),
                            end: end.clone(),
                            item: item.clone(),
                            written_item: written_item.clone(),
                        });
                        frames.push(Frame::Visit(body));
                    }
                    ClickProposition::RangeAny {
                        start,
                        end,
                        item,
                        written_item,
                        body,
                    } => {
                        frames.push(Frame::BuildRangeAny {
                            start: start.clone(),
                            end: end.clone(),
                            item: item.clone(),
                            written_item: written_item.clone(),
                        });
                        frames.push(Frame::Visit(body));
                    }
                    atomic => values.push(clone_click_proposition_atom(atomic)),
                }
            }
            Frame::BuildAt(selector) => {
                let proposition = values.pop().expect("the anchored proposition is cloned");
                values.push(ClickProposition::At {
                    selector,
                    proposition: Box::new(proposition),
                });
            }
            Frame::BuildAnd => {
                let right = values.pop().expect("the right proposition is cloned");
                let left = values.pop().expect("the left proposition is cloned");
                values.push(ClickProposition::And(Box::new(left), Box::new(right)));
            }
            Frame::BuildOr => {
                let right = values.pop().expect("the right proposition is cloned");
                let left = values.pop().expect("the left proposition is cloned");
                values.push(ClickProposition::Or(Box::new(left), Box::new(right)));
            }
            Frame::BuildNot => {
                let body = values.pop().expect("the proposition body is cloned");
                values.push(ClickProposition::Not(Box::new(body)));
            }
            Frame::BuildImplies => {
                let right = values.pop().expect("the implication consequent is cloned");
                let left = values.pop().expect("the implication antecedent is cloned");
                values.push(ClickProposition::Implies(Box::new(left), Box::new(right)));
            }
            Frame::BuildForAll {
                click_type,
                name,
                written_name,
            } => {
                let body = values.pop().expect("the forall body is cloned");
                values.push(ClickProposition::ForAll {
                    click_type,
                    name,
                    written_name,
                    body: Box::new(body),
                });
            }
            Frame::BuildExists {
                click_type,
                name,
                written_name,
            } => {
                let body = values.pop().expect("the exists body is cloned");
                values.push(ClickProposition::Exists {
                    click_type,
                    name,
                    written_name,
                    body: Box::new(body),
                });
            }
            Frame::BuildRangeAll {
                start,
                end,
                item,
                written_item,
            } => {
                let body = values.pop().expect("the range-all body is cloned");
                values.push(ClickProposition::RangeAll {
                    start,
                    end,
                    item,
                    written_item,
                    body: Box::new(body),
                });
            }
            Frame::BuildRangeAny {
                start,
                end,
                item,
                written_item,
            } => {
                let body = values.pop().expect("the range-any body is cloned");
                values.push(ClickProposition::RangeAny {
                    start,
                    end,
                    item,
                    written_item,
                    body: Box::new(body),
                });
            }
        }
    }
    values.pop().expect("the root proposition is cloned")
}

impl Clone for TheoremDefinition {
    fn clone(&self) -> Self {
        clone_theorem_definition_iteratively(self)
    }
}

#[cfg(test)]
thread_local! {
    static THEOREM_DEFINITION_COPIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn theorem_definition_copies() -> usize {
    THEOREM_DEFINITION_COPIES.with(std::cell::Cell::get)
}

pub(crate) fn clone_theorem_definition_iteratively(
    theorem: &TheoremDefinition,
) -> TheoremDefinition {
    #[cfg(test)]
    THEOREM_DEFINITION_COPIES.with(|copies| copies.set(copies.get() + 1));
    TheoremDefinition {
        axiom: theorem.axiom,
        generic_pointer_parameters: theorem.generic_pointer_parameters.clone(),
        body: theorem.body.clone(),
        name: theorem.name.clone(),
        type_parameters: theorem.type_parameters.clone(),
        parameters: theorem.parameters.clone(),
        executes: theorem.executes.clone(),
        requires: theorem
            .requires
            .iter()
            .map(clone_requirement_iteratively)
            .collect(),
        ensures: theorem
            .ensures
            .iter()
            .map(clone_ensure_clause_iteratively)
            .collect(),
        ensure_claim_ids: theorem.ensure_claim_ids.clone(),
    }
}

fn clone_requirement_iteratively(requirement: &Requirement) -> Requirement {
    match requirement {
        Requirement::Proposition(proposition) => {
            Requirement::Proposition(clone_click_proposition_iteratively(proposition))
        }
        requirement => requirement.clone(),
    }
}

fn clone_ensure_clause_iteratively(clause: &EnsureClause) -> EnsureClause {
    EnsureClause {
        proof_bindings: clause.proof_bindings.clone(),
        name: clause.name.clone(),
        ensure: match &clause.ensure {
            Ensure::Proposition(proposition) => {
                Ensure::Proposition(clone_click_proposition_iteratively(proposition))
            }
            ensure => ensure.clone(),
        },
        proof: clause.proof.clone(),
        borrowed: clause.borrowed,
        view_source: clause.view_source,
        condition: clause.condition.clone(),
    }
}

impl SurfaceProposition {
    fn written_quantifier_name(&self) -> Option<&str> {
        match self {
            Self::ForAll { written_name, .. } | Self::Exists { written_name, .. } => {
                written_name.as_deref()
            }
            Self::RangeAll { written_item, .. } | Self::RangeAny { written_item, .. } => {
                written_item.as_deref()
            }
            _ => None,
        }
    }
}

pub(crate) fn collect_program_expression_variables(
    expression: &ProgramExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Variable(name) => {
            if let Some(name) = name.named() {
                names.insert(name.to_owned());
            }
        }
        ProgramExpression::Cast { expression, .. } => {
            collect_program_expression_variables(expression, names);
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        } => {
            collect_program_expression_variables(expression, names);
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_program_expression_variables(field, names);
            }
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_variables(condition, names);
            collect_program_expression_variables(then_branch, names);
            collect_program_expression_variables(else_branch, names);
        }
        ProgramExpression::AddressOf(inner)
        | ProgramExpression::CheckedObjectAddress(inner)
        | ProgramExpression::PointerOffsetBytes { pointer: inner, .. }
        | ProgramExpression::Subobject { pointer: inner, .. }
        | ProgramExpression::Not(inner)
        | ProgramExpression::BitwiseNot(inner)
        | ProgramExpression::Load(inner)
        | ProgramExpression::TypedLoad { pointer: inner, .. } => {
            collect_program_expression_variables(inner, names);
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_program_expression_variables(left, names);
            collect_program_expression_variables(right, names);
        }
    }
}

fn collect_current_segment_variables(segment: &ContractSegment, names: &mut BTreeSet<String>) {
    if segment.state != ContractSegmentState::Current {
        return;
    }
    collect_program_expression_variables(&segment.base, names);
    collect_program_expression_variables(&segment.start, names);
    collect_program_expression_variables(&segment.end, names);
}

fn collect_current_resource_clause_variables(
    resource: &ResourceClause,
    names: &mut BTreeSet<String>,
) {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => {
            collect_current_proposition_variables(condition, names);
            collect_current_resource_clause_variables(resource, names);
        }
        ResourceClause::Named { resource, .. } => {
            collect_current_resource_clause_variables(resource, names)
        }
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            collect_current_segment_variables(segment, names);
        }
        ResourceClause::MemoryAggregate { segments, .. } => {
            for segment in segments {
                collect_current_segment_variables(segment, names);
            }
        }
        ResourceClause::Quantified { quantity, resource } => {
            collect_current_contract_expression_variables(quantity, names);
            collect_current_resource_clause_variables(resource, names);
        }
        ResourceClause::Declared {
            arguments,
            resource_type_arguments,
            ..
        } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
            for resource in resource_type_arguments {
                collect_current_resource_clause_variables(resource, names);
            }
        }
        ResourceClause::Iterated(clause) => {
            let mut inner = BTreeSet::new();
            collect_current_segment_variables(&clause.element, &mut inner);
            collect_current_proposition_variables(&clause.range, &mut inner);
            if let Some(guard) = &clause.guard {
                collect_current_proposition_variables(guard, &mut inner);
            }
            if let Some(name) = clause.binder.written() {
                inner.remove(name);
            }
            names.extend(inner);
        }
    }
}

fn collect_current_resource_subject_variables(
    subject: &ResourceSubject,
    names: &mut BTreeSet<String>,
) {
    match subject {
        ResourceSubject::At { .. } => {}
        ResourceSubject::Emp => (),
        ResourceSubject::Star(left, right) => {
            collect_current_resource_subject_variables(left, names);
            collect_current_resource_subject_variables(right, names);
        }
        ResourceSubject::Footprint(_) => {}
        ResourceSubject::Parameter { name, .. } | ResourceSubject::Instance { name, .. } => {
            names.insert(name.clone());
        }
        ResourceSubject::Captured { .. } => {}
        ResourceSubject::Memory(segment) => collect_current_segment_variables(segment, names),
        ResourceSubject::SavedMemory { base, start, end } => {
            for expression in [base, start].into_iter().chain(end.iter()) {
                collect_current_contract_expression_variables(expression, names);
            }
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
    }
}

pub(crate) fn collect_current_contract_expression_variables(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::IntegerContext(value) => {
            collect_current_contract_expression_variables(value, names)
        }

        ContractExpression::Proposition(proposition) => {
            collect_current_proposition_variables(proposition, names)
        }
        ContractExpression::Resource(subject) => {
            collect_current_resource_subject_variables(subject, names)
        }
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => {}
        ContractExpression::Lambda {
            parameters, body, ..
        } => {
            let mut captures = BTreeSet::new();
            collect_current_contract_expression_variables(body, &mut captures);
            for (name, _) in parameters {
                if let Some(name) = name.written() {
                    captures.remove(name);
                }
            }
            names.extend(captures);
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            collect_current_contract_expression_variables(function, names);
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }

        ContractExpression::ResourceField(_) | ContractExpression::IntegerLiteral(_) => {}
        ContractExpression::AlgebraicVariable { name, .. } => {
            if let Some(name) = name.written() {
                names.insert(name.to_owned());
            }
        }
        ContractExpression::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_current_contract_expression_variables(scrutinee, names);
            for arm in arms {
                let mut arm_names = BTreeSet::new();
                collect_current_contract_expression_variables(&arm.body, &mut arm_names);
                for binding in &arm.bindings {
                    if let Some(name) = binding.written() {
                        arm_names.remove(name);
                    }
                }
                names.extend(arm_names);
            }
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                collect_current_contract_expression_variables(element, names);
            }
        }
        ContractExpression::SequenceConcat(left, right) => {
            collect_current_contract_expression_variables(left, names);
            collect_current_contract_expression_variables(right, names);
        }
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::ProgramExpression(expression) => {
            collect_program_expression_variables(expression, names);
        }
        // A `program::name` base is skipped like a bare `program::name`: its
        // lowered C form names the same binding, not a Click value such as
        // the contract `result`.
        ContractExpression::Field { base, lowered, .. } => {
            collect_current_contract_expression_variables(base, names);
            if !matches!(base.as_ref(), ContractExpression::ProgramBinding(_)) {
                collect_program_expression_variables(lowered, names);
            }
        }
        ContractExpression::ArrayIndex {
            base,
            indexes,
            lowered,
            ..
        } => {
            collect_current_contract_expression_variables(base, names);
            for index in indexes {
                collect_current_contract_expression_variables(index, names);
            }
            if !matches!(base.as_ref(), ContractExpression::ProgramBinding(_)) {
                collect_program_expression_variables(lowered, names);
            }
        }
        ContractExpression::Binding(name) => {
            names.insert(name.clone());
        }
        ContractExpression::ProgramBinding(_) | ContractExpression::ResourceWildcard => {}
        ContractExpression::ResourceCount(resource) => {
            collect_current_resource_clause_variables(resource, names);
        }
        // Explicitly anchored expressions are stable across a local write.
        ContractExpression::Old(_) | ContractExpression::At { .. } => {}
        ContractExpression::BitwiseNot(inner) => {
            collect_current_contract_expression_variables(inner, names);
        }
        ContractExpression::CUnary { operand: inner, .. }
        | ContractExpression::MemoryLoad { pointer: inner, .. }
        | ContractExpression::Negate(inner)
        | ContractExpression::Exact(inner) => {
            collect_current_contract_expression_variables(inner, names);
        }
        crate::surface::binary_contract_expression!(left, right) => {
            collect_current_contract_expression_variables(left, names);
            collect_current_contract_expression_variables(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_current_proposition_variables(condition, names);
            collect_current_contract_expression_variables(then_branch, names);
            collect_current_contract_expression_variables(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_current_contract_expression_variables(start, names);
            collect_current_contract_expression_variables(end, names);
            collect_current_contract_expression_variables(initial, names);
            collect_current_contract_expression_variables(body, names);
        }
        ContractExpression::Let { value, body, .. } => {
            collect_current_contract_expression_variables(value, names);
            collect_current_contract_expression_variables(body, names);
        }
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            collect_current_contract_expression_variables(receiver, names);
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
    }
}

fn collect_current_proposition_variables(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::Value(expression) => {
                collect_current_contract_expression_variables(expression, names)
            }

            ClickProposition::Comparison { left, right, .. } => {
                collect_current_contract_expression_variables(left, names);
                collect_current_contract_expression_variables(right, names);
            }
            ClickProposition::FloatClassification { expression, .. } => {
                collect_current_contract_expression_variables(expression, names);
            }
            ClickProposition::ResourceViewable { resource } => {
                collect_current_resource_subject_variables(resource, names)
            }
            ClickProposition::Separate { left, right }
            | ClickProposition::Contains {
                parent: left,
                child: right,
            } => {
                collect_current_resource_subject_variables(left, names);
                collect_current_resource_subject_variables(right, names);
            }
            ClickProposition::Loadable { segment } => {
                collect_current_segment_variables(segment, names);
            }
            ClickProposition::Defined { expression }
            | ClickProposition::IsA {
                pointer: expression,
                ..
            } => {
                collect_current_contract_expression_variables(expression, names);
            }
            // The proposition itself is anchored, so current-local writes cannot
            // change its meaning even if its body contains a C fragment.
            ClickProposition::At { .. } => {}
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            ClickProposition::Not(body)
            | ClickProposition::ForAll { body, .. }
            | ClickProposition::Exists { body, .. } => {
                pending.push(body);
            }
            ClickProposition::RangeAll {
                start, end, body, ..
            }
            | ClickProposition::RangeAny {
                start, end, body, ..
            } => {
                collect_current_contract_expression_variables(start, names);
                collect_current_contract_expression_variables(end, names);
                pending.push(body);
            }
            ClickProposition::PredicateCall { arguments, .. } => {
                for argument in arguments {
                    collect_current_contract_expression_variables(argument, names);
                }
            }
        }
    }
}

/// Compatibility name while expression consumers migrate to `SurfaceTerm`.
mod binders;
pub use binders::SurfaceBinder;
use binders::{BinderMap, BinderSet, PersistentBinderMap, ScopedBinders};

pub type ContractExpression = SurfaceTerm;

/// The library function a Rust subslice's length lowers through; its call
/// owes the subslice's bounds.
pub(crate) const RUST_SUBSLICE_LEN: &str = "click::rust::slice::subslice_len";

/// Source expressions shared by declarations, proof claims and raised terms.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SurfaceTerm {
    Resource(Box<ResourceSubject>),
    /// An unsuffixed decimal retained until specification type checking. The
    /// same source spelling can denote a C literal or an exact Integer when
    /// its surrounding expression supplies that context.
    IntegerLiteral(String),
    /// Mathematical Integer type context, written `(value : Integer)`.
    IntegerContext(Box<SurfaceTerm>),
    /// A translation-unit-qualified C object. Retain its spelling for checked
    /// proof expansion while lowering its stable storage identity, not a local.
    QualifiedC {
        name: String,
        lowered: ProgramExpression,
    },
    ResourceField(ResourceFieldAccess),
    /// A fully type-applied constructor of a specification-only algebraic
    /// datatype. The first slice permits C scalar and data-pointer fields.
    AlgebraicConstructor {
        algebraic_type: AlgebraicTypeApplication,
        variant: String,
        arguments: Vec<ContractExpression>,
    },
    /// A method call on a value of a Click type, `s.len()`, as written: its
    /// meaning comes from the receiver's type, so declaration expansion
    /// resolves it once types are known
    /// (`design/typed-method-resolution.md`). An index `s[i]` and a range
    /// index `s[a..b]` on such a receiver are the methods `[]` and `[..]`,
    /// `[a..]`, `[..b]` or `[a..b]`, with the written bounds as arguments.
    MethodCall {
        receiver: Box<ContractExpression>,
        method: String,
        arguments: Vec<ContractExpression>,
    },
    /// A Click-native binder whose value is not a C object or scalar.
    AlgebraicVariable {
        name: SurfaceBinder,
        algebraic_type: AlgebraicTypeApplication,
        binder_index: usize,
    },
    /// A bare source-level name whose Click type is resolved from its lexical
    /// environment. Unlike `ProgramBinding`, this can denote either a C value or a
    /// specification-only value such as an algebraic datatype.
    Binding(String),
    /// Exhaustive elimination of an algebraic value. Its arms may produce a
    /// common C or algebraic result type.
    AlgebraicMatch {
        scrutinee: Box<ContractExpression>,
        arms: Vec<AlgebraicMatchArm>,
    },
    /// An immutable, finite specification sequence. Elements remain ordinary
    /// scalar contract expressions and are evaluated at the surrounding
    /// state.
    SequenceLiteral(Vec<ContractExpression>),
    /// Persistent sequence concatenation. This is specification syntax only;
    /// it does not denote C pointer arithmetic or allocate C memory.
    SequenceConcat(Box<ContractExpression>, Box<ContractExpression>),
    /// A C expression fragment appearing inside Surface Click.
    ProgramExpression(ProgramExpression),
    /// A typed read in the surrounding memory. The pointer expression may
    /// select an address in a different state.
    MemoryLoad {
        pointer: Box<SurfaceTerm>,
        value_type: ProgramType,
        volatile: bool,
        pointee_constant: bool,
    },
    /// A C unary operation whose operand retains source and binding syntax.
    /// Scalar casts and typed loads may also wrap a pure or historical expression. `operand` is authoritative;
    /// in that case `lowered` retains the cast metadata with a placeholder, and
    /// conversion back to a C fragment must rebuild from `operand` or refuse.
    CUnary {
        operand: Box<ContractExpression>,
        lowered: ProgramExpression,
    },
    /// A source-level struct field place paired with its lowered C expression.
    ///
    /// The source place is retained for certificates and diagnostics; only
    /// `lowered` crosses into semantic checking.
    Field {
        /// Declared struct identity of a pointer-valued field, retained for
        /// nominal type validation independently of its scalar C carrier.
        pointee_struct: Option<String>,
        base: Box<ContractExpression>,
        field: String,
        lowered: ProgramExpression,
        /// Byte offset of `field` from the address denoted by `base`.
        /// Keeping this separately lets lowering rebuild the field load when
        /// `base` is evaluated in a different state from the field value.
        /// A number, or in a symbolic layout the field's `offsetof` term.
        offset_bytes: crate::kernel::LayoutOffset,
    },
    /// `program::name`: a binding from the verified program function's
    /// lexical environment, in any source language.
    ///
    /// This is distinct from contract built-ins such as bare `result`, even
    /// when the program binding has the same source name.
    ProgramBinding(String),
    /// The authoritative population count of one instantiated counted
    /// resource family. This expression is only meaningful while the
    /// family's population body is in scope.
    ResourceCount(Box<ResourceClause>),
    /// A wildcard argument inside the resource pattern accepted by
    /// `count(...)`. It is never a standalone contract expression.
    ResourceWildcard,
    /// The value a region produced, written `<region>.result`: for a call's
    /// region, the call's result. A region has `entry` and `exit` points and
    /// this one value; it is the result its region assigned, read at the
    /// region's exit.
    RegionResult(CodeRegionRef),
    /// The fresh heap identity of an allocation region, distinct from its nullable result.
    RegionAllocation(CodeRegionRef),
    /// A by-value aggregate parameter of a call's region as the call bound
    /// it, written `<region>.parameter(name)`: the callee's copy of the
    /// argument, read at the memory just after the copy. It is an object;
    /// a field or element of it is read through it, `R.parameter(v).f[0]`.
    RegionParameter {
        region: CodeRegionRef,
        name: String,
    },
    /// `old(e)`: a point-selecting special form, sugar for
    /// `at(function.entry, e)`. The special forms are `old`, `at`, `exact`
    /// and `defined` (`ClickProposition::Defined`); see
    /// `docs/reference/glossary.md#special-forms`.
    Old(Box<ContractExpression>),
    /// `at(point, e)`: a point-selecting special form, `e` read when the
    /// proof path was at `point`. `ClickProposition::At` is the same form in
    /// proposition position.
    At {
        selector: ProgramPointSelector,
        expression: Box<ContractExpression>,
    },
    /// `exact(place)`, a point-selecting special form: the read of `place`
    /// named by the state in scope itself, with no version walk
    /// (`design/exact-reads.md`). It applies to the outermost read only;
    /// reads computing the place's address stay ordinary. It grants no
    /// access and adds no facts.
    Exact(Box<ContractExpression>),
    Negate(Box<ContractExpression>),
    Add(Box<ContractExpression>, Box<ContractExpression>),
    Subtract(Box<ContractExpression>, Box<ContractExpression>),
    Multiply(Box<ContractExpression>, Box<ContractExpression>),
    Divide(Box<ContractExpression>, Box<ContractExpression>),
    Remainder(Box<ContractExpression>, Box<ContractExpression>),
    ShiftLeft(Box<ContractExpression>, Box<ContractExpression>),
    /// Rust shifts preserve the operand width and owe only count bounds.
    RustShiftLeft(Box<ContractExpression>, Box<ContractExpression>),
    RustShiftRight(Box<ContractExpression>, Box<ContractExpression>),
    ShiftRight(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseAnd(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseOr(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseXor(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseNot(Box<ContractExpression>),
    Index(Box<ContractExpression>, Box<ContractExpression>),
    /// A multidimensional C array access. `lowered` carries the flattened
    /// pointer access used by the kernel while `indexes` retain their binding
    /// syntax and source rank. Dimensions recover the row-major strides when
    /// the source operands need separate namespace lowering.
    ArrayIndex {
        base: Box<ContractExpression>,
        indexes: Vec<ContractExpression>,
        dimensions: Vec<u32>,
        lowered: ProgramExpression,
    },
    If {
        condition: Box<ClickProposition>,
        then_branch: Box<ContractExpression>,
        else_branch: Box<ContractExpression>,
    },
    /// A proposition carried as a specification value.
    Proposition(Box<ClickProposition>),
    /// A typed, lexically scoped specification function; reads use application state.
    Lambda {
        parameters: Vec<(SurfaceBinder, ClickType)>,
        result: ClickType,
        body: Box<ContractExpression>,
    },
    /// Application of an expression whose value is a specification function.
    Apply {
        function: Box<ContractExpression>,
        arguments: Vec<ContractExpression>,
    },
    RangeFold {
        start: Box<ContractExpression>,
        end: Box<ContractExpression>,
        initial: Box<ContractExpression>,
        accumulator: SurfaceBinder,
        item: SurfaceBinder,
        body: Box<ContractExpression>,
    },
    Let {
        name: SurfaceBinder,
        click_type: Option<ClickType>,
        value: Box<ContractExpression>,
        body: Box<ContractExpression>,
    },
    Call {
        name: String,
        arguments: Vec<ContractExpression>,
    },
}

/// Matches every arithmetic, bitwise and indexing binary [`ContractExpression`], binding the
/// operands to `$left` and `$right`.
macro_rules! binary_contract_expression {
    ($left:pat, $right:pat) => {
        $crate::surface::ContractExpression::Add($left, $right)
            | $crate::surface::ContractExpression::Subtract($left, $right)
            | $crate::surface::ContractExpression::Multiply($left, $right)
            | $crate::surface::ContractExpression::Divide($left, $right)
            | $crate::surface::ContractExpression::Remainder($left, $right)
            | $crate::surface::ContractExpression::BitwiseAnd($left, $right)
            | $crate::surface::ContractExpression::BitwiseOr($left, $right)
            | $crate::surface::ContractExpression::BitwiseXor($left, $right)
            | $crate::surface::ContractExpression::ShiftLeft($left, $right)
            | $crate::surface::ContractExpression::RustShiftLeft($left, $right)
            | $crate::surface::ContractExpression::ShiftRight($left, $right)
            | $crate::surface::ContractExpression::RustShiftRight($left, $right)
            | $crate::surface::ContractExpression::Index($left, $right)
    };
}
pub(crate) use binary_contract_expression;

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClickArrayRef {
    point: crate::kernel::ProgramPoint,
    pointer: Address,
    element_type: ProgramType,
}

type ClickArrayRefs = BTreeMap<String, ClickArrayRef>;

/// The names a contract expression reads: scalar values and array
/// references, as `contract_environment_at_state` builds them.
#[derive(Clone, Copy)]
struct ContractEnvironment<'a> {
    values: &'a ProgramValueBindings,
    array_refs: &'a ClickArrayRefs,
    parameters: ParameterBinding<'a>,
}

impl<'a> ContractEnvironment<'a> {
    fn new(values: &'a ProgramValueBindings, array_refs: &'a ClickArrayRefs) -> Self {
        Self {
            values,
            array_refs,
            parameters: ParameterBinding::default(),
        }
    }
    fn with_parameters(self, parameters: ParameterBinding<'a>) -> Self {
        Self { parameters, ..self }
    }
    /// Ordinal lookup is checked against the exact prepared declaration: another
    /// function's parameter with the same spelling never acquires this value.
    fn parameter_value(self, binding: &crate::kernel::BindingName) -> Option<&'a ProgramValue> {
        if let Some(slice) = binding.slice_length_of() {
            if let Some(index) = self.parameters.index {
                let position = index.slice_length_position(slice)?;
                if self.parameters.parameters.get(position)?.binding_name() != binding {
                    return None;
                }
                let ProgramExpression::Value(value) = self.parameters.arguments.get(position)?
                else {
                    return None;
                };
                return Some(value);
            }
            return self.values.get(binding.source_name());
        }
        if let Some(referent) = binding.reference_referent() {
            if let Some(index) = self.parameters.index {
                let position = index.position(referent.source_name())?;
                let parameter = self.parameters.parameters.get(position)?;
                if !parameter.matches_binding(binding) {
                    return None;
                }
                let ProgramExpression::Value(value) = self.parameters.arguments.get(position)?
                else {
                    return None;
                };
                return Some(value);
            }
            // An unresolved carrier uses the explicit source-parameter value
            // table, just as an unresolved ordinary parameter does. This is
            // a source name lookup, never decoding a fabricated identifier.
            if let Some(name) = referent.named() {
                return self.values.get(name);
            }
        }
        let id = binding
            .local_id()
            .or_else(|| binding.reference_referent()?.local_id())?;
        if !id.is_parameter() {
            return None;
        }
        crate::instrumentation::record_deterministic_work(1);
        let position = id.ordinal() as usize;
        let parameter = self.parameters.parameters.get(position)?;
        if parameter.binding_name() != binding {
            return None;
        }
        let ProgramExpression::Value(value) = self.parameters.arguments.get(position)? else {
            return None;
        };
        Some(value)
    }
}
/// Ordinary parameters use their source identifier in the current scope.
/// A reference carrier or slice length retains its typed binding so it raises
/// as `&x` or `x.len()`.
fn surface_parameter_binding(binding: &crate::kernel::BindingName) -> crate::kernel::BindingName {
    if binding.reference_referent().is_some() || binding.slice_length_of().is_some() {
        binding.clone()
    } else {
        binding.source_name().into()
    }
}

/// The identity of a symbolic model-field value, independent of its carrier.
fn model_field_variable<'a>(
    value: impl Into<crate::kernel::ResourceFieldValue<'a>>,
) -> Option<crate::kernel::Variable> {
    use crate::kernel::{AlgebraicTermNode, MachineTerm};
    match value.into() {
        crate::kernel::ResourceFieldValue::Algebraic(term) => match term.node {
            AlgebraicTermNode::Variable(variable) => Some(variable),
            _ => None,
        },
        crate::kernel::ResourceFieldValue::Program(ProgramValue::Parameter(term)) => {
            match term.node {
                AlgebraicTermNode::Variable(variable) => Some(variable),
                _ => None,
            }
        }
        crate::kernel::ResourceFieldValue::Program(
            crate::kernel::integer_c_value!(MachineTerm::Variable(variable)),
        ) => Some(*variable),
        _ => None,
    }
}

fn instance_holds_field_value(
    state: &ExecutionState,
    identity: crate::kernel::InstanceId,
    field_index: usize,
    variable: crate::kernel::Variable,
) -> bool {
    state
        .resource_instance_fields(identity)
        .and_then(|instance| instance.fields().get(field_index))
        .is_some_and(|field| model_field_variable(field) == Some(variable))
}

/// How many recorded points whose memory held a value's fingerprint the
/// raiser tries.
const CELL_POINTS_OFFERED: usize = 4;

/// How many recorded points holding a pointer's block the raiser tries.
const POINTER_POINTS_OFFERED: usize = 4;

type ReadEventNames<T> =
    crate::persistent::PersistentMap<T, crate::persistent::PersistentSet<(usize, usize)>>;

/// A position in a path's recorded history.
#[derive(Clone, Default)]
struct RecordedHistoryMark(Option<std::sync::Arc<RecordedStateChange>>);

type RecordedCallResults = crate::persistent::PersistentMap<usize, RetainedProgramValue>;

/// Points one path recorded at a range of regions, with their call results.
#[derive(Clone, Default)]
struct RecordedRegionPoints {
    retained_states: Vec<(
        ProgramPointSelector,
        ExecutionState,
        Option<RecordedCallResults>,
    )>,
    call_results: Vec<(usize, RetainedProgramValue)>,
}

#[derive(Default)]
struct EntrySeparationSources {
    facts: Vec<Proposition>,
    ranges: BTreeMap<MemoryRange, ContractSegment>,
}

#[derive(Clone)]
struct RecordedStates {
    /// Source ranges from the contract's checked incoming resource section.
    /// A proof mark at this point can cite their exact pre-copy terms.
    entry_separation_sources: Option<(
        crate::kernel::program_point::ProgramPointId,
        std::sync::Arc<EntrySeparationSources>,
    )>,
    effect_log: imbl::Vector<crate::kernel::Resource>,
    effect_gaps: imbl::Vector<usize>,
    effect_offsets: imbl::OrdMap<ProgramPointSelector, usize>,
    footprint_values: std::sync::Arc<
        std::sync::Mutex<
            std::collections::HashMap<
                (
                    ProgramPointSelector,
                    ProgramPointSelector,
                    usize,
                    usize,
                    Option<crate::kernel::Resource>,
                    crate::kernel::SharedMemory,
                    crate::kernel::SharedMemory,
                ),
                crate::kernel::Resource,
            >,
        >,
    >,
    version: std::sync::Arc<RecordedStateVersion>,
    /// A temporary interface lowering scope reads marks from the common
    /// tree without exposing its incidental program points.
    interface_marks: Option<std::sync::Arc<RecordedInterfaceMarks>>,
    /// The labels the proof gave loops on this path. A program point is
    /// recorded once, under its loop's first label when it has one and as
    /// `loop(N)` otherwise; a lookup by either spelling, or by another label
    /// of the same loop, reads that one entry.
    loop_labels: Option<std::sync::Arc<LoopLabels>>,
    /// The function's source layout, through which a path through the
    /// statements as written, such as `statement(2).exit`, is spelled as the
    /// `region(N)` point it is recorded at.
    source_layout: Option<lowering::SourceExecutionLayout>,
    /// The name of each recorded point, by the identity of the point its
    /// state's path reached there ([`crate::kernel::ProgramPoint`]): a
    /// direct lookup, independent of what the memory there holds.
    point_names: imbl::HashMap<crate::kernel::program_point::ProgramPointId, ProgramPointSelector>,
    /// The newest recorded point whose memory reads each set of program
    /// bytes, keyed by the memory's read identity. A load registered in a
    /// memory other than the one being spelled is looked up here and
    /// spelled `at(point, ...)` in one step, instead of trying recorded
    /// states in turn. Ordered, because identities are made in program
    /// order: a load registered in a memory between recorded points is read
    /// at the first recorded memory after it.
    memory_points: imbl::OrdMap<(u32, u32), ProgramPointSelector>,
    /// The recorded point at which each scalar local first held each integer
    /// value, keyed like the locals' held-term index by the value's
    /// fingerprint and the local's name. A value no nearer state names is
    /// spelled `at(point, local)` from here in one lookup. Entries are made
    /// from the locals each insert changed, and checked against the point's
    /// state when read.
    value_points:
        crate::persistent::PersistentMap<(u64, crate::kernel::BindingName), ProgramPointSelector>,
    /// The recorded point at which each local first held a pointer into
    /// each block, keyed by the block and the local's name: a pointer no
    /// nearer state names is spelled at such a point, from that local.
    /// Filled and checked as `value_points` is.
    pointer_points: crate::persistent::PersistentMap<
        (crate::kernel::AddressBase, crate::kernel::BindingName),
        ProgramPointSelector,
    >,
    /// Allocation results keep the region that introduced them, independently
    /// of later pointer reads or assignments to the result local.
    allocation_results: crate::persistent::PersistentMap<crate::kernel::Address, CodeRegionRef>,
    /// Values produced at call exits, independent of destination locals.
    call_results: RecordedCallResults,
    /// Prelowered result steps retain their result table at each citable
    /// state. An `at` expression selects a table by its program point.
    call_result_snapshots: imbl::OrdMap<ProgramPointSelector, RecordedCallResults>,
    /// The points inside a loop that left at several places, by the loop
    /// and its number of leaving paths: each path recorded the point at its
    /// own state, so after the loop the name has no one state.
    ambiguous_exit_points: crate::persistent::PersistentMap<ProgramPointSelector, (usize, usize)>,
    call_result_points: crate::persistent::PersistentMap<(u64, usize), ()>,
    read_event_results: crate::persistent::PersistentMap<(usize, usize), RetainedProgramValue>,
    read_event_counts: crate::persistent::PersistentMap<usize, usize>,
    read_event_names: ReadEventNames<ProgramValue>,
    read_event_scalar_names: ReadEventNames<crate::kernel::MachineTerm>,
    read_event_pointer_names: ReadEventNames<crate::kernel::Address>,
    /// The call that produced each algebraic value a call returned, a Rust
    /// enum's: the value is spelled `<region>.result`.
    algebraic_call_results: crate::persistent::PersistentMap<crate::kernel::AlgebraicTerm, usize>,
    /// The call that produced each pointer a call returned, by the
    /// pointer's address: the value is spelled `<region>.result`, which
    /// lowers to the exact returned value.
    pointer_call_results: crate::persistent::PersistentMap<crate::kernel::Address, usize>,
    /// Each exited loop's pass count, the head's `iterations`, which the
    /// facts past the loop state over: spelled `loop(i).iterations`.
    loop_iterations: crate::persistent::PersistentMap<usize, crate::kernel::KernelTerm>,
    /// The loop whose pass count each variable is: one lookup spells it.
    loop_iteration_variables: crate::persistent::PersistentMap<crate::kernel::Variable, usize>,
    /// The recorded point at which each scalar model-field value was first
    /// held by its resource instance, keyed by the value's variable: a field
    /// value no nearer state's instance holds is spelled at that point.
    /// Filled from the instances each insert changed, and checked against
    /// the point's state when read.
    field_points: crate::persistent::PersistentMap<crate::kernel::Variable, ProgramPointSelector>,
    /// The locals of the state inserted last, against which the next insert
    /// finds the locals it changed.
    last_locals: Option<crate::kernel::LocalEnvironment>,
    /// The resources of the state inserted last, against which the next
    /// insert finds the instances it changed.
    last_resources: Option<crate::kernel::ResourceContext>,
    /// The recorded points at which a memory cell came to hold each integer
    /// value, keyed by the value's held-term fingerprint and then newest
    /// first (by the count of entries made before, subtracted from the
    /// largest count): a value no nearer state names is spelled in such a
    /// point's state, as the field or element it is there. Filled from the
    /// cells each insert's memory changed; whether the point's state spells
    /// the value is the reader's check.
    cell_points: crate::persistent::PersistentMap<(u64, usize), ProgramPointSelector>,
    /// The memory of the state inserted last, against which the next insert
    /// finds the cells it changed.
    last_memory: Option<crate::kernel::SymbolicMemory>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LoopLabels {
    loops: BTreeMap<String, usize>,
    preferred: BTreeMap<usize, String>,
}

struct RecordedStateVersion {
    root: Option<std::sync::Arc<RecordedStateNode>>,
    history: Option<std::sync::Arc<RecordedStateChange>>,
    origin: std::sync::Arc<()>,
}

struct RecordedInterfaceMarks {
    root: Option<std::sync::Arc<RecordedStateNode>>,
    call_result_snapshots: imbl::OrdMap<ProgramPointSelector, RecordedCallResults>,
}

impl Default for RecordedStates {
    fn default() -> Self {
        Self {
            entry_separation_sources: None,
            effect_log: imbl::Vector::new(),
            effect_gaps: imbl::Vector::new(),
            effect_offsets: imbl::OrdMap::new(),
            footprint_values: std::sync::Arc::new(std::sync::Mutex::new(
                std::collections::HashMap::new(),
            )),
            version: std::sync::Arc::new(RecordedStateVersion {
                root: None,
                history: None,
                origin: std::sync::Arc::new(()),
            }),
            interface_marks: None,
            loop_labels: None,
            source_layout: None,
            point_names: imbl::HashMap::new(),
            memory_points: imbl::OrdMap::new(),
            value_points: crate::persistent::PersistentMap::default(),
            pointer_points: crate::persistent::PersistentMap::default(),
            allocation_results: crate::persistent::PersistentMap::default(),
            call_results: RecordedCallResults::default(),
            call_result_snapshots: imbl::OrdMap::new(),
            ambiguous_exit_points: crate::persistent::PersistentMap::default(),
            call_result_points: crate::persistent::PersistentMap::default(),
            read_event_results: Default::default(),
            read_event_counts: Default::default(),
            read_event_names: Default::default(),
            read_event_scalar_names: Default::default(),
            read_event_pointer_names: Default::default(),
            algebraic_call_results: crate::persistent::PersistentMap::default(),
            pointer_call_results: crate::persistent::PersistentMap::default(),
            loop_iterations: crate::persistent::PersistentMap::default(),
            loop_iteration_variables: crate::persistent::PersistentMap::default(),
            field_points: crate::persistent::PersistentMap::default(),
            last_locals: None,
            last_resources: None,
            cell_points: crate::persistent::PersistentMap::default(),
            last_memory: None,
        }
    }
}

#[derive(Clone)]
struct RecordedStateNode {
    selector: ProgramPointSelector,
    state: Option<ExecutionState>,
    left: Option<std::sync::Arc<RecordedStateNode>>,
    right: Option<std::sync::Arc<RecordedStateNode>>,
    height: u8,
}

/// One persistent map mutation. Proof branches share their complete prefix;
/// an audited join can therefore visit only the keys changed in either arm
/// instead of intersecting every state accumulated by the project.
#[derive(Clone)]
struct RecordedStateChange {
    selector: ProgramPointSelector,
    parent: Option<std::sync::Arc<RecordedStateChange>>,
}

/// The history is one node per recorded change, so a proof that steps a few
/// thousand statements owns a chain that long. Dropping it through the
/// derived `Drop` recurses once per node and overflowed the 8 MB main thread
/// of `click verify` at about 6,000 recorded steps, well inside the budget an
/// implicit proof may spend; the test harness only hid it behind a 64 MB
/// worker. The chain is unlinked here instead, node by node, for as long as
/// this drop holds the last reference to the next one; a node another
/// version still shares stops the walk and is dropped by that version later.
impl Drop for RecordedStateChange {
    fn drop(&mut self) {
        let mut next = self.parent.take();
        while let Some(node) = next {
            next = match std::sync::Arc::try_unwrap(node) {
                Ok(mut node) => node.parent.take(),
                Err(_) => None,
            };
        }
    }
}

#[cfg(test)]
thread_local! {
    static RECORDED_STATE_NODE_ALLOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn recorded_state_node_allocations() -> usize {
    RECORDED_STATE_NODE_ALLOCATIONS.with(std::cell::Cell::get)
}

impl RecordedStates {
    fn record_effect(&mut self, effect: Option<&std::sync::Arc<crate::kernel::RegionFootprint>>) {
        if let Some(effect) = effect {
            let gap = self.effect_log.back().is_some_and(|previous| {
                let crate::kernel::Resource::Footprint(previous) = previous else {
                    unreachable!()
                };
                crate::kernel::intern_memory_ref(&previous.after)
                    != crate::kernel::intern_memory_ref(&effect.before)
                    || !previous
                        .after_resources
                        .shares_storage_with(&effect.before_resources)
            });
            self.effect_gaps
                .push_back(self.effect_gaps.back().copied().unwrap_or(0) + usize::from(gap));
            self.effect_log
                .push_back(crate::kernel::Resource::Footprint(effect.clone()));
        }
    }

    fn footprint(&self, region: &CodeRegionRef) -> Result<crate::kernel::Resource, String> {
        let before = self.recorded_spelling(ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: region.clone(),
            kind: ProgramPointKind::Entry,
        }));
        let after = self.recorded_spelling(ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: region.clone(),
            kind: ProgramPointKind::Exit,
        }));
        let start = *self
            .effect_offsets
            .get(&before)
            .ok_or("region footprint requires a recorded entry")?;
        let end = *self
            .effect_offsets
            .get(&after)
            .ok_or("region footprint requires a recorded exit")?;
        if start > end {
            return Err("region footprint endpoints belong to different executions".into());
        }
        let before_state = self.get(&before).ok_or("missing footprint entry")?;
        let after_state = self.get(&after).ok_or("missing footprint exit")?;
        let memory_is = |a: &crate::kernel::SymbolicMemory, b: &crate::kernel::SymbolicMemory| {
            crate::kernel::intern_memory_ref(a) == crate::kernel::intern_memory_ref(b)
        };
        let covered = if start == end {
            memory_is(before_state.memory(), after_state.memory())
                && before_state
                    .resources()
                    .shares_storage_with(after_state.resources())
        } else {
            match (self.effect_log.get(start), self.effect_log.get(end - 1)) {
                (
                    Some(crate::kernel::Resource::Footprint(first)),
                    Some(crate::kernel::Resource::Footprint(last)),
                ) => {
                    memory_is(before_state.memory(), &first.before)
                        && memory_is(after_state.memory(), &last.after)
                        && before_state
                            .resources()
                            .shares_storage_with(&first.before_resources)
                        && after_state
                            .resources()
                            .shares_storage_with(&last.after_resources)
                        && self.effect_gaps.get(start) == self.effect_gaps.get(end - 1)
                }
                _ => false,
            }
        };
        if !covered {
            return Err("region footprint is not recorded across this execution boundary".into());
        }
        // A single atomic effect already is the execution-produced descriptor.
        // Keep its identity so its published containment fact names this term.
        if end == start + 1
            && let Some(crate::kernel::Resource::Footprint(effect)) = self.effect_log.get(start)
        {
            return Ok(crate::kernel::Resource::Footprint(effect.clone()));
        }
        let key = (
            before.clone(),
            after.clone(),
            start,
            end,
            end.checked_sub(1)
                .and_then(|i| self.effect_log.get(i).cloned()),
            crate::kernel::intern_memory_ref(before_state.memory()),
            crate::kernel::intern_memory_ref(after_state.memory()),
        );
        if let Some(value) = self.footprint_values.lock().unwrap().get(&key) {
            return Ok(value.clone());
        }
        let mut members = self.effect_log.clone().split_off(start);
        members.truncate(end - start);
        // A state comparison cannot establish that an unrecorded region had
        // no effects: a write may restore the same value. Only the matching
        // producer's atomic region is currently a complete footprint.
        let complete = match (&before, &after, members.front()) {
            (
                ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Region(a),
                    ..
                }),
                ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Region(b),
                    ..
                }),
                Some(crate::kernel::Resource::Footprint(effect)),
            ) => a == b && members.len() == 1 && effect.source == format!("region({a}).footprint"),
            _ => false,
        };
        let value = crate::kernel::Resource::Footprint(crate::kernel::RegionFootprint::sequence(
            format!(
                "{}.footprint",
                diagnostics::describe_code_region_ref(region)
            ),
            self.get(&before).ok_or("missing footprint entry")?,
            self.get(&after).ok_or("missing footprint exit")?,
            members,
            complete,
        ));
        self.footprint_values
            .lock()
            .unwrap()
            .insert(key, value.clone());
        Ok(value)
    }

    fn new() -> Self {
        Self::default()
    }

    /// The abstract interface can read its target and shared proof marks.
    /// Its target is only a lowering input. Publication at the continuation
    /// adds the checked successor to the ordinary indexes once.
    fn for_branch_interface(
        &self,
        common: &Self,
        target: &ProgramPointRef,
        state: &ExecutionState,
    ) -> Self {
        let selector = self.recorded_spelling(target.clone().into());
        let mut records = Self {
            version: std::sync::Arc::new(RecordedStateVersion {
                root: Some(recorded_state_node(
                    selector.clone(),
                    Some(state.clone()),
                    None,
                    None,
                )),
                history: None,
                origin: std::sync::Arc::new(()),
            }),
            interface_marks: Some(std::sync::Arc::new(RecordedInterfaceMarks {
                root: common.version.root.clone(),
                call_result_snapshots: common.call_result_snapshots.clone(),
            })),
            loop_labels: self.loop_labels.clone(),
            source_layout: self.source_layout.clone(),
            loop_iterations: self.loop_iterations.clone(),
            loop_iteration_variables: self.loop_iteration_variables.clone(),
            ..Self::new()
        };
        records.effect_offsets.insert(selector.clone(), 0);
        if records.records_call_snapshots() {
            records.set_call_result_snapshot(&selector, Some(RecordedCallResults::default()));
        }
        records
    }

    fn get<K: RecordedStateKey + ?Sized>(&self, key: &K) -> Option<&ExecutionState> {
        if self.loop_labels.is_some() || key.is_source_path() {
            let selector = self.recorded_spelling(key.to_selector());
            return self.get_exact(&selector);
        }
        self.get_exact(key)
    }

    /// Resolves statement paths through `layout`, the function's own.
    fn with_source_layout(mut self, layout: lowering::SourceExecutionLayout) -> Self {
        self.source_layout = Some(layout);
        self
    }

    /// The `region(N)` point a path through the statements as written names.
    fn source_point(&self, point: &ProgramPointRef) -> Result<ProgramPointRef, String> {
        let CodeRegionRef::Path(steps) = &point.region else {
            return Ok(point.clone());
        };
        // A table built for a fixed-state proof inside the function may not
        // carry the layout; the function being checked is the same one.
        let fallback;
        let layout = match &self.source_layout {
            Some(layout) => layout,
            None => {
                fallback = diagnostics::spelling_layout().ok_or(
                    "`statement(i)` regions name points of a function body being executed",
                )?;
                &fallback
            }
        };
        Ok(ProgramPointRef {
            region: CodeRegionRef::Region(layout.source_path_region(steps, point.kind)?),
            kind: point.kind,
        })
    }

    /// The exit point of the call region `region` names, recorded as its
    /// `region(N)`, and the local that call assigns its result to: what
    /// `<region>.result` reads.
    pub(crate) fn region_result(
        &self,
        region: &CodeRegionRef,
    ) -> Result<(ProgramPointRef, crate::kernel::BindingName), String> {
        let fallback;
        let layout = match &self.source_layout {
            Some(layout) => layout,
            None => {
                fallback = diagnostics::spelling_layout()
                    .ok_or("`.result` names a region of a function body being executed")?;
                &fallback
            }
        };
        let index = match region {
            CodeRegionRef::Path(steps) => {
                layout.source_path_region(steps, ProgramPointKind::Exit)?
            }
            CodeRegionRef::Region(index) => *index,
            _ => return Err("`.result` names a call's region".to_string()),
        };
        let local = layout.call_result_local(index).ok_or_else(|| {
            format!(
                "`{}` is not a call that produces a result, so it has no `.result`",
                diagnostics::describe_code_region_ref(region)
            )
        })?;
        Ok((
            ProgramPointRef {
                region: CodeRegionRef::Region(index),
                kind: ProgramPointKind::Exit,
            },
            local.clone(),
        ))
    }

    fn result_region_index(&self, region: &CodeRegionRef) -> Result<usize, String> {
        match region {
            CodeRegionRef::Region(index) => Ok(*index),
            CodeRegionRef::Path(steps) => self
                .source_layout
                .clone()
                .or_else(diagnostics::spelling_layout)
                .ok_or("`.result` requires a function execution")?
                .source_path_region(steps, ProgramPointKind::Exit),
            _ => Err("`.result` names a call's region".into()),
        }
    }

    fn read_event_region(&self, index: usize, event: usize) -> CodeRegionRef {
        let mut steps = self
            .source_layout
            .as_ref()
            .and_then(|layout| layout.source_path_spelling(index, ProgramPointKind::Exit))
            .unwrap_or_else(|| vec![SourcePathStep::Region(index)]);
        steps.push(SourcePathStep::ReadEvent(event));
        CodeRegionRef::Path(steps)
    }

    fn add_read_event_name<T: Ord + Clone>(
        names: &mut ReadEventNames<T>,
        value: &T,
        event: (usize, usize),
    ) {
        let events = names
            .get(value)
            .cloned()
            .unwrap_or_default()
            .with_value(event);
        names.insert(value.clone(), events);
    }

    fn remove_read_event_name<T: Ord + Clone>(
        names: &mut ReadEventNames<T>,
        value: &T,
        event: (usize, usize),
    ) {
        let Some(events) = names.get(value) else {
            return;
        };
        let events = events.without_value(&event);
        if events.is_empty() {
            names.remove(value);
        } else {
            names.insert(value.clone(), events);
        }
    }

    fn record_read_events(&mut self, index: usize, facts: &crate::kernel::ExecutionFacts) {
        self.record_read_retained_event_values(
            index,
            facts.iter().filter_map(|fact| {
                crate::instrumentation::record_deterministic_work(1);
                fact.volatile_read_retained_result().cloned()
            }),
        );
    }

    fn record_read_event_values<'a>(
        &mut self,
        index: usize,
        values: impl Iterator<Item = &'a ProgramValue>,
    ) {
        self.record_read_retained_event_values(index, values.map(|value| value.clone().into()));
    }

    fn record_read_retained_event_values(
        &mut self,
        index: usize,
        values: impl Iterator<Item = crate::kernel::ExecutionValue>,
    ) {
        // Only this completed statement's output is visited, never prior facts.
        for event in 0..self.read_event_counts.get(&index).copied().unwrap_or(0) {
            crate::instrumentation::record_deterministic_work(1);
            let key = (index, event);
            if let Some(value) = self.read_event_native(&key).cloned() {
                self.read_event_results.remove(&key);
                Self::remove_read_event_name(&mut self.read_event_names, &value, key);
                match &value {
                    ProgramValue::Bool(term) | crate::kernel::integer_c_value!(term) => {
                        Self::remove_read_event_name(&mut self.read_event_scalar_names, term, key);
                    }
                    ProgramValue::Pointer(pointer) => {
                        Self::remove_read_event_name(
                            &mut self.read_event_pointer_names,
                            pointer.address(),
                            key,
                        );
                    }
                    _ => {}
                }
            }
        }
        let mut count = 0;
        for value in values {
            crate::instrumentation::record_deterministic_work(1);
            let key = (index, count);
            let retained = RetainedProgramValue::from(value);
            let value = retained.native_compat();
            Self::add_read_event_name(&mut self.read_event_names, value, key);
            match value {
                ProgramValue::Bool(term) | crate::kernel::integer_c_value!(term) => {
                    Self::add_read_event_name(&mut self.read_event_scalar_names, term, key);
                }
                ProgramValue::Pointer(pointer) => {
                    Self::add_read_event_name(
                        &mut self.read_event_pointer_names,
                        pointer.address(),
                        key,
                    );
                }
                _ => {}
            }
            self.read_event_results.insert(key, retained);
            count += 1;
        }
        if count == 0 {
            self.read_event_counts.remove(&index);
        } else {
            self.read_event_counts.insert(index, count);
        }
    }

    fn read_event_values(&self, index: usize) -> impl Iterator<Item = &ProgramValue> {
        (0..self.read_event_counts.get(&index).copied().unwrap_or(0)).map(move |event| {
            self.read_event_native(&(index, event))
                .expect("recorded read")
        })
    }

    fn read_event_naming_value(&self, value: &ProgramValue) -> Option<CodeRegionRef> {
        crate::instrumentation::record_deterministic_work(1);
        let &(index, event) = self.read_event_names.get(value)?.last()?;
        Some(self.read_event_region(index, event))
    }

    fn read_event_naming_scalar(
        &self,
        value: &crate::kernel::MachineTerm,
    ) -> Option<CodeRegionRef> {
        crate::instrumentation::record_deterministic_work(1);
        let &(index, event) = self.read_event_scalar_names.get(value)?.last()?;
        Some(self.read_event_region(index, event))
    }

    fn read_event_naming_pointer(&self, value: &crate::kernel::Address) -> Option<CodeRegionRef> {
        crate::instrumentation::record_deterministic_work(1);
        let &(index, event) = self.read_event_pointer_names.get(value)?.last()?;
        Some(self.read_event_region(index, event))
    }

    fn region_result_value(&self, region: &CodeRegionRef) -> Result<ProgramValue, String> {
        self.region_result_value_at(region, None)
    }

    fn call_results_at(&self, selector: &ProgramPointSelector) -> Option<&RecordedCallResults> {
        crate::instrumentation::record_deterministic_work(1);
        let selector = self.recorded_spelling(selector.clone());
        if matches!(selector, ProgramPointSelector::Mark(_))
            && let Some(marks) = &self.interface_marks
        {
            return marks.call_result_snapshots.get(&selector);
        }
        self.call_result_snapshots.get(&selector)
    }

    fn records_call_snapshots(&self) -> bool {
        self.source_layout
            .as_ref()
            .is_some_and(lowering::SourceExecutionLayout::snapshots_step_results)
    }

    fn region_result_value_at(
        &self,
        region: &CodeRegionRef,
        selector: Option<&ProgramPointSelector>,
    ) -> Result<ProgramValue, String> {
        if let CodeRegionRef::Path(steps) = region
            && let Some((SourcePathStep::ReadEvent(event), parent)) = steps.split_last()
        {
            let index = match parent {
                [SourcePathStep::Region(index)] => *index,
                _ => self.result_region_index(&CodeRegionRef::Path(parent.to_vec()))?,
            };
            return self
                .read_event_native(&(index, *event))
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "`{}.result` has no recorded volatile read result",
                        diagnostics::describe_code_region_ref(region)
                    )
                });
        }
        let index = self.result_region_index(region)?;
        if let Some(selector) = selector
            && self.records_call_snapshots()
            && self.source_layout.as_ref().is_some_and(|layout| {
                layout.call_number(index).is_some()
                    || layout
                        .call_result_local(index)
                        .and_then(crate::kernel::BindingName::local_id)
                        .is_some_and(crate::kernel::LocalBindingId::is_return_place)
            })
        {
            return self
                .call_results_at(selector)
                .and_then(|results| results.get(&index))
                .map(RetainedProgramValue::native_compat)
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "`{}.result` has no recorded non-void result at `{}`",
                        diagnostics::describe_code_region_ref(region),
                        diagnostics::describe_program_point_selector(selector)
                    )
                });
        }
        if let Some(result) = self.call_result_native(&index) {
            return Ok(result.clone());
        }
        if self.read_event_counts.get(&index) == Some(&1) {
            return Ok(self
                .read_event_native(&(index, 0))
                .expect("recorded read")
                .clone());
        }
        if self
            .read_event_counts
            .get(&index)
            .is_some_and(|count| *count > 1)
        {
            return Err("multiple volatile reads: select `.read_event(i).result`".into());
        }
        Err(format!(
            "`{}.result` has no recorded non-void result at this region's exit",
            diagnostics::describe_code_region_ref(region)
        ))
    }

    /// Where this path's change history stands now: `recorded_since` reads
    /// the points recorded after it.
    fn history_mark(&self) -> RecordedHistoryMark {
        RecordedHistoryMark(self.version.history.clone())
    }

    /// The program points this path recorded since `mark`, newest state of
    /// each, with the call results recorded at them: what a loop's exit
    /// carries out of the pass that left, so the proof after the loop can
    /// name the points of that pass. The walk visits the changes made since
    /// `mark` and no others, so it costs what the pass itself recorded.
    fn recorded_since(&self, mark: &RecordedHistoryMark) -> RecordedRegionPoints {
        let mut seen = std::collections::BTreeSet::new();
        let mut points = RecordedRegionPoints::default();
        let mut change = self.version.history.as_ref();
        while let Some(entry) = change {
            if mark
                .0
                .as_ref()
                .is_some_and(|marked| std::sync::Arc::ptr_eq(marked, entry))
            {
                break;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(index),
                kind,
            }) = &entry.selector
                && seen.insert(entry.selector.clone())
                && let Some(state) = self.get(&entry.selector)
            {
                points.retained_states.push((
                    entry.selector.clone(),
                    state.clone(),
                    self.call_result_snapshots.get(&entry.selector).cloned(),
                ));
                if *kind == ProgramPointKind::Exit
                    && let Some(value) = self.call_results.get(index)
                {
                    points.call_results.push((*index, value.clone()));
                }
            }
            change = entry.parent.as_ref();
        }
        points.retained_states.reverse();
        points
    }

    /// Notes that loop `loop_index` left on several paths, which recorded
    /// these points: each at its own state, so none is recorded here and a
    /// read of one is refused naming the paths.
    fn record_ambiguous_exit_points(&mut self, loop_index: usize, paths: &[RecordedRegionPoints]) {
        for points in paths {
            for (selector, _, _) in &points.retained_states {
                crate::instrumentation::record_deterministic_work(1);
                self.ambiguous_exit_points
                    .insert(selector.clone(), (loop_index, paths.len()));
            }
        }
    }

    /// Why `selector` has no recorded state after a loop that left on
    /// several paths, when that is the reason.
    fn ambiguous_exit_refusal(&self, selector: &ProgramPointSelector) -> Option<String> {
        let (loop_index, paths) = self.ambiguous_exit_points.get(selector)?;
        let ProgramPointSelector::ProgramPoint(point) = selector else {
            return None;
        };
        Some(format!(
            "`loop({loop_index})` left on {paths} paths, and each recorded `{}` at its own state, so after the loop it names no one state; a fact every leaving path states about that point is kept after the loop, so state what you need on each path before it leaves",
            crate::surface::diagnostics::describe_program_point_ref(point)
        ))
    }

    /// Records points another path recorded, as `recorded_since` returned
    /// them.
    fn record_region_points(&mut self, points: &RecordedRegionPoints) {
        for (selector, state, results) in &points.retained_states {
            self.insert(selector.clone(), state.clone());
            self.set_call_result_snapshot(selector, results.clone());
        }
        for (index, value) in &points.call_results {
            self.record_retained_call_result(*index, Some(value.clone()));
        }
    }

    fn set_call_result_snapshot(
        &mut self,
        selector: &ProgramPointSelector,
        results: Option<RecordedCallResults>,
    ) {
        if let Some(results) = results {
            self.call_result_snapshots.insert(selector.clone(), results);
        } else {
            self.call_result_snapshots.remove(selector);
        }
    }

    /// Some transition certificates expose the return value separately
    /// from the state recorded at the call's exit.
    fn record_call_transition_result(&mut self, index: usize, value: RetainedProgramValue) {
        if self.records_call_snapshots() {
            let exit = ProgramPointSelector::from(ProgramPointRef {
                region: CodeRegionRef::Region(index),
                kind: ProgramPointKind::Exit,
            });
            if let Some(results) = self.call_result_snapshots.get_mut(&exit) {
                results.insert(index, value.clone());
            }
        }
        self.record_retained_call_result(index, Some(value));
    }

    fn record_call_result(&mut self, index: usize, value: Option<ProgramValue>) {
        self.record_retained_call_result(index, value.map(RetainedProgramValue::from));
    }

    fn call_result_native(&self, index: &usize) -> Option<&ProgramValue> {
        self.call_results
            .get(index)
            .map(RetainedProgramValue::native_compat)
    }

    fn read_event_native(&self, key: &(usize, usize)) -> Option<&ProgramValue> {
        self.read_event_results
            .get(key)
            .map(RetainedProgramValue::native_compat)
    }

    fn record_retained_call_result(&mut self, index: usize, value: Option<RetainedProgramValue>) {
        crate::instrumentation::record_deterministic_work(1);
        // A pointer-sized integer is named by its numeric value.
        if let Some(ProgramValue::Bool(term) | crate::kernel::integer_c_value!(term)) = self
            .call_result_native(&index)
            .map(ProgramValue::numeric_value)
        {
            self.call_result_points
                .remove(&(crate::kernel::held_term_fingerprint(term), index));
        }
        if let Some(ProgramValue::Parameter(term)) = self
            .call_results
            .get(&index)
            .map(RetainedProgramValue::native_compat)
            && self.algebraic_call_results.get(term.as_ref()) == Some(&index)
        {
            self.algebraic_call_results.remove(term.as_ref());
        }
        if let Some(ProgramValue::Pointer(pointer)) = self
            .call_results
            .get(&index)
            .map(RetainedProgramValue::native_compat)
            && self.pointer_call_results.get(pointer.address()) == Some(&index)
        {
            self.pointer_call_results.remove(pointer.address());
        }
        self.call_results.remove(&index);
        if let Some(value) = value.filter(|value| value.native_compat() != &ProgramValue::Void) {
            let native = value.native_compat();
            if let ProgramValue::Bool(term) | crate::kernel::integer_c_value!(term) =
                native.numeric_value()
            {
                self.call_result_points
                    .insert((crate::kernel::held_term_fingerprint(term), index), ());
            }
            // The first call to produce an algebraic value names it.
            if let ProgramValue::Parameter(term) = native
                && self.algebraic_call_results.get(term.as_ref()).is_none()
            {
                self.algebraic_call_results
                    .insert(term.as_ref().clone(), index);
            }
            // So does the first call to return a pointer.
            if let ProgramValue::Pointer(pointer) = native
                && self.pointer_call_results.get(pointer.address()).is_none()
            {
                self.pointer_call_results
                    .insert(pointer.address().clone(), index);
            }
            self.call_results.insert(index, value);
        }
    }

    /// Records the pass count `iterations` of loop `loop_index`'s head,
    /// which the facts of a path past the loop state over.
    #[cfg(test)]
    pub(crate) fn record_loop_iterations(
        &mut self,
        loop_index: usize,
        iterations: &crate::kernel::IntegerTerm,
    ) {
        let root = crate::kernel::KernelTermImport::default().integer(&iterations.clone().into());
        self.record_loop_iterations_root(loop_index, root);
    }

    pub(crate) fn record_loop_iterations_root(
        &mut self,
        loop_index: usize,
        iterations: crate::kernel::KernelTerm,
    ) {
        if let Some(prior) = self.loop_iterations.get(&loop_index)
            && let crate::kernel::KernelTermNode::Variable(prior) = prior.node()
        {
            self.loop_iteration_variables.remove(prior);
        }
        if let crate::kernel::KernelTermNode::Variable(variable) = iterations.node() {
            self.loop_iteration_variables.insert(*variable, loop_index);
        }
        self.loop_iterations.insert(loop_index, iterations);
    }

    /// The loop whose pass count `variable` is: one lookup.
    pub(crate) fn loop_naming_iterations(
        &self,
        variable: crate::kernel::Variable,
    ) -> Option<usize> {
        let index = *self.loop_iteration_variables.get(&variable)?;
        matches!(self.loop_iterations.get(&index).map(|root| root.node()), Some(crate::kernel::KernelTermNode::Variable(held)) if *held == variable)
            .then_some(index)
    }

    /// Selected diagnostic output; retained loop counts remain common roots.
    pub(crate) fn loop_iteration_bindings(
        &self,
    ) -> impl Iterator<Item = (String, crate::kernel::IntegerTerm)> {
        self.loop_iterations.iter().map(|(index, term)| {
            (
                loop_iterations_spelling(*index),
                crate::kernel::KernelTermExport::default()
                    .integer(term)
                    .expect("recorded Integer output")
                    .as_ref()
                    .clone(),
            )
        })
    }

    /// A capture in a recorded state names the call result in that
    /// snapshot. An unqualified capture names the path's current result.
    fn call_capture_expression(
        &self,
        binding: &crate::kernel::BindingName,
        value: &crate::kernel::StoredExecutionValue,
        selector: Option<&ProgramPointSelector>,
    ) -> Option<ContractExpression> {
        if !binding
            .local_id()
            .is_some_and(crate::kernel::LocalBindingId::is_temporary)
        {
            return None;
        }
        let layout = self.source_layout.as_ref()?;
        let (index, source) = layout.call_capture_source(binding)?;
        let results = match selector {
            Some(point) => self.call_results_at(point)?,
            None => &self.call_results,
        };
        let recorded = results.get(&index)?.native_compat();
        if recorded.program_type() != value.program_type() || recorded != value.native().as_ref() {
            return None;
        }
        let expression = ContractExpression::RegionResult(source);
        Some(match selector {
            Some(selector) => ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(expression),
            },
            None => expression,
        })
    }

    /// Each recorded call's result with the source spelling that names it,
    /// `<call>.result`. Diagnostics only.
    pub(in crate::surface) fn call_result_bindings(&self) -> Vec<(String, &ProgramValue)> {
        let Some(layout) = self.source_layout.as_ref() else {
            return Vec::new();
        };
        self.call_results
            .iter()
            .filter_map(|(index, value)| {
                let steps = layout.source_path_spelling(*index, ProgramPointKind::Exit)?;
                Some((
                    format!(
                        "{}.result",
                        diagnostics::describe_code_region_ref(&CodeRegionRef::Path(steps))
                    ),
                    value.native_compat(),
                ))
            })
            .collect()
    }

    /// The call that produced the algebraic value `term`: one index lookup.
    fn call_result_naming_algebraic(
        &self,
        term: &crate::kernel::AlgebraicTerm,
    ) -> Option<CodeRegionRef> {
        crate::instrumentation::record_deterministic_work(1);
        let index = *self.algebraic_call_results.get(term)?;
        matches!(self.call_result_native(&index), Some(ProgramValue::Parameter(held)) if held.as_ref() == term)
            .then_some(CodeRegionRef::Region(index))
    }

    /// The call that returned the pointer at `pointer`'s address: one index
    /// lookup, checked against the recorded value.
    fn call_result_naming_pointer(
        &self,
        pointer: &crate::kernel::Address,
    ) -> Option<CodeRegionRef> {
        crate::instrumentation::record_deterministic_work(1);
        let index = *self.pointer_call_results.get(pointer)?;
        matches!(self.call_result_native(&index), Some(ProgramValue::Pointer(held)) if held.address() == pointer)
            .then_some(CodeRegionRef::Region(index))
    }

    fn call_result_naming_integer(
        &self,
        term: &crate::kernel::MachineTerm,
    ) -> Option<CodeRegionRef> {
        let fingerprint = crate::kernel::held_term_fingerprint(term);
        let mut key = (fingerprint, 0);
        let mut found = self.call_result_points.get_key_value(&key);
        loop {
            let ((hash, index), _) =
                found.or_else(|| self.call_result_points.get_greater_than(&key))?;
            if *hash != fingerprint {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            if matches!(self.call_result_native(index).map(ProgramValue::numeric_value), Some(ProgramValue::Bool(held) | crate::kernel::integer_c_value!(held)) if held == term)
            {
                return Some(CodeRegionRef::Region(*index));
            }
            key = (*hash, *index);
            found = None;
        }
    }

    fn region_allocation(&self, region: &CodeRegionRef) -> Result<ProgramValue, String> {
        let (point, local) = self.region_result(region)?;
        let CodeRegionRef::Region(index) = &point.region else {
            unreachable!("resolved region")
        };
        let layout = self
            .source_layout
            .clone()
            .or_else(diagnostics::spelling_layout)
            .ok_or("`.allocation` names an allocation region being executed")?;
        if layout.allocation_result_local(*index).is_none() {
            return Err("`.allocation` requires a fresh allocation region".to_string());
        }
        let state = self
            .get(&ProgramPointSelector::ProgramPoint(point))
            .ok_or("`.allocation` names an allocation this proof has not executed yet")?;
        let result_value = state.locals().get_native(&local);
        let Some(ProgramValue::Pointer(result)) = result_value.as_deref() else {
            return Err("allocation result was not recorded at its exit".to_string());
        };
        state
            .memory()
            .fresh_allocation_identity(result)
            .map(ProgramValue::Pointer)
            .ok_or_else(|| "region has no fresh allocation identity".to_string())
    }

    /// The program point `selector` names, spelled as it is recorded: a
    /// statement path as its `region(N)`, and a loop under its first label
    /// when the loop has one.
    fn recorded_spelling(&self, selector: ProgramPointSelector) -> ProgramPointSelector {
        let selector = match &selector {
            ProgramPointSelector::ProgramPoint(
                point @ ProgramPointRef {
                    region: CodeRegionRef::Path(_),
                    ..
                },
            ) => match self.source_point(point) {
                Ok(point) => ProgramPointSelector::ProgramPoint(point),
                Err(_) => return selector,
            },
            _ => selector,
        };
        let Some(labels) = &self.loop_labels else {
            return selector;
        };
        let ProgramPointSelector::ProgramPoint(ProgramPointRef { region, kind }) = &selector else {
            return selector;
        };
        let index = match region {
            CodeRegionRef::Loop(index) => *index,
            CodeRegionRef::Label(label) => match labels.loops.get(label) {
                Some(index) => *index,
                None => return selector,
            },
            _ => return selector,
        };
        match labels.preferred.get(&index) {
            Some(label) => ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Label(label.clone()),
                kind: *kind,
            }),
            None => ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Loop(index),
                kind: *kind,
            }),
        }
    }

    /// Records that the proof calls loop `index` `label` on this path.
    /// Record a loop's labels before its first state.
    fn label_loop(&mut self, index: usize, label: &str) {
        if self
            .loop_labels
            .as_ref()
            .is_some_and(|labels| labels.loops.get(label) == Some(&index))
        {
            return;
        }
        let mut labels = self.loop_labels.as_deref().cloned().unwrap_or_default();
        labels.loops.insert(label.to_string(), index);
        let first = !labels.preferred.contains_key(&index);
        labels
            .preferred
            .entry(index)
            .or_insert_with(|| label.to_string());
        // A state recorded before the loop had a label moves to the
        // label's spelling, so it stays the one entry for its point.
        let unlabeled = if first {
            [ProgramPointKind::Entry, ProgramPointKind::Exit]
                .into_iter()
                .filter_map(|kind| {
                    let point = ProgramPointRef {
                        region: CodeRegionRef::Loop(index),
                        kind,
                    };
                    let state = self.get_exact(&point)?.clone();
                    Some((point, state))
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        for (point, _) in &unlabeled {
            self.remove(point);
        }
        self.loop_labels = Some(std::sync::Arc::new(labels));
        for (point, state) in unlabeled {
            self.insert(point, state);
        }
    }

    /// The region a footprint runs across, which `R.footprint` names: the
    /// region its entry point is recorded as entering, when that region's
    /// recorded exit is the footprint's end point and its recorded footprint
    /// is this one. A point can carry several names (a statement and the
    /// call it makes end together), so the exit is confirmed by its identity
    /// rather than read from the point's name.
    pub(in crate::surface) fn footprint_region(
        &self,
        footprint: &crate::kernel::RegionFootprint,
    ) -> Option<CodeRegionRef> {
        let ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region,
            kind: ProgramPointKind::Entry,
        }) = self.point_names.get(&footprint.before_point.id()?)?
        else {
            return None;
        };
        let exit = ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: region.clone(),
            kind: ProgramPointKind::Exit,
        });
        if self.get(&exit)?.observation_point_id() != footprint.after_point.id() {
            return None;
        }
        // A region of several recorded effects has a combined footprint of
        // its own, which `R.footprint` lowers to; only the region whose
        // recorded footprint is this one names it.
        match self.footprint(region) {
            Ok(crate::kernel::Resource::Footprint(recorded)) if *recorded == *footprint => {
                Some(region.clone())
            }
            _ => None,
        }
    }

    /// Where a population total a lock acquired is spelled: the exit of the
    /// region whose recorded entry the lock started from, when that exit's
    /// state still counts exactly that total.
    pub(in crate::surface) fn acquired_total_point(
        &self,
        variable: crate::kernel::Variable,
        acquired_from: crate::kernel::program_point::ProgramPointId,
    ) -> Option<ProgramPointSelector> {
        let ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region,
            kind: ProgramPointKind::Entry,
        }) = self.point_names.get(&acquired_from)?
        else {
            return None;
        };
        let exit = ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: region.clone(),
            kind: ProgramPointKind::Exit,
        });
        let state = self.get(&exit)?;
        (state.population_count_acquired_point(variable) == Some(acquired_from)
            && state.population_total_unchanged(variable))
        .then_some(exit)
    }

    /// The name of the recorded point a path reached, by that point's
    /// identity.
    #[cfg_attr(not(test), allow(dead_code))]
    fn point_name(
        &self,
        id: crate::kernel::program_point::ProgramPointId,
    ) -> Option<&ProgramPointSelector> {
        self.point_names.get(&id)
    }

    fn get_exact<K: RecordedStateKey + ?Sized>(&self, key: &K) -> Option<&ExecutionState> {
        let root = match &self.interface_marks {
            Some(marks) if matches!(key.to_selector(), ProgramPointSelector::Mark(_)) => {
                &marks.root
            }
            _ => &self.version.root,
        };
        let mut node = root.as_deref();
        while let Some(current) = node {
            match key.compare(&current.selector) {
                std::cmp::Ordering::Less => node = current.left.as_deref(),
                std::cmp::Ordering::Greater => node = current.right.as_deref(),
                std::cmp::Ordering::Equal => return current.state.as_ref(),
            }
        }
        None
    }

    /// The newest recorded point whose memory reads the same program bytes
    /// as `memory`, with its state. One hash lookup; no state is visited.
    fn point_reading_memory(
        &self,
        memory: &crate::kernel::SharedMemory,
    ) -> Option<(&ProgramPointSelector, &ExecutionState)> {
        let selector = self.memory_points.get(&memory.read_identity())?;
        Some((selector, self.get_exact(selector)?))
    }

    /// Select a recorded read by its own point and verify the retained view.
    fn point_naming_read(
        &self,
        point: &crate::kernel::ProgramPoint,
    ) -> Option<(&ProgramPointSelector, &ExecutionState)> {
        crate::instrumentation::record_deterministic_work(1);
        let selector = self.point_name(point.id()?)?;
        let state = self.get_exact(selector)?;
        state
            .program_point()
            .names_read_view(point)
            .then_some((selector, state))
    }

    /// Name the retained read point. Detached legacy reads may carry a
    /// canonical projection, so they consult the index of its source memory.
    fn point_reading_load(
        &self,
        point: &crate::kernel::ProgramPoint,
        pointer: &crate::kernel::Address,
    ) -> Option<(&ProgramPointSelector, &ExecutionState)> {
        if point.id().is_some() {
            return self.point_naming_read(point);
        }
        let memory = point.shared_memory();
        self.point_reading_memory(memory).or_else(|| {
            let source = crate::kernel::load_projection_source(memory, pointer)?;
            self.point_reading_memory(&source)
        })
    }

    /// A recorded point at which a scalar local held exactly `term`, the
    /// local's name, and that point's state: one index range over the
    /// locals that held a term of this fingerprint, each checked there.
    fn point_naming_integer(
        &self,
        term: &crate::kernel::MachineTerm,
    ) -> Option<(
        &ProgramPointSelector,
        &crate::kernel::BindingName,
        &ExecutionState,
    )> {
        let fingerprint = crate::kernel::held_term_fingerprint(term);
        let mut key = (fingerprint, crate::kernel::BindingName::from(""));
        let mut found = self.value_points.get_key_value(&key);
        loop {
            let ((found_fingerprint, name), selector) =
                found.or_else(|| self.value_points.get_greater_than(&key))?;
            if *found_fingerprint != fingerprint {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(state) = self.get_exact(selector)
                && state.locals().holds_integer(name, term)
            {
                return Some((selector, name, state));
            }
            key = (fingerprint, name.clone());
            found = None;
        }
    }

    /// Indexes the integer values, and the blocks of the pointers, that
    /// `state`'s locals hold and the state inserted before it did not, at
    /// `selector`. A value keeps the first
    /// point that names it while that point's state still holds it.
    fn record_value_points(&mut self, selector: &ProgramPointSelector, state: &ExecutionState) {
        for (name, term) in state
            .locals()
            .changed_integer_holdings(self.last_locals.as_ref())
        {
            crate::instrumentation::record_deterministic_work(1);
            let key = (crate::kernel::held_term_fingerprint(term), name.clone());
            let named = self.value_points.get(&key).is_some_and(|earlier| {
                earlier != selector
                    && self
                        .get_exact(earlier)
                        .is_some_and(|earlier| earlier.locals().holds_integer(name, term))
            });
            if !named {
                self.value_points.insert(key, selector.clone());
            }
        }
        for (name, block) in state
            .locals()
            .changed_address_bases(self.last_locals.as_ref())
        {
            crate::instrumentation::record_deterministic_work(1);
            let key = (block.clone(), name.clone());
            let named = self.pointer_points.get(&key).is_some_and(|earlier| {
                earlier != selector
                    && self
                        .get_exact(earlier)
                        .is_some_and(|earlier| earlier.locals().holds_pointer_in_block(name, block))
            });
            if !named {
                self.pointer_points.insert(key, selector.clone());
            }
        }
        self.last_locals = Some(state.locals().clone());
        for instance in state
            .resources()
            .changed_owned_instances(self.last_resources.as_ref())
        {
            for (field_index, field) in instance.fields().iter().enumerate() {
                let Some(variable) = model_field_variable(field) else {
                    continue;
                };
                crate::instrumentation::record_deterministic_work(1);
                let named = self.field_points.get(&variable).is_some_and(|earlier| {
                    earlier != selector
                        && self.get_exact(earlier).is_some_and(|earlier| {
                            instance_holds_field_value(
                                earlier,
                                instance.identity(),
                                field_index,
                                variable,
                            )
                        })
                });
                if !named {
                    self.field_points.insert(variable, selector.clone());
                }
            }
        }
        self.last_resources = Some(state.resources().clone());
        for term in state
            .memory()
            .changed_cell_integers(self.last_memory.as_ref())
        {
            crate::instrumentation::record_deterministic_work(1);
            let newest_first = usize::MAX - self.cell_points.len();
            self.cell_points.insert(
                (crate::kernel::held_term_fingerprint(term), newest_first),
                selector.clone(),
            );
        }
        self.last_memory = Some(state.memory().clone());
    }

    fn update_allocation_result(
        &mut self,
        selector: &ProgramPointSelector,
        prior: Option<&ExecutionState>,
        next: Option<&ExecutionState>,
    ) {
        let ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        }) = selector
        else {
            return;
        };
        let Some(local) = self
            .source_layout
            .as_ref()
            .and_then(|layout| layout.allocation_result_local(*index))
        else {
            return;
        };
        let result = |state: &ExecutionState| {
            let native = state.locals().get_native(local)?;
            let ProgramValue::Pointer(value) = native.as_ref() else {
                return None;
            };
            state
                .memory()
                .fresh_allocation_identity(value)
                .map(|value| value.address().clone())
        };
        let region = CodeRegionRef::Region(*index);
        if let Some(old) = prior.and_then(result)
            && self.allocation_results.get(&old) == Some(&region)
        {
            self.allocation_results.remove(&old);
        }
        if let Some(new) = next.and_then(result)
            && self.allocation_results.get(&new).is_none()
        {
            self.allocation_results.insert(new, region);
        }
    }

    fn allocation_result(&self, pointer: &crate::kernel::Address) -> Option<CodeRegionRef> {
        crate::instrumentation::record_deterministic_work(1);
        self.allocation_results.get(pointer).cloned()
    }

    /// Name the address of frontend-owned storage by its producing region.
    fn produced_address_expression(
        &self,
        pointer: &crate::kernel::Address,
    ) -> Option<ContractExpression> {
        use crate::kernel::AddressBase;
        match &pointer.base {
            AddressBase::AutomaticLocal { binding, .. } if binding.is_temporary() => {
                self.call_result_address_expression(pointer)
            }
            AddressBase::Heap(_) => Self::displaced_result_address(pointer, |base| {
                Some(ContractExpression::RegionAllocation(
                    self.allocation_result(base)?,
                ))
            }),
            _ => None,
        }
    }

    fn call_result_address_expression(
        &self,
        pointer: &crate::kernel::Address,
    ) -> Option<ContractExpression> {
        if let Some(region) = self.call_result_naming_pointer(pointer) {
            return Some(ContractExpression::RegionResult(region));
        }
        Self::displaced_result_address(pointer, |base| {
            Some(ContractExpression::RegionResult(
                self.call_result_naming_pointer(base)?,
            ))
        })
    }

    fn displaced_result_address(
        pointer: &crate::kernel::Address,
        name_base: impl FnOnce(&crate::kernel::Address) -> Option<ContractExpression>,
    ) -> Option<ContractExpression> {
        use crate::kernel::{Address, AddressOffset};
        let AddressOffset::Constant(bytes) = pointer.offset else {
            return None;
        };
        let bytes = u32::try_from(bytes).ok()?;
        if bytes == 0 {
            return name_base(pointer);
        }
        let base = Address {
            base: pointer.base.clone(),
            offset: AddressOffset::Constant(0),
        };
        Some(ContractExpression::CUnary {
            operand: Box::new(name_base(&base)?),
            lowered: ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(ProgramExpression::Value(crate::kernel::int32(0))),
                bytes: bytes.into(),
            },
        })
    }

    /// The recorded points at which some local held a pointer into `block`,
    /// with their states, in the locals' name order: at most
    /// [`POINTER_POINTS_OFFERED`], each checked against its state.
    fn points_holding_address_base<'a>(
        &'a self,
        block: &'a crate::kernel::AddressBase,
    ) -> impl Iterator<Item = (&'a ProgramPointSelector, &'a ExecutionState)> {
        let mut key = (block.clone(), crate::kernel::BindingName::from(""));
        let mut found = self.pointer_points.get_key_value(&key);
        std::iter::from_fn(move || {
            loop {
                let ((found_block, name), selector) = found
                    .take()
                    .or_else(|| self.pointer_points.get_greater_than(&key))?;
                if found_block != block {
                    return None;
                }
                crate::instrumentation::record_deterministic_work(1);
                key = (block.clone(), name.clone());
                if let Some(state) = self.get_exact(selector)
                    && state.locals().holds_pointer_in_block(name, block)
                {
                    return Some((selector, state));
                }
            }
        })
        .take(POINTER_POINTS_OFFERED)
    }

    /// The recorded points at which a memory cell held an integer term of
    /// `term`'s fingerprint, newest first, with their states: at most
    /// [`CELL_POINTS_OFFERED`]. The caller spells the term in each state.
    fn points_holding_cell_integer(
        &self,
        term: &crate::kernel::MachineTerm,
    ) -> impl Iterator<Item = (&ProgramPointSelector, &ExecutionState)> {
        let fingerprint = crate::kernel::held_term_fingerprint(term);
        let mut key = (fingerprint, 0);
        let mut first = true;
        std::iter::from_fn(move || {
            let found = if std::mem::take(&mut first) {
                self.cell_points
                    .get_key_value(&key)
                    .or_else(|| self.cell_points.get_greater_than(&key))
            } else {
                self.cell_points.get_greater_than(&key)
            };
            let (found_key, selector) = found?;
            if found_key.0 != fingerprint {
                return None;
            }
            key = *found_key;
            crate::instrumentation::record_deterministic_work(1);
            Some(selector)
        })
        .filter_map(|selector| Some((selector, self.get_exact(selector)?)))
        .take(CELL_POINTS_OFFERED)
    }

    /// The recorded point at which a resource instance held the scalar
    /// model-field value `variable`, with its state: one index lookup,
    /// checked against that state.
    fn point_holding_field_value(
        &self,
        variable: crate::kernel::Variable,
    ) -> Option<(&ProgramPointSelector, &ExecutionState)> {
        let selector = self.field_points.get(&variable)?;
        let state = self.get_exact(selector)?;
        let origin = crate::kernel::model_fields::registered_model_field_origin(variable)?;
        instance_holds_field_value(state, origin.identity, origin.field_index, variable)
            .then_some((selector, state))
    }

    fn contains_key<K: RecordedStateKey + ?Sized>(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    fn insert(
        &mut self,
        selector: impl Into<ProgramPointSelector>,
        state: ExecutionState,
    ) -> Option<ExecutionState> {
        let selector = self.recorded_spelling(selector.into());
        self.ambiguous_exit_points.remove(&selector);
        self.effect_offsets
            .insert(selector.clone(), self.effect_log.len());
        let prior = self.get(&selector).cloned();
        self.update_allocation_result(&selector, prior.as_ref(), Some(&state));
        if let Some(id) = state.observation_point_id() {
            self.point_names.insert(id, selector.clone());
        }
        if let Some(memory) = crate::kernel::interned_storage_of(state.memory()) {
            self.memory_points
                .insert(memory.read_identity(), selector.clone());
        }
        if let ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        }) = &selector
        {
            // A call inside an expression leaves its result in the state by
            // its number; one assigned to a local leaves it there.
            let result =
                self.source_layout
                    .as_ref()
                    .and_then(|layout| match layout.call_number(*index) {
                        Some(call) => state
                            .step_result(call)
                            .map(|value| RetainedProgramValue::from(value.clone().into_value())),
                        None => {
                            let local = layout.call_result_local(*index)?;
                            if let Some(value) = state.locals().get(local) {
                                return Some(RetainedProgramValue::from(
                                    value.clone().into_value(),
                                ));
                            }
                            local.local_id().filter(|id| id.is_temporary())?;
                            let address = state.locals().aggregate_object_pointer(local)?;
                            Some(RetainedProgramValue::from(ProgramValue::typed_pointer(
                                address.clone(),
                                crate::kernel::ProgramType::UInt8Pointer,
                            )))
                        }
                    });
            self.record_retained_call_result(*index, result);
        }
        if self.records_call_snapshots() {
            self.call_result_snapshots
                .insert(selector.clone(), self.call_results.clone());
        }
        self.record_value_points(&selector, &state);
        self.version = std::sync::Arc::new(RecordedStateVersion {
            root: Some(recorded_state_insert(
                self.version.root.as_ref(),
                selector.clone(),
                Some(state),
            )),
            history: Some(std::sync::Arc::new(RecordedStateChange {
                selector,
                parent: self.version.history.clone(),
            })),
            origin: self.version.origin.clone(),
        });
        prior
    }

    /// The index of the C statement whose state was recorded most
    /// recently and is still recorded: the statement an execution path last
    /// stepped. Diagnostics read this to name where a path ended.
    ///
    /// The walk follows the change history from its newest entry and stops
    /// at the first statement, so it costs the few non-statement changes
    /// (marks, loop and label points) recorded after that statement. It
    /// gives up after `LATEST_STATEMENT_WALK` changes rather than scan a
    /// long history for a location note.
    fn latest_statement(&self) -> Option<usize> {
        const LATEST_STATEMENT_WALK: usize = 64;
        let mut change = self.version.history.as_ref();
        for _ in 0..LATEST_STATEMENT_WALK {
            let entry = change?;
            if let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(index),
                ..
            }) = &entry.selector
                && self.contains_key(&entry.selector)
            {
                return Some(*index);
            }
            change = entry.parent.as_ref();
        }
        None
    }

    fn remove<K: RecordedStateKey + ?Sized>(&mut self, key: &K) -> Option<ExecutionState> {
        let selector = self.recorded_spelling(key.to_selector());
        let prior = self.get(key).cloned();
        self.call_result_snapshots.remove(&selector);
        self.update_allocation_result(&selector, prior.as_ref(), None);
        if let ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        }) = &selector
        {
            self.record_call_result(*index, None);
            self.record_read_event_values(*index, std::iter::empty());
        }

        if let Some(id) = prior.as_ref().and_then(|state| state.program_point_id())
            && self.point_names.get(&id) == Some(&selector)
        {
            self.point_names.remove(&id);
        }
        if let Some(memory) = prior
            .as_ref()
            .and_then(|state| crate::kernel::interned_storage_of(state.memory()))
            && self.memory_points.get(&memory.read_identity()) == Some(&selector)
        {
            self.memory_points.remove(&memory.read_identity());
        }
        if prior.is_some() {
            self.version = std::sync::Arc::new(RecordedStateVersion {
                root: Some(recorded_state_insert(
                    self.version.root.as_ref(),
                    selector.clone(),
                    None,
                )),
                history: Some(std::sync::Arc::new(RecordedStateChange {
                    selector,
                    parent: self.version.history.clone(),
                })),
                origin: self.version.origin.clone(),
            });
        }
        prior
    }

    /// Intersects two descendants of one exact persistent ancestor by
    /// visiting only the keys changed after the fork.
    ///
    /// This is the recorded-state merge required by a proof-level execution
    /// case split. Returning `None` for unrelated histories prevents a caller
    /// from treating structurally similar maps as branches of the same proof.
    fn common_descendant(&self, other: &Self, ancestor: &Self) -> Option<Self> {
        fn changed_keys_since(
            descendant: &RecordedStates,
            ancestor: &RecordedStates,
            changed: &mut BTreeSet<ProgramPointSelector>,
        ) -> bool {
            let mut current = descendant.version.history.as_ref();
            loop {
                match (current, ancestor.version.history.as_ref()) {
                    (Some(left), Some(right)) if std::sync::Arc::ptr_eq(left, right) => {
                        return true;
                    }
                    (None, None) => return true,
                    (Some(change), _) => {
                        changed.insert(change.selector.clone());
                        current = change.parent.as_ref();
                    }
                    (None, Some(_)) => return false,
                }
            }
        }

        if !std::sync::Arc::ptr_eq(&self.version.origin, &ancestor.version.origin)
            || !std::sync::Arc::ptr_eq(&other.version.origin, &ancestor.version.origin)
        {
            return None;
        }
        let mut changed = BTreeSet::new();
        if !changed_keys_since(self, ancestor, &mut changed)
            || !changed_keys_since(other, ancestor, &mut changed)
        {
            return None;
        }
        let mut common = ancestor.clone();
        // Labels both arms agree on stay; an arm's own labels end at the join.
        if self.loop_labels == other.loop_labels {
            common.loop_labels = self.loop_labels.clone();
        }
        // Overlay agreed counts on the ancestor. A key with the ancestor's
        // value in this arm cannot change the result, regardless of the
        // other arm's value. The diff skips shared subtrees.
        for (index, iterations, _) in self.loop_iterations.diff(&ancestor.loop_iterations) {
            if let Some(iterations) = iterations
                && other.loop_iterations.get(index) == Some(iterations)
            {
                common.record_loop_iterations_root(*index, iterations.clone());
            }
        }
        for selector in changed {
            match (self.get(&selector), other.get(&selector)) {
                (Some(left), Some(right)) if left == right => {
                    common.insert(selector.clone(), left.clone());
                    if let (Some(left), Some(right)) = (
                        self.call_result_snapshots.get(&selector),
                        other.call_result_snapshots.get(&selector),
                    ) {
                        let mut results = left.clone();
                        for (index, left, _) in left.diff(right) {
                            if left.is_some() {
                                results.remove(index);
                            }
                        }
                        common
                            .call_result_snapshots
                            .insert(selector.clone(), results);
                    } else {
                        common.call_result_snapshots.remove(&selector);
                    }
                    if let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: CodeRegionRef::Region(index),
                        kind: ProgramPointKind::Exit,
                    }) = selector
                    {
                        if self
                            .read_event_values(index)
                            .eq(other.read_event_values(index))
                        {
                            common.record_read_event_values(index, self.read_event_values(index));
                        } else {
                            common.record_read_event_values(index, std::iter::empty());
                        }
                    }
                }
                _ => {
                    common.remove(&selector);
                }
            }
        }
        Some(common)
    }

    fn iter(&self) -> std::vec::IntoIter<(&ProgramPointSelector, &ExecutionState)> {
        let mut entries = Vec::new();
        recorded_state_entries(self.version.root.as_deref(), &mut entries);
        entries.into_iter()
    }

    /// The entries newest selector first, read from the persistent tree as
    /// they are taken: a reader that stops at the first one it wants visits
    /// a logarithm of the tree, not every state the path recorded.
    fn iter_newest_first(&self) -> RecordedStatesNewestFirst<'_> {
        let mut entries = RecordedStatesNewestFirst {
            pending: Vec::new(),
        };
        entries.push_right_spine(self.version.root.as_deref());
        entries
    }

    fn keys_newest_first(&self) -> impl Iterator<Item = &ProgramPointSelector> {
        self.iter_newest_first().map(|(selector, _)| selector)
    }

    /// Bounded, newest-first source points for diagnostic reconstruction.
    /// History can repeat a key; only its currently recorded state is returned.
    fn recent(&self, limit: usize) -> Vec<(&ProgramPointSelector, &ExecutionState)> {
        let mut result = Vec::new();
        let mut seen = BTreeSet::new();
        let mut change = self.version.history.as_ref();
        while let Some(current) = change {
            if seen.insert(&current.selector)
                && let Some(state) = self.get(&current.selector)
            {
                result.push((&current.selector, state));
                if result.len() >= limit {
                    break;
                }
            }
            change = current.parent.as_ref();
        }
        result
    }

    /// The proof's marks, at most `limit` of them. `Mark` selectors sort
    /// after every program point, so they lead the newest-first walk and
    /// the walk stops at the first program point.
    fn marks(&self, limit: usize) -> Vec<(&ProgramPointSelector, &ExecutionState)> {
        self.iter_newest_first()
            .take_while(|(selector, _)| matches!(selector, ProgramPointSelector::Mark(_)))
            .take(limit)
            .collect()
    }
}

trait RecordedStateKey {
    fn compare(&self, selector: &ProgramPointSelector) -> std::cmp::Ordering;
    fn to_selector(&self) -> ProgramPointSelector;
    /// Whether the key is a path through the statements as written, which
    /// is recorded under the `region(N)` it resolves to.
    fn is_source_path(&self) -> bool;
}

impl RecordedStateKey for ProgramPointSelector {
    fn compare(&self, selector: &ProgramPointSelector) -> std::cmp::Ordering {
        self.cmp(selector)
    }

    fn to_selector(&self) -> ProgramPointSelector {
        self.clone()
    }

    fn is_source_path(&self) -> bool {
        matches!(
            self,
            ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Path(_),
                ..
            })
        )
    }
}

impl RecordedStateKey for ProgramPointRef {
    fn compare(&self, selector: &ProgramPointSelector) -> std::cmp::Ordering {
        ProgramPointSelector::ProgramPoint(self.clone()).cmp(selector)
    }

    fn to_selector(&self) -> ProgramPointSelector {
        ProgramPointSelector::ProgramPoint(self.clone())
    }

    fn is_source_path(&self) -> bool {
        matches!(self.region, CodeRegionRef::Path(_))
    }
}

impl std::fmt::Debug for RecordedStates {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

impl PartialEq for RecordedStates {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl Eq for RecordedStates {}

fn recorded_state_height(node: Option<&std::sync::Arc<RecordedStateNode>>) -> u8 {
    node.map_or(0, |node| node.height)
}

fn recorded_state_node(
    selector: ProgramPointSelector,
    state: Option<ExecutionState>,
    left: Option<std::sync::Arc<RecordedStateNode>>,
    right: Option<std::sync::Arc<RecordedStateNode>>,
) -> std::sync::Arc<RecordedStateNode> {
    #[cfg(test)]
    RECORDED_STATE_NODE_ALLOCATIONS.with(|allocations| allocations.set(allocations.get() + 1));
    let height =
        1 + recorded_state_height(left.as_ref()).max(recorded_state_height(right.as_ref()));
    std::sync::Arc::new(RecordedStateNode {
        selector,
        state,
        left,
        right,
        height,
    })
}

fn recorded_state_balance(
    selector: ProgramPointSelector,
    state: Option<ExecutionState>,
    mut left: Option<std::sync::Arc<RecordedStateNode>>,
    mut right: Option<std::sync::Arc<RecordedStateNode>>,
) -> std::sync::Arc<RecordedStateNode> {
    let balance = i16::from(recorded_state_height(left.as_ref()))
        - i16::from(recorded_state_height(right.as_ref()));
    if balance > 1 {
        let left_root = left.as_ref().expect("left-heavy AVL node has a left child");
        if recorded_state_height(left_root.left.as_ref())
            < recorded_state_height(left_root.right.as_ref())
        {
            let pivot = left_root
                .right
                .as_ref()
                .expect("left-right AVL rotation has a pivot");
            left = Some(recorded_state_node(
                pivot.selector.clone(),
                pivot.state.clone(),
                Some(recorded_state_node(
                    left_root.selector.clone(),
                    left_root.state.clone(),
                    left_root.left.clone(),
                    pivot.left.clone(),
                )),
                pivot.right.clone(),
            ));
        }
        let pivot = left.as_ref().expect("left AVL rotation has a pivot");
        return recorded_state_node(
            pivot.selector.clone(),
            pivot.state.clone(),
            pivot.left.clone(),
            Some(recorded_state_node(
                selector,
                state,
                pivot.right.clone(),
                right,
            )),
        );
    }
    if balance < -1 {
        let right_root = right
            .as_ref()
            .expect("right-heavy AVL node has a right child");
        if recorded_state_height(right_root.right.as_ref())
            < recorded_state_height(right_root.left.as_ref())
        {
            let pivot = right_root
                .left
                .as_ref()
                .expect("right-left AVL rotation has a pivot");
            right = Some(recorded_state_node(
                pivot.selector.clone(),
                pivot.state.clone(),
                pivot.left.clone(),
                Some(recorded_state_node(
                    right_root.selector.clone(),
                    right_root.state.clone(),
                    pivot.right.clone(),
                    right_root.right.clone(),
                )),
            ));
        }
        let pivot = right.as_ref().expect("right AVL rotation has a pivot");
        return recorded_state_node(
            pivot.selector.clone(),
            pivot.state.clone(),
            Some(recorded_state_node(
                selector,
                state,
                left,
                pivot.left.clone(),
            )),
            pivot.right.clone(),
        );
    }
    recorded_state_node(selector, state, left, right)
}

fn recorded_state_insert(
    root: Option<&std::sync::Arc<RecordedStateNode>>,
    selector: ProgramPointSelector,
    state: Option<ExecutionState>,
) -> std::sync::Arc<RecordedStateNode> {
    let Some(root) = root else {
        return recorded_state_node(selector, state, None, None);
    };
    match selector.cmp(&root.selector) {
        std::cmp::Ordering::Less => recorded_state_balance(
            root.selector.clone(),
            root.state.clone(),
            Some(recorded_state_insert(root.left.as_ref(), selector, state)),
            root.right.clone(),
        ),
        std::cmp::Ordering::Greater => recorded_state_balance(
            root.selector.clone(),
            root.state.clone(),
            root.left.clone(),
            Some(recorded_state_insert(root.right.as_ref(), selector, state)),
        ),
        std::cmp::Ordering::Equal => {
            recorded_state_node(selector, state, root.left.clone(), root.right.clone())
        }
    }
}

/// [`RecordedStates::iter_newest_first`].
struct RecordedStatesNewestFirst<'a> {
    pending: Vec<&'a RecordedStateNode>,
}

impl<'a> RecordedStatesNewestFirst<'a> {
    fn push_right_spine(&mut self, mut node: Option<&'a RecordedStateNode>) {
        while let Some(current) = node {
            self.pending.push(current);
            node = current.right.as_deref();
        }
    }
}

impl<'a> Iterator for RecordedStatesNewestFirst<'a> {
    type Item = (&'a ProgramPointSelector, &'a ExecutionState);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.pending.pop() {
            self.push_right_spine(node.left.as_deref());
            if let Some(state) = &node.state {
                return Some((&node.selector, state));
            }
        }
        None
    }
}

fn recorded_state_entries<'a>(
    node: Option<&'a RecordedStateNode>,
    entries: &mut Vec<(&'a ProgramPointSelector, &'a ExecutionState)>,
) {
    let Some(node) = node else {
        return;
    };
    recorded_state_entries(node.left.as_deref(), entries);
    if let Some(state) = &node.state {
        entries.push((&node.selector, state));
    }
    recorded_state_entries(node.right.as_deref(), entries);
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecArrayRef {
    point: SpecPoint,
    pointer: SpecExpression,
    element_type: ProgramType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecElaborationContext {
    values: PersistentBinderMap<SpecExpression>,
    integer_values: PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    algebraic_values: PersistentBinderMap<SpecAlgebraicExpression>,
    array_refs: PersistentBinderMap<SpecArrayRef>,
    /// The point a bound array name reads at, when its binding names a state
    /// of its own. A theorem argument that names another state (`old(a)`,
    /// `at(mark, a)`) binds the parameter to that state's array reference, and
    /// an array reference is a point as well as a pointer; without this the
    /// clause's indexing would read at the application's current point. Only a
    /// binding that names another state appears here, so an ordinary array
    /// name keeps reading at `current_point` and carries no state.
    array_points: PersistentBinderMap<SpecPoint>,
    current_point: SpecPoint,
    current_loop_entry: Option<usize>,
    function_contract: bool,
    /// The context is the function entry (`old(...)`), so a resource count
    /// is the entry's population, not the current one.
    at_function_entry: bool,
    /// The recorded state a proof state names, when the context is one:
    /// a resource count there is that state's population, which the spec
    /// form cannot name and the elaboration evaluates.
    reference_state: Option<ExecutionState>,
    call_result_point: Option<ProgramPointSelector>,
    /// Bare `result` names the internal contract-return binding here;
    /// explicit C bindings keep their source identifier and value.
    contract_result_in_scope: bool,
    /// A fixed return value, separate from all lexical bindings.
    contract_result: Option<std::sync::Arc<SpecExpression>>,
    /// Preserve native address checks inside the `defined(...)` special form.
    checking_definedness: bool,
}

impl Default for SpecElaborationContext {
    fn default() -> Self {
        Self {
            values: PersistentBinderMap::default(),
            integer_values: PersistentBinderMap::default(),
            algebraic_values: PersistentBinderMap::default(),
            array_refs: PersistentBinderMap::default(),
            array_points: PersistentBinderMap::default(),
            current_point: SpecPoint::Current,
            current_loop_entry: None,
            at_function_entry: false,
            function_contract: false,
            reference_state: None,
            call_result_point: None,
            contract_result_in_scope: false,
            contract_result: None,
            checking_definedness: false,
        }
    }
}

impl SpecElaborationContext {
    fn with_current_point(current_point: SpecPoint) -> Self {
        Self {
            current_point,
            ..Self::default()
        }
    }

    /// A loop clause's context. `iterations` is the loop's pass count, which
    /// each loop phase binds where it lowers the invariant; a program binding
    /// of that name is `program::iterations`.
    fn for_loop_invariant(loop_index: usize) -> Self {
        Self {
            current_loop_entry: Some(loop_index),
            integer_values: PersistentBinderMap::default().with_inserted(
                LOOP_ITERATIONS_NAME.to_string(),
                crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(
                    crate::kernel::LOOP_ITERATIONS_VARIABLE,
                )),
            ),
            ..Self::default()
        }
    }

    fn for_function_contract() -> Self {
        Self {
            function_contract: true,
            ..Self::default()
        }
    }

    fn old_state(
        &self,
        entry_values: &ProgramValueBindings,
        entry: &crate::kernel::ProgramPoint,
    ) -> Result<Self, String> {
        if self.function_contract {
            return Ok(Self {
                values: self.values.clone(),
                integer_values: self.integer_values.clone(),
                algebraic_values: self.algebraic_values.clone(),
                array_refs: PersistentBinderMap::default(),
                array_points: PersistentBinderMap::default(),
                current_point: SpecPoint::FunctionEntry,
                current_loop_entry: None,
                function_contract: true,
                at_function_entry: true,
                reference_state: None,
                call_result_point: None,
                contract_result_in_scope: false,
                contract_result: None,
                checking_definedness: self.checking_definedness,
            });
        }
        let mut values = entry_values
            .iter()
            .map(|(name, value)| (name.clone(), SpecExpression::Value(value.clone())))
            .collect::<BinderMap<_>>();

        // A `let` name the proof holds as an expression reads the same at
        // the entry. A name the entry records is a local, and a parameter's
        // binding in a proof is that local, not its argument: letting it win
        // here read `old(n)` as the current `n` once the body had reassigned
        // it, while the contract's `old(n)` correctly read the argument.
        for (name, value) in &self.values {
            if !values.contains_key(&name) {
                values.insert(name.clone(), value.clone());
            }
        }

        Ok(Self {
            values: values
                .iter()
                .map(|(name, value)| (name, value.clone()))
                .collect(),
            integer_values: self.integer_values.clone(),
            algebraic_values: self.algebraic_values.clone(),
            array_refs: PersistentBinderMap::default(),
            array_points: PersistentBinderMap::default(),
            current_point: SpecPoint::At(entry.clone()),
            current_loop_entry: None,
            function_contract: false,
            at_function_entry: true,
            reference_state: None,
            call_result_point: None,
            // The return value is a logical proof binding, like `let`.
            // Historical C reads still use their own entry bindings.
            contract_result_in_scope: self.contract_result_in_scope,
            contract_result: self.contract_result.clone(),
            checking_definedness: self.checking_definedness,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct ContractSegment {
    state: ContractSegmentState,
    base: ProgramExpression,
    start: ProgramExpression,
    end: ProgramExpression,
    surface: ContractSegmentSurface,
    /// `uninitialized(p[a..b])`: the callee holds these bytes but makes no
    /// claim that they are initialized. The callee's proof starts with them
    /// unwritten; a produced range reaches the caller unwritten.
    uninitialized: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum ContractSegmentSurface {
    Range {
        base: ContractExpression,
        start: ContractExpression,
        end: ContractExpression,
    },
    StructRange {
        base: ContractExpression,
        start: ContractExpression,
        end: ContractExpression,
        layout: std::sync::Arc<StructRangeLayout>,
    },
    Field {
        /// How the contract spelled the struct the field belongs to, when the
        /// parse had it. A base reached through a link reads as `old->left`
        /// there, which is what the user wrote; the lowered `ProgramExpression` for
        /// the same place reads as `load<int32*>(old)`, which is not.
        base: Option<Box<ContractExpression>>,
        name: String,
        element_width: Option<u32>,
        element_type: Option<ProgramType>,
        /// A scalar field's slot runs to the next field, so its trailing
        /// bytes are padding: the value is this many bytes at its start.
        value_bytes: Option<u32>,
    },
    Object(String),
    ObjectPlace {
        name: crate::kernel::BindingName,
        layout: std::sync::Arc<StructRangeLayout>,
    },
}

/// The imported ABI retained by one range of whole struct objects. Hash the
/// nominal name and size without walking every field; equality still checks
/// the complete ABI, so different layouts cannot be conflated.
#[derive(Clone, Debug, Eq, PartialEq)]
struct StructRangeLayout {
    name: String,
    layout: crate::languages::interface::RecordLayout,
}

impl std::hash::Hash for StructRangeLayout {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.name, state);
        std::hash::Hash::hash(&self.layout.size_bytes(), state);
    }
}

impl ContractSegment {
    pub(crate) fn is_uninitialized(&self) -> bool {
        self.uninitialized
    }

    /// A scalar field's slot runs to the next field, so its trailing bytes
    /// are padding; the value is the field type's width at its start.
    pub(crate) fn scalar_field_value_bytes(&self) -> Option<u32> {
        match &self.surface {
            ContractSegmentSurface::Field { value_bytes, .. } => *value_bytes,
            _ => None,
        }
    }

    pub(crate) fn into_uninitialized(mut self) -> Self {
        self.uninitialized = true;
        self
    }

    /// The written base and bounds of a range segment.
    ///
    /// A diagnostic that names the cell a single-cell condition came from
    /// reads them here: the cell is `<base>[<start>]`, which is the spelling
    /// the reader has in front of them.
    pub(crate) fn surface_range(
        &self,
    ) -> Option<(
        &ContractExpression,
        &ContractExpression,
        &ContractExpression,
    )> {
        match &self.surface {
            ContractSegmentSurface::Range { base, start, end }
            | ContractSegmentSurface::StructRange {
                base, start, end, ..
            } => Some((base, start, end)),
            ContractSegmentSurface::Field { .. }
            | ContractSegmentSurface::Object(_)
            | ContractSegmentSurface::ObjectPlace { .. } => None,
        }
    }

    /// Whether the segment is a whole object of a symbolic layout, its end
    /// that layout's `sizeof`: a range of bytes, whatever its base's type.
    pub(crate) fn spans_symbolic_object(&self) -> bool {
        matches!(&self.end, ProgramExpression::Value(ProgramValue::UInt64(end))
            if matches!(crate::kernel::SymbolicLayoutName::of_term(end), Some((_, None)))
                || crate::kernel::TypeParameterName::of_size_term(end).is_some())
    }

    pub(crate) fn field_element_width(&self) -> Option<u32> {
        if self.spans_symbolic_object() {
            return Some(1);
        }
        match &self.surface {
            ContractSegmentSurface::Field { element_width, .. } => *element_width,
            ContractSegmentSurface::StructRange { layout, .. } => Some(layout.layout.size_bytes()),
            ContractSegmentSurface::Range { .. }
            | ContractSegmentSurface::Object(_)
            | ContractSegmentSurface::ObjectPlace { .. } => None,
        }
    }

    pub(crate) fn field_element_type(&self) -> Option<ProgramType> {
        match &self.surface {
            ContractSegmentSurface::Field { element_type, .. } => *element_type,
            ContractSegmentSurface::Range { .. }
            | ContractSegmentSurface::StructRange { .. }
            | ContractSegmentSurface::Object(_)
            | ContractSegmentSurface::ObjectPlace { .. } => None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ContractSegmentState {
    Current,
    Old,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
    In,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

impl fmt::Display for ComparisonOperator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let form = match self {
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::In => "in",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
        };
        formatter.write_str(form)
    }
}

/// A `.click` `by` clause proving one theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceProof {
    Default,
    Tactic(SmartTactic),
    Script(Vec<ProofTactic>),
}

#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedStatementTransition {
    pub(crate) native_step: std::sync::Arc<crate::kernel::SymbolicExecutionPath>,
    pub(crate) call_result: Option<RetainedProgramValue>,
    /// The call's by-value aggregate parameters as it bound them, recorded
    /// as the call region's parameter point (`R.parameter(name)`).
    pub(crate) call_parameters: Option<crate::kernel::CallParameters>,
    pub(crate) theorem: Theorem,
    /// The kernel fact context the theorem was proved under; retained with
    /// the theorem so the proof object checks its premises against exactly that.
    pub(crate) context: PureFactContext,
    pub(crate) outcome: StatementOutcome,
    pub(crate) execution_facts: crate::kernel::ExecutionFacts,
    pub(crate) path_facts: Vec<Proposition>,
    pub(crate) obligations: Vec<ProofObligation>,
    pub(crate) pure_facts: PureFactList,
    /// Facts emitted by this statement transition itself, after applying the
    /// same state transports reflected in `pure_facts`. This is an
    /// output-sized semantic delta; it deliberately excludes inherited
    /// ambient facts without rediscovering them by set difference.
    pub(crate) introduced_facts: Vec<Proposition>,
    /// Exact clause indices retained by the loop producer, with the same
    /// checked transports as the emitted facts. No positional inference.
    pub(crate) loop_invariant_correspondence: Vec<(usize, Proposition)>,
    /// The loop head's pass count the facts state over, recorded so a proof
    /// past the loop spells it `loop(i).iterations`.
    pub(crate) loop_iterations: Option<crate::kernel::KernelTerm>,
    pub(crate) prerequisite_derivations: Vec<PropositionDerivation>,
    /// Exact entry-state facts consumed while planning this
    /// transition. Kept outside the kernel theorem so collecting certificate
    /// premises cannot perturb execution paths or fresh identities.
    pub(crate) planning_premises: Vec<Proposition>,
    pub(crate) fact_transports: Vec<CertifiedFactTransport>,
    /// Kernel-produced load equation metadata from this exact transition.
    /// This is carried separately from propositions so presentation can use
    /// the producer's state/pointer identity without inferring it from
    /// ambient state.
    pub(crate) generated_load_bindings: Vec<crate::kernel::GeneratedLoadBinding>,
    /// Exact source identities emitted by producer facts in this transition.
    pub(crate) generated_load_source_events: Vec<crate::kernel::GeneratedLoadSourceEvent>,
    /// Checked stable-view call evidence produced by this exact transition.
    /// The loop planner forwards it to the kernel exit candidate instead of
    /// reconstructing it from the post-state.
    pub(crate) borrow_evidence: crate::kernel::CheckedBorrowCallEvidenceSequence,
}

#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedFactTransport {
    pub(crate) source: Proposition,
    pub(crate) target: Proposition,
    pub(crate) theorem: Theorem,
    pub(crate) statement_local: bool,
    /// Exact facts the bounded frame check consumed to carry `source`
    /// across the statement effect; check frames the fact from exactly
    /// these.
    pub(crate) frame_premises: Vec<Proposition>,
}

/// A tactic in an explicit `.click` proof script.
///
/// Tactics are classified by [`ProofTactic::class`]. A `SourceProof::Script`
/// certificate is not considered fully expanded while it contains a smart
/// tactic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofTactic {
    CloseInvariantsBy(Vec<ProofTactic>),
    Mark(String),
    /// A `step` form followed by proofs of the obligations its fast path
    /// leaves open: `step() by { ... }` or `step() { requires P by ...; }`.
    StepProved {
        step: Box<ProofTactic>,
        proof: StepProof,
    },
    Step,
    StepContract(ContractApplication),
    /// Name the scalar value assigned by this checked statement.
    StepBind(String),
    StepCall(CallBinderTransport),
    /// `name(args, { binder: instance })`: one application of a user-defined
    /// tactic's verified contract, with no C statement.
    UserTactic(CallBinderTransport),
    /// A tactic Click adds to a script, never written in source: the end of
    /// a user-defined tactic's proof steps its procedure's `return` and
    /// closes its claims. It occupies no source position, so the tactics
    /// the author wrote keep their source indices; indexing unwraps it.
    Synthetic(Box<ProofTactic>),
    SmartExecute,
    ExecuteUntil(ExecutionPoint),
    UnfoldProposition(ClickProposition),
    UnfoldFunction(ClickFunctionApplication),
    UnfoldResource(ResourceClause),
    ReleaseView(ResourceClause),
    /// `let { witness: name, ... } = unfold(resource)` on a declared
    /// resource: the unfold, with each named `let ... where` witness of the
    /// opened body bound to a proof name.
    UnfoldWitnesses {
        resource: ResourceClause,
        names: Vec<(String, String)>,
    },
    FoldResource(ResourceClause),
    Induct {
        parameter: String,
        hypothesis: String,
    },
    ApplyInduction {
        hypothesis: String,
        arguments: Vec<ContractExpression>,
    },
    /// Apply an established implication, proving its antecedents.
    ApplyFact(ClickProposition),
    ApplyFactUsing {
        fact: ClickProposition,
        premises: Vec<ClickProposition>,
    },
    ApplyTheorem(TheoremApplication),
    ApplyTheoremUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    Have(ProofHave),
    Open(ProofOpen),
    If(ProofIf),
    Match(std::sync::Arc<ProofMatch>),
    Cases(ProofCases),
    Both(ProofBoth),
    All(ProofAll),
    Branch(ProofBranch),
    CallOutcomes(ProofCallOutcomes),
    Loop(StructuralClause),
    ObserveResource(ResourceClause),
    ObserveSubject(ResourceSubject),
    /// Checked operation on iterated guarded ownership.
    Iterated(IteratedTactic),
    Witness(ProofWitness),
    LetSatisfy(ProofLetSatisfy),
    Choose(ProofChoice),
    CheckTerminationLocal(String),
    CheckTerminationComponent {
        function: String,
        strict: bool,
    },
    CheckTerminationCallbacks,
    Close,
    Known,
    Normalize,
    NormalizeUsing(Vec<ClickProposition>),
    /// A compatibility check used in verification. It has no expansion spelling.
    CompatibilityNormalize(Option<Vec<ClickProposition>>),
    ArithmeticUsing(Vec<ClickProposition>),
    Intro,
    /// `let name = intro()`: introduce a universal goal's variable under a
    /// name the proof chooses instead of the one the proposition wrote.
    IntroAs(String),
    IntroBinder(SurfaceBinder),
    IntroBlock {
        binder: Option<SurfaceBinder>,
        body: Vec<ProofTactic>,
    },
    Enumerate,
    Contradiction(ClickProposition),
    CloseInvariants,
    Rewrite(ClickProposition),
    Preserve(ClickProposition),
    Transport {
        source: ClickProposition,
        target: ClickProposition,
    },
    TransportUsing {
        source: ClickProposition,
        target: ClickProposition,
        premises: Vec<ClickProposition>,
    },
    /// Substitute consecutive universal binders, preserving the residual body and guards.
    Instantiate {
        quantified: ClickProposition,
        arguments: Vec<ContractExpression>,
    },
    Solve,
    /// The driver schedules ordinary `solve` for every remaining claim.
    /// This has no written spelling; explicit `close()` selects one goal.
    ImplicitSolve,
    SolveUsing(ProofSolveUsing),

    /// Dev-only proof hole. Closes the enclosing proof unit without checking
    /// anything. Parses only while `verification::with_allow_sorry` is active
    /// (set solely by `click verify --allow-sorry`); every other use is
    /// rejected, and admissions are reported loudly and rejected by
    /// `click audit`, `click expand`, and the gate.
    Sorry,
}

/// Whether these tactics are exactly one complete `sorry` body: a whole
/// contract admitted without checking, like an `extern` declaration.
/// A `sorry` nested inside a script is admitted goal-by-goal by the linear
/// script runner (with a loud warning).
pub fn is_complete_sorry_body(tactics: &[ProofTactic]) -> bool {
    matches!(tactics, [ProofTactic::Sorry])
}

/// Whether `sorry` appears anywhere except as a complete `have` body.
/// Such positions cannot be admitted minimally (a bare `sorry` would cover
/// an unbounded suffix), so they are rejected with a diagnostic. A `sorry`
/// that is a complete `have` body is admitted by the `have` solver.
pub fn sorry_outside_have_bodies(tactics: &[ProofTactic]) -> bool {
    tactics
        .iter()
        .any(|tactic| tactic_sorry_outside_have(tactic, false))
}

fn tactic_sorry_outside_have(tactic: &ProofTactic, in_have: bool) -> bool {
    if matches!(tactic, ProofTactic::Sorry) {
        return !in_have;
    }
    // An obligation proves a fact as a `have` does.
    tactic.children().into_iter().any(|child| match child {
        TacticChild::Continuing(proof) => child_proof_sorry_outside_have(proof, in_have),
        TacticChild::Obligation(proof) => child_proof_sorry_outside_have(proof, true),
    })
}

fn child_proof_sorry_outside_have(proof: ChildProof<'_>, in_have: bool) -> bool {
    match proof {
        ChildProof::Script(tactics) => tactic_sorry_outside_have_in(tactics, in_have),
        ChildProof::Source(proof) => source_proof_sorry_outside_have(proof, in_have),
    }
}

fn tactic_sorry_outside_have_in(tactics: &[ProofTactic], in_have: bool) -> bool {
    tactics
        .iter()
        .any(|tactic| tactic_sorry_outside_have(tactic, in_have))
}

fn source_proof_sorry_outside_have(proof: &SourceProof, in_have: bool) -> bool {
    match proof {
        SourceProof::Script(tactics) => tactic_sorry_outside_have_in(tactics, in_have),
        SourceProof::Default | SourceProof::Tactic(_) => false,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SimpleTactic {
    Mark,
    StatementTransition,
    /// One application of a user-defined tactic's verified contract.
    UserTactic,
    UnfoldPredicate,
    UnfoldFunction,
    UnfoldResource,
    ObserveResource,
    Induct,
    ApplyInduction,
    ApplyTheorem,
    Witness,
    LetSatisfy,
    Choose,
    Termination,
    Known,
    Normalize,
    Intro,
    Enumerate,
    Contradiction,
    Rewrite,
    FactTransport,
    Instantiate,
    FoldResource,
    ReleaseView,
    IteratedOwnership,
}

/// The smart tactics, each one engine
/// (`docs/concepts/smart-and-simple-tactics.md`): `solve` closes one goal
/// and wraps `arithmetic`; `execute` runs C; `step_until` is a variant
/// of `execute`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SmartTacticKind {
    Arithmetic,
    Solve,
    Execute,
}

/// A simple tactic written with one argument elided. The search behind it
/// only looks the argument up, and the same tactic with the argument
/// written is [`ElidedArgument::written_form`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElidedArgument {
    /// `apply(theorem(args))`: the theorem's premises.
    /// `apply(ih(m))`: the hypothesis's premises.
    /// `transport(P, Q)`: the frame evidence.
    FrameEvidence,
}

impl ElidedArgument {
    /// The simple tactic the elided form is, once its argument is written.
    pub fn written_form(self) -> SimpleTactic {
        match self {
            Self::FrameEvidence => SimpleTactic::FactTransport,
        }
    }
}

/// What a smart site searches with. Each runs on the smart budget, is
/// refused by a certificate, and is replaced by `click expand`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SmartSite {
    /// One of the four smart tactics.
    Engine(SmartTacticKind),
    /// A simple tactic whose argument a lookup fills.
    Elided(ElidedArgument),
    /// Bare `close_invariants()`: a fixed expansion into
    /// `close_invariants() by { ... }` with `close()` on each member.
    CloseInvariants,
    /// What an omitted proof and the end of a script mean: execute the C
    /// that remains and `solve` each open goal.
    Implicit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlTactic {
    Intro,
    Match,
    CloseInvariants,
    /// A `step` with proofs of its open obligations.
    StepProofs,
    Both,
    Have,
    Open,
    If,
    Cases,
    Branch,
    CallOutcomes,
    Loop,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TacticClass {
    Simple(SimpleTactic),
    Smart(SmartSite),
    Control(ControlTactic),
    /// Dev-only proof hole; never a real proof step. Anything that would
    /// expand, certify, or audit a tactic must reject this class outright.
    Sorry,
}

impl TacticClass {
    /// The class of a smart tactic itself.
    pub fn smart(kind: SmartTacticKind) -> Self {
        Self::Smart(SmartSite::Engine(kind))
    }
}

/// One user-selectable proof-tactic form exposed by the Surface Click parser.
/// Internal planner-only variants don't appear in this registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PublicTacticForm {
    pub id: &'static str,
    pub syntax: &'static str,
    pub class: &'static str,
}

/// Canonical public tactic forms used by the reference coverage test.
pub const PUBLIC_TACTIC_FORMS: &[PublicTacticForm] = &[
    PublicTacticForm {
        id: "mark",
        syntax: "mark name;",
        class: "simple",
    },
    PublicTacticForm {
        id: "step",
        syntax: "step()",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-result",
        syntax: "let { result: name } = step()",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-contract",
        syntax: "step(Contract)",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-contract-application",
        syntax: "step(Contract, { handle: instance, ... })",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-call",
        syntax: "step(callee, { binder: instance })",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-contract-map",
        syntax: "step(Contract, { binder: instance })",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-by",
        syntax: "step(...) by { ... }",
        class: "control",
    },
    PublicTacticForm {
        id: "step-requires",
        syntax: "step(...) { requires P by ...; }",
        class: "control",
    },
    PublicTacticForm {
        id: "user-tactic",
        syntax: "name(args, { binder: instance })",
        class: "simple",
    },
    PublicTacticForm {
        id: "step-until",
        syntax: "step_until",
        class: "smart",
    },
    PublicTacticForm {
        id: "unfold-predicate",
        syntax: "unfold(predicate(args))",
        class: "simple",
    },
    PublicTacticForm {
        id: "unfold-function",
        syntax: "unfold(function(args))",
        class: "simple",
    },
    PublicTacticForm {
        id: "unfold-resource",
        syntax: "unfold(resource(args))",
        class: "simple",
    },
    PublicTacticForm {
        id: "fold-resource",
        syntax: "fold(resource)",
        class: "simple",
    },
    PublicTacticForm {
        id: "release-view",
        syntax: "release_view(range)",
        class: "simple",
    },
    PublicTacticForm {
        id: "unfold-slot",
        syntax: "unfold(resource(args)[i])",
        class: "simple",
    },
    PublicTacticForm {
        id: "fold-slot",
        syntax: "fold(resource(args)[i])",
        class: "simple",
    },
    PublicTacticForm {
        id: "fold-iterated-clause",
        syntax: "fold(resource(args)[..])",
        class: "simple",
    },
    PublicTacticForm {
        id: "unfold-iterated-clause",
        syntax: "unfold(resource(args)[..])",
        class: "simple",
    },
    PublicTacticForm {
        id: "induct",
        syntax: "let ih = induct(value)",
        class: "simple",
    },
    PublicTacticForm {
        id: "proof-match",
        syntax: "match value [ensuring { ... }] { Type::Variant(fields)",
        class: "control",
    },
    PublicTacticForm {
        id: "apply-induction",
        syntax: "apply(ih(m))",
        class: "simple",
    },
    PublicTacticForm {
        id: "apply-fact",
        syntax: "apply(fact)",
        class: "simple",
    },
    PublicTacticForm {
        id: "apply-theorem",
        syntax: "apply(theorem(args))",
        class: "simple",
    },
    PublicTacticForm {
        id: "have",
        syntax: "have P by",
        class: "control",
    },
    PublicTacticForm {
        id: "with",
        syntax: "with(resource)",
        class: "control",
    },
    PublicTacticForm {
        id: "if",
        syntax: "if P",
        class: "control",
    },
    PublicTacticForm {
        id: "cases",
        syntax: "cases {",
        class: "control",
    },
    PublicTacticForm {
        id: "all",
        syntax: "all {",
        class: "control",
    },
    PublicTacticForm {
        id: "branch",
        syntax: "branch",
        class: "control",
    },
    PublicTacticForm {
        id: "outcomes",
        syntax: "outcomes { returned => { ... } threw => { ... } }",
        class: "control",
    },
    PublicTacticForm {
        id: "loop",
        syntax: "loop",
        class: "control",
    },
    PublicTacticForm {
        id: "observe-resource",
        syntax: "observe(resource)",
        class: "simple",
    },
    PublicTacticForm {
        id: "witness",
        syntax: "witness(",
        class: "simple",
    },
    PublicTacticForm {
        id: "obtain",
        syntax: "= obtain(",
        class: "simple",
    },
    PublicTacticForm {
        id: "close",
        syntax: "close()",
        class: "smart",
    },
    PublicTacticForm {
        id: "normalize",
        syntax: "normalize()",
        class: "simple",
    },
    PublicTacticForm {
        id: "normalize-using",
        syntax: "normalize() using",
        class: "simple",
    },
    PublicTacticForm {
        id: "preserve",
        syntax: "preserve(resource, region)",
        class: "simple",
    },
    PublicTacticForm {
        id: "intro",
        syntax: "intro()",
        class: "simple",
    },
    PublicTacticForm {
        id: "intro-as",
        syntax: "let name = intro()",
        class: "simple",
    },
    PublicTacticForm {
        id: "enumerate",
        syntax: "enumerate()",
        class: "simple",
    },
    PublicTacticForm {
        id: "contradiction",
        syntax: "contradiction(P)",
        class: "simple",
    },
    PublicTacticForm {
        id: "contradiction-false",
        syntax: "contradiction()",
        class: "simple",
    },
    PublicTacticForm {
        id: "rewrite",
        syntax: "rewrite(from, to)",
        class: "simple",
    },
    PublicTacticForm {
        id: "transport",
        syntax: "transport(P, Q)",
        class: "smart",
    },
    PublicTacticForm {
        id: "transport-using",
        syntax: "transport(P, Q) using",
        class: "simple",
    },
    PublicTacticForm {
        id: "instantiate",
        syntax: "instantiate(F, value, ...)",
        class: "simple",
    },
    PublicTacticForm {
        id: "close-using",
        syntax: "close() using",
        class: "smart",
    },
    PublicTacticForm {
        id: "check-termination-local",
        syntax: "check_termination_local(",
        class: "simple",
    },
    PublicTacticForm {
        id: "check-termination-component",
        syntax: "check_termination_component(",
        class: "simple",
    },
    PublicTacticForm {
        id: "check-termination-callbacks",
        syntax: "check_termination_callbacks()",
        class: "simple",
    },
];

mod proof_certificate;
pub use proof_certificate::*;

/// One child proof of a structured tactic, as [`ProofTactic::children`]
/// yields it.
#[derive(Clone, Copy)]
pub(crate) enum TacticChild<'a> {
    /// A block that continues the tactic's own proof: an `if`, `branch`,
    /// `match`, `cases`, induction or `outcomes` arm, a `with` body, a side
    /// of `both`, a `close_invariants by` body, or a loop's `initialize` or
    /// `maintain` proof.
    Continuing(ChildProof<'a>),
    /// A proof of a separate proposition, as a `have` body is: a `have`, the
    /// close proof of a `with`, or a step's obligation proofs.
    Obligation(ChildProof<'a>),
}

/// The written form of a child proof.
#[derive(Clone, Copy)]
pub(crate) enum ChildProof<'a> {
    Script(&'a [ProofTactic]),
    /// A `have`, step-requirement or loop proof, which may be the default
    /// proof or a smart tactic instead of a script.
    Source(&'a SourceProof),
}

impl<'a> ChildProof<'a> {
    /// The written tactics, when the child is a script.
    pub(crate) fn tactics(self) -> Option<&'a [ProofTactic]> {
        match self {
            Self::Script(tactics) => Some(tactics),
            Self::Source(proof) => proof.tactics(),
        }
    }
}

impl ProofTactic {
    /// Every child proof of this tactic, in source order. This is the one
    /// place that knows where each structured tactic keeps its children: a
    /// traversal matches the tactics it treats specially and recurses
    /// through this for the rest, so a new control tactic is visited
    /// everywhere once it is listed here. A leaf has no children. The step a
    /// `StepProved` proves is a leaf of the tactic, not a child proof.
    pub(crate) fn children(&self) -> Vec<TacticChild<'_>> {
        use ChildProof::{Script, Source};
        use TacticChild::{Continuing, Obligation};
        match self {
            Self::CloseInvariantsBy(body) => vec![Continuing(Script(body))],
            Self::StepProved { proof, .. } => match proof {
                StepProof::By(body) => vec![Obligation(Script(body))],
                StepProof::Requires(entries) => entries
                    .iter()
                    .map(|entry| Obligation(Source(&entry.have.proof)))
                    .collect(),
            },
            Self::Have(have) => vec![Obligation(Source(&have.proof))],
            Self::IntroBlock { body, .. } => vec![Obligation(Script(body))],
            Self::Open(open) => vec![Continuing(Script(&open.tactics))],
            Self::If(proof_if) => vec![
                Continuing(Script(&proof_if.then_tactics)),
                Continuing(Script(&proof_if.else_tactics)),
            ],
            Self::Match(proof_match) => proof_match
                .arms
                .iter()
                .map(|arm| Continuing(Script(&arm.tactics)))
                .collect(),
            Self::Cases(cases) => cases
                .arms
                .iter()
                .map(|arm| Continuing(Script(&arm.tactics)))
                .collect(),
            Self::All(all) => all
                .arms
                .iter()
                .map(|arm| Continuing(Script(&arm.tactics)))
                .collect(),
            Self::Both(both) => vec![
                Continuing(Script(&both.left_tactics)),
                Continuing(Script(&both.right_tactics)),
            ],
            Self::Branch(branch) => vec![
                Continuing(Script(&branch.then_tactics)),
                Continuing(Script(&branch.else_tactics)),
            ],
            Self::CallOutcomes(outcomes) => vec![
                Continuing(Script(&outcomes.returned_tactics)),
                Continuing(Script(&outcomes.threw_tactics)),
            ],
            Self::Loop(clause) => clause
                .initialize_proof()
                .into_iter()
                .chain(clause.preserve_proof())
                .chain(clause.otherwise_proof())
                .map(|proof| Continuing(Source(proof)))
                .collect(),
            _ => Vec::new(),
        }
    }
}

impl ProofTactic {
    pub fn class(&self) -> TacticClass {
        match self {
            Self::Synthetic(inner) => inner.class(),
            Self::Mark(_) => TacticClass::Simple(SimpleTactic::Mark),
            Self::Step | Self::StepBind(_) | Self::StepContract(_) | Self::StepCall(_) => {
                TacticClass::Simple(SimpleTactic::StatementTransition)
            }
            Self::UserTactic(_) => TacticClass::Simple(SimpleTactic::UserTactic),
            Self::UnfoldProposition(_) => TacticClass::Simple(SimpleTactic::UnfoldPredicate),
            Self::UnfoldFunction(_) => TacticClass::Simple(SimpleTactic::UnfoldFunction),
            Self::UnfoldResource(_) | Self::UnfoldWitnesses { .. } => {
                TacticClass::Simple(SimpleTactic::UnfoldResource)
            }
            Self::ObserveResource(_) | Self::ObserveSubject(_) => {
                TacticClass::Simple(SimpleTactic::ObserveResource)
            }
            Self::Iterated(_) => TacticClass::Simple(SimpleTactic::IteratedOwnership),
            Self::Induct { .. } => TacticClass::Simple(SimpleTactic::Induct),
            Self::ApplyInduction { .. } => TacticClass::Simple(SimpleTactic::ApplyInduction),
            Self::ApplyFact(_)
            | Self::ApplyFactUsing { .. }
            | Self::ApplyTheorem(_)
            | Self::ApplyTheoremUsing { .. } => TacticClass::Simple(SimpleTactic::ApplyTheorem),
            Self::Witness(_) => TacticClass::Simple(SimpleTactic::Witness),
            Self::LetSatisfy(_) => TacticClass::Simple(SimpleTactic::LetSatisfy),
            Self::Choose(_) => TacticClass::Simple(SimpleTactic::Choose),
            Self::CheckTerminationLocal(_)
            | Self::CheckTerminationComponent { .. }
            | Self::CheckTerminationCallbacks => TacticClass::Simple(SimpleTactic::Termination),
            Self::Known => TacticClass::Simple(SimpleTactic::Known),
            Self::Normalize | Self::NormalizeUsing(_) | Self::CompatibilityNormalize(_) => {
                TacticClass::Simple(SimpleTactic::Normalize)
            }
            Self::ArithmeticUsing(_) => TacticClass::smart(SmartTacticKind::Arithmetic),

            Self::Preserve(_) => TacticClass::Simple(SimpleTactic::FactTransport),
            Self::Intro | Self::IntroAs(_) | Self::IntroBinder(_) => {
                TacticClass::Simple(SimpleTactic::Intro)
            }
            Self::Enumerate => TacticClass::Simple(SimpleTactic::Enumerate),
            Self::Contradiction(_) => TacticClass::Simple(SimpleTactic::Contradiction),
            Self::CloseInvariants => TacticClass::Smart(SmartSite::CloseInvariants),
            Self::CloseInvariantsBy(_) => TacticClass::Control(ControlTactic::CloseInvariants),
            Self::StepProved { .. } => TacticClass::Control(ControlTactic::StepProofs),
            Self::Rewrite(_) => TacticClass::Simple(SimpleTactic::Rewrite),
            Self::Transport { .. } => {
                TacticClass::Smart(SmartSite::Elided(ElidedArgument::FrameEvidence))
            }
            Self::TransportUsing { .. } => TacticClass::Simple(SimpleTactic::FactTransport),
            Self::Instantiate { .. } => TacticClass::Simple(SimpleTactic::Instantiate),
            Self::FoldResource(_) => TacticClass::Simple(SimpleTactic::FoldResource),
            Self::ReleaseView(_) => TacticClass::Simple(SimpleTactic::ReleaseView),
            Self::SmartExecute | Self::ExecuteUntil(_) => {
                TacticClass::smart(SmartTacticKind::Execute)
            }
            Self::Close | Self::Solve | Self::SolveUsing(_) => {
                TacticClass::smart(SmartTacticKind::Solve)
            }
            Self::ImplicitSolve => TacticClass::Smart(SmartSite::Implicit),
            Self::Have(_) => TacticClass::Control(ControlTactic::Have),
            Self::IntroBlock { .. } => TacticClass::Control(ControlTactic::Intro),
            Self::Open(_) => TacticClass::Control(ControlTactic::Open),
            Self::If(_) => TacticClass::Control(ControlTactic::If),
            Self::Match(_) => TacticClass::Control(ControlTactic::Match),
            Self::Cases(_) => TacticClass::Control(ControlTactic::Cases),
            Self::Both(_) | Self::All(_) => TacticClass::Control(ControlTactic::Both),
            Self::Branch(_) => TacticClass::Control(ControlTactic::Branch),
            Self::CallOutcomes(_) => TacticClass::Control(ControlTactic::CallOutcomes),
            Self::Loop(_) => TacticClass::Control(ControlTactic::Loop),
            Self::Sorry => TacticClass::Sorry,
        }
    }
}

impl SmartTactic {
    /// Distinguish omitted-proof attribution from a written `close()` site.
    pub fn site(self) -> SmartSite {
        match self {
            Self::ImplicitTail => SmartSite::Implicit,
            Self::Solve => SmartSite::Engine(SmartTacticKind::Solve),
        }
    }
}

/// The proofs written on a `step` for the obligations its fast path leaves
/// open (`docs/reference/tactics/index.md`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepProof {
    /// `step() by ...`: the body proves the one remaining obligation.
    By(Vec<ProofTactic>),
    /// `step() { requires P by ...; }`: each entry proves the obligation `P`
    /// states.
    Requires(Vec<StepRequirement>),
}

/// One `requires [label:] P by ...` entry of a `step`. Its proposition and
/// proof are checked as a `have` at the step's pre-state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepRequirement {
    pub(crate) label: Option<String>,
    pub(crate) have: ProofHave,
}

/// The checked form of [`StepProof`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepProofCertificate {
    By(Box<ProofCertificate>),
    Requires(Vec<StepRequirementCertificate>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepRequirementCertificate {
    pub(crate) label: Option<String>,
    pub(crate) proposition: ClickProposition,
    pub(crate) proof: ProofCertificate,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofHave {
    proposition: ClickProposition,
    proof: SourceProof,
}

impl ProofHave {
    /// Check the short forms as the same single solve step as the block form,
    /// so a failed step retains its diagnostic. Keep the written source proof
    /// unchanged for inventory, capture, and source locations.
    fn checking_proof(&self) -> std::borrow::Cow<'_, SourceProof> {
        match &self.proof {
            SourceProof::Default | SourceProof::Tactic(SmartTactic::Solve) => {
                std::borrow::Cow::Owned(SourceProof::Script(vec![ProofTactic::Solve]))
            }
            _ => std::borrow::Cow::Borrowed(&self.proof),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofOpen {
    resource: ResourceClause,
    tactics: Vec<ProofTactic>,
    // The captured tail of a deferred close, merged into the matching scope
    // when the outcome proof is assembled.
    deferred_tail: Option<DeferredOpenTail>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DeferredOpenTail {
    Restore,
    AlreadyRestored,
}

impl ProofOpen {
    pub(crate) fn deferred_block_tail(
        resource: ResourceClause,
        tactics: Vec<ProofTactic>,
        tail: DeferredOpenTail,
    ) -> Self {
        Self {
            resource,
            tactics,
            deferred_tail: Some(tail),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofIf {
    condition: ClickProposition,
    /// What the rejoined proof keeps when the arms end in different states.
    ensuring: Option<Vec<ProofAssertion>>,
    then_tactics: Vec<ProofTactic>,
    else_tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofInductionArm {
    type_name: String,
    variant: String,
    bindings: Vec<String>,
    tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateInductionArm {
    type_name: String,
    variant: String,
    bindings: Vec<String>,
    proof: Box<ProofCertificate>,
}

/// Prove the exact conjuncts in isolated child scopes of the current goal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofBoth {
    pub left_tactics: Vec<ProofTactic>,
    pub right_tactics: Vec<ProofTactic>,
}

/// Proofs of the conjuncts of the focused goal, in goal order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofAll {
    pub(crate) arms: Vec<ProofAllArm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ProofAllArm {
    pub(crate) proposition: ClickProposition,
    pub(crate) tactics: Vec<ProofTactic>,
}

/// Explicit elimination of a disjunctive fact: proof checking requires the
/// disjunction of the arms' assumptions, grouped left to right as `or`
/// parses, to be an available fact, then checks each arm under exactly its
/// assumption. Every arm is written; nothing is searched.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofCases {
    arms: Vec<ProofCaseArm>,
}

/// One arm of `cases`: the disjunct it assumes and the proof under it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofCaseArm {
    assumption: ClickProposition,
    tactics: Vec<ProofTactic>,
}

impl ProofCaseArm {
    pub(crate) fn new(assumption: ClickProposition, tactics: Vec<ProofTactic>) -> Self {
        Self {
            assumption,
            tactics,
        }
    }

    pub(crate) fn assumption(&self) -> &ClickProposition {
        &self.assumption
    }

    pub(crate) fn tactics(&self) -> &[ProofTactic] {
        &self.tactics
    }
}

impl ProofCases {
    /// At least two arms; a parser or certificate never builds fewer.
    pub(crate) fn new(arms: Vec<ProofCaseArm>) -> Self {
        debug_assert!(arms.len() >= 2, "`cases` has at least two arms");
        Self { arms }
    }

    pub(crate) fn arms(&self) -> &[ProofCaseArm] {
        &self.arms
    }

    /// The disjunction the arms eliminate.
    pub(crate) fn disjunction(&self) -> ClickProposition {
        case_arms_disjunction(&self.arms)
    }

    /// The same arms with each assumption and tactic list rewritten.
    pub(crate) fn try_map<E>(
        &self,
        mut assumption: impl FnMut(&ClickProposition) -> Result<ClickProposition, E>,
        mut tactics: impl FnMut(&[ProofTactic]) -> Result<Vec<ProofTactic>, E>,
    ) -> Result<Self, E> {
        Ok(Self {
            arms: self
                .arms
                .iter()
                .map(|arm| {
                    Ok(ProofCaseArm {
                        assumption: assumption(&arm.assumption)?,
                        tactics: tactics(&arm.tactics)?,
                    })
                })
                .collect::<Result<_, E>>()?,
        })
    }

    /// The two-armed form the kernel splits on: every arm but the last
    /// against the last, with the leading arms as a nested `cases`.
    pub(crate) fn binary(&self) -> (ClickProposition, Vec<ProofTactic>, Vec<ProofTactic>) {
        let (last, leading) = self.arms.split_last().expect("`cases` has arms");
        let left = match leading {
            [only] => only.tactics.clone(),
            _ => vec![ProofTactic::Cases(Self {
                arms: leading.to_vec(),
            })],
        };
        (self.disjunction(), left, last.tactics.clone())
    }

    /// Rebuilds the arms of a two-armed certificate, flattening a left arm
    /// that is itself the `cases` on the left disjunct, as [`Self::binary`]
    /// writes one.
    pub(crate) fn from_binary(
        disjunction: &ClickProposition,
        left: Vec<ProofTactic>,
        right: Vec<ProofTactic>,
    ) -> Self {
        let (left_assumption, right_assumption) = split_case_disjunction(disjunction)
            .unwrap_or_else(|| (disjunction.clone(), disjunction.clone()));
        let mut arms = match left.as_slice() {
            [ProofTactic::Cases(inner)] if inner.disjunction() == left_assumption => {
                inner.arms.clone()
            }
            _ => vec![ProofCaseArm {
                assumption: left_assumption,
                tactics: left,
            }],
        };
        arms.push(ProofCaseArm {
            assumption: right_assumption,
            tactics: right,
        });
        Self { arms }
    }
}

/// The two disjuncts of a written `cases` disjunction. A disjunction read at
/// a state, `at(s, A or B)`, splits into `at(s, A)` and `at(s, B)`.
fn split_case_disjunction(
    disjunction: &ClickProposition,
) -> Option<(ClickProposition, ClickProposition)> {
    match disjunction {
        ClickProposition::Or(left, right) => Some((left.as_ref().clone(), right.as_ref().clone())),
        ClickProposition::At {
            selector,
            proposition,
        } => {
            let (left, right) = split_case_disjunction(proposition)?;
            let at = |proposition| ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(proposition),
            };
            Some((at(left), at(right)))
        }
        _ => None,
    }
}

/// The disjunction of the arms' assumptions, grouped left to right.
pub(crate) fn case_arms_disjunction(arms: &[ProofCaseArm]) -> ClickProposition {
    let mut arms = arms.iter();
    let first = arms.next().expect("`cases` has arms").assumption.clone();
    arms.fold(first, |disjunction, arm| {
        ClickProposition::Or(Box::new(disjunction), Box::new(arm.assumption.clone()))
    })
}

/// Explicit proof-by-constructor-cases, not evaluation of a pure expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofMatch {
    scrutinee: ContractExpression,
    /// What the rejoined proof keeps when the arms end in different states.
    ensuring: Option<Vec<ProofAssertion>>,
    arms: Vec<ProofInductionArm>,
}

impl ProofMatch {
    pub(in crate::surface) fn arm_count(&self) -> usize {
        self.arms.len()
    }

    /// The checked `match` step with one proof per written arm, in order.
    pub(in crate::surface) fn certificate_step(
        &self,
        ensuring: Option<Vec<ProofAssertion>>,
        proofs: Vec<ProofCertificate>,
    ) -> ProofStep {
        ProofStep::Match {
            scrutinee: self.scrutinee.clone(),
            ensuring,
            arms: self
                .arms
                .iter()
                .zip(proofs)
                .map(|(arm, proof)| CertificateInductionArm {
                    type_name: arm.type_name.clone(),
                    variant: arm.variant.clone(),
                    bindings: arm.bindings.clone(),
                    proof: Box::new(proof),
                })
                .collect(),
        }
    }

    /// The C local an execution-generated `match` splits on.
    pub(in crate::surface) fn describe_scrutinee(&self) -> String {
        crate::surface::diagnostics::describe_contract_expression(&self.scrutinee)
    }

    /// The written form with each arm's tactics elided:
    /// `match s { Shape::Circle(s_0) => { ... }, Shape::Empty => { ... } }`.
    pub(in crate::surface) fn outline(&self) -> String {
        let arms = self
            .arms
            .iter()
            .map(|arm| {
                let fields = if arm.bindings.is_empty() {
                    String::new()
                } else {
                    format!("({})", arm.bindings.join(", "))
                };
                format!("{}::{}{fields} => {{ ... }}", arm.type_name, arm.variant)
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!("match {} {{ {arms} }}", self.describe_scrutinee())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofBranch {
    ensuring: Option<Vec<ProofAssertion>>,
    then_tactics: Vec<ProofTactic>,
    else_tactics: Vec<ProofTactic>,
}

/// Explicit proof arms for the checked edge of one potentially throwing call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofCallOutcomes {
    /// Optional proof names for the returned and thrown payloads, in that order.
    pub payload_bindings: [Option<String>; 2],
    pub returned_tactics: Vec<ProofTactic>,
    pub threw_tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofSolveUsing {
    premises: Vec<ClickProposition>,
}

/// The checked signed-int32 arithmetic rule family. Surface nodes retain
/// source expressions so explicit certificates round-trip without erasing
/// their source origin before the kernel performs its independent validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedIntervalPlan {
    pub nodes: Vec<SignedArithmeticStep>,
    pub conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SignedInt32Comparison {
    LessThan,
    LessEqual,
    Equal,
    Disequal,
    /// `ult`: the `uint32` order `<` of the two words.
    UnsignedLessThan,
    /// `ule`: the `uint32` order `<=` of the two words.
    UnsignedLessEqual,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SignedInt32Interval {
    pub lower: i64,
    pub upper: i64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SignedArithmeticStep {
    Premise {
        index: usize,
        proposition: ClickProposition,
        result: ClickProposition,
    },
    Scale {
        source: usize,
        coefficient: ContractExpression,
        result: ClickProposition,
    },
    Add {
        left: usize,
        right: usize,
        result: ClickProposition,
    },
    EqualityToLessEqual {
        source: usize,
        reverse: bool,
        result: ClickProposition,
    },
    EqualityFromBounds {
        lower: usize,
        upper: usize,
        result: ClickProposition,
    },
    StrictFromDisequal {
        bound: usize,
        disequal: usize,
        result: ClickProposition,
    },
    Trivial {
        result: ClickProposition,
    },
    /// One opaque term's int32 range bound, `t <= 2147483647` or
    /// `-2147483648 <= t`.
    Int32Range {
        result: ClickProposition,
    },
    IntervalFromAffine {
        source: usize,
        term: ContractExpression,
        lower: i64,
        upper: i64,
    },
    IntervalFromAffineDirect {
        source: usize,
        term: ContractExpression,
        lower: i64,
        upper: i64,
    },
    IntervalAtom {
        term: ContractExpression,
        lower: i64,
        upper: i64,
    },
    IntervalIntersect {
        left: usize,
        right: usize,
        result: SignedInt32Interval,
    },
    DefinedPremise {
        index: usize,
        term: ContractExpression,
    },
    IntervalAdd {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedInt32Interval,
    },
    IntervalAddBounded {
        left: usize,
        right: usize,
        result: SignedInt32Interval,
    },
    IntervalSubtract {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedInt32Interval,
    },
    IntervalMultiply {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedInt32Interval,
    },
    /// Remainder after a bounded addition, using a checked interval for the
    /// original remainder. Both the original and resulting dividends are nonnegative.
    IntervalRemainderAdd {
        operand: usize,
        remainder: usize,
        addend: i32,
        divisor: i32,
        result: SignedInt32Interval,
    },
    IntervalRemainder {
        operand: usize,
        divisor: i32,
        defined: usize,
        result: SignedInt32Interval,
    },
    IntervalShiftLeft {
        operand: usize,
        shift: i32,
        defined: usize,
        result: SignedInt32Interval,
    },
    IntervalArithmeticShiftRight {
        operand: usize,
        shift: i32,
        result: SignedInt32Interval,
    },
    IntervalBitwiseAnd {
        operand: usize,
        mask: u32,
        result: SignedInt32Interval,
    },
    /// A C conversion of the operand into a one- or two-byte type, with the
    /// operand's interval inside the destination range.
    IntervalNarrowedCast {
        operand: usize,
        source: crate::kernel::MachineIntegerType,
        destination: crate::kernel::MachineIntegerType,
        result: SignedInt32Interval,
    },
    IntervalCompare {
        left: usize,
        right: usize,
        comparison: SignedInt32Comparison,
        result: ClickProposition,
    },
    AffinePremise {
        source: usize,
        left_evidence: usize,
        right_evidence: usize,
        result: ClickProposition,
    },
    AffineConclusion {
        source: usize,
        evidence: usize,
        result: ClickProposition,
    },
    AffineConclusionWithEvidence {
        source: usize,
        left_evidence: usize,
        right_evidence: usize,
        result: ClickProposition,
    },
}

/// Checked pointer and finite-float arithmetic rules. The premise vector is
/// the exact source premise slice consumed by the certificate; node indices
/// refer only to that vector and the flat node list as documented by the
/// parser/printer.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SpecializedCompositionPlan {
    pub premises: Vec<ClickProposition>,
    pub nodes: Vec<SpecialArithmeticNode>,
    pub conclusion: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpecialArithmeticNode {
    IntegerPolynomialIdentity {
        bounds: Vec<usize>,
        result: ClickProposition,
    },
    IntegerCastIdentity {
        bounds: Vec<usize>,
        result: ClickProposition,
    },
    UnsignedSumBound {
        bounds: Vec<usize>,
        result: ClickProposition,
    },
    PointerTranslation {
        relation: usize,
        bounds: Vec<usize>,
        result: ClickProposition,
    },
    PointerAlignment {
        premise: Option<usize>,
        result: ClickProposition,
    },
    PointerWordEquality {
        relation: usize,
        alignments: Vec<usize>,
        result: ClickProposition,
    },
    PointerWordFromAlignment {
        alignments: Vec<usize>,
        result: ClickProposition,
    },
    FloatBound {
        premise: usize,
        result: ClickProposition,
    },
    FloatReflexive {
        finite: usize,
        result: ClickProposition,
    },
    /// `defined(left + right)` or `defined(left - right)` over `int32`
    /// (`int32_defined`) or `int64` (`int64_defined`), from the operands'
    /// width ranges and the listed constant bounds.
    SignedDefined {
        width: crate::kernel::SignedDefinedWidth,
        bounds: Vec<usize>,
        result: ClickProposition,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofAssertion {
    Fact(ClickProposition),
    Resource(ResourceClause),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TheoremApplication {
    name: String,
    arguments: Vec<ContractExpression>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFunctionApplication {
    name: String,
    arguments: Vec<ContractExpression>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum CodeRegionRef {
    Function,
    Loop(usize),
    /// The `N`th region `step()` crosses: one lowered statement, in
    /// executable preorder. Each call a C statement makes is its own region.
    Region(usize),
    Label(String),
    /// A static local assignment occurrence in the executable layout.
    /// Currently accepted by `step_until`, not state expressions.
    Assignment {
        local: String,
        occurrence: usize,
    },
    /// A statement with an explicit scalar memory load, in executable preorder.
    Read(usize),
    /// A region written as a chain of regions, each inside the one before
    /// it, such as `statement(2).statement(0)` or `statement(3).call(f, 1)`;
    /// it names the atomic regions it resolves to through the function's
    /// source layout.
    Path(Vec<SourcePathStep>),
}

/// One link of a chained region. Each counts from zero within the region
/// before it: the function body, a statement, or a loop's statement.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum SourcePathStep {
    /// The `i`th statement: a block item, or a statement an `if` or loop
    /// controls. The arms of an `if` share one count, in source order.
    Statement(usize),
    /// Loop `i` of the function, as `loop(i)` counts it; a chain's start.
    Loop(usize),
    /// The statement's `j`th atomic region of its own, in executable order;
    /// a chain's end.
    Region(usize),
    /// The statement's `j`th call of `f`, in evaluation order; a chain's end.
    Call(String, usize),
    /// The statement's `j`th call of any callee, including one through a
    /// function pointer, in evaluation order: `call(j)`; a chain's end.
    AnyCall(usize),
    /// A loop's own test, after the calls its condition makes: `test()`; a
    /// chain's end.
    Test,
    /// The statement's `j`th own region that assigns local `x`, in executable
    /// order; a chain's end.
    Assignment(String, usize),
    /// The statement's `j`th own region with an explicit scalar memory load,
    /// in executable order; a chain's end.
    Read(usize),
    /// One completed volatile read within an atomic region; only `.result`.
    ReadEvent(usize),
    /// The statement's `j`th `&&`, `||` or ternary operator whose operands
    /// run as steps, in executable order: `and(j)`, `or(j)` or `ternary(j)`;
    /// a chain's end. Its `.result` is the operator's value.
    Operator(crate::kernel::OperatorKind, usize),
}

impl CodeRegionRef {
    /// The C code region this written region names, through the one binding
    /// of each loop label: the structural clause that declared it. Assignment and
    /// read selectors are resolved by the execution layout.
    pub(in crate::surface) fn resolve(
        &self,
        structural_clauses: &StructuralClauses,
    ) -> Result<CodeRegion, CodeRegionResolutionError> {
        match self {
            CodeRegionRef::Function => Ok(CodeRegion::Function),
            CodeRegionRef::Loop(index) => Ok(CodeRegion::Loop(*index)),
            CodeRegionRef::Region(index) => Ok(CodeRegion::Statement(*index)),
            CodeRegionRef::Label(label) => structural_clauses
                .labelled_region(label)
                .copied()
                .ok_or_else(|| CodeRegionResolutionError::UnknownLabel(label.clone())),
            CodeRegionRef::Path(_) => Err(CodeRegionResolutionError::StatementRegionTarget),
            CodeRegionRef::Assignment { .. } | CodeRegionRef::Read(_) => Err(
                CodeRegionResolutionError::ExecutionTargetOnly("assignment and read regions are"),
            ),
        }
    }
}

/// Why a written code region names no C code region.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum CodeRegionResolutionError {
    /// A region only `step_until` accepts; the text names which.
    ExecutionTargetOnly(&'static str),
    /// No loop on this execution path was given this label.
    UnknownLabel(String),
    /// A statement region, which resolves through the function's source
    /// layout rather than the structural clauses.
    StatementRegionTarget,
}

impl std::fmt::Display for CodeRegionResolutionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExecutionTargetOnly(regions) => {
                write!(formatter, "{regions} supported only by `step_until`")
            }
            Self::UnknownLabel(label) => write!(formatter, "unknown code region label `{label}`"),
            Self::StatementRegionTarget => write!(
                formatter,
                "a `statement(i)` region resolves only through the source layout of a function being executed"
            ),
        }
    }
}

/// The surface program point selected by `at(point, expression)`.
///
/// A code location is a `ProgramPointRef`; a proof mark names the current
/// point on its proof path. Both select a recorded symbolic state. Neither
/// is a memory state or a cell's version point.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ProgramPointSelector {
    ProgramPoint(ProgramPointRef),
    Mark(String),
}

impl From<ProgramPointRef> for ProgramPointSelector {
    fn from(point: ProgramPointRef) -> Self {
        Self::ProgramPoint(point)
    }
}

/// Whether a state can name the contract `result`. `result` is the return
/// value, which exists only once the function returns, so `old(...)` (`None`)
/// and every program point but `function.exit` precede it. A proof mark is
/// placed by the proof itself and may follow the return.
pub(crate) fn program_point_can_name_result(selector: Option<&ProgramPointSelector>) -> bool {
    match selector {
        None => false,
        Some(ProgramPointSelector::Mark(_)) => true,
        Some(ProgramPointSelector::ProgramPoint(point)) => {
            point.region == CodeRegionRef::Function && point.kind == ProgramPointKind::Exit
        }
    }
}

/// Whether `result` occurs in a proposition outside any nested state.
pub(crate) fn proposition_names_result(proposition: &ClickProposition) -> bool {
    let mut names = BTreeSet::new();
    collect_current_proposition_variables(proposition, &mut names);
    names.contains("result")
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ProgramPointRef {
    region: CodeRegionRef,
    kind: ProgramPointKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ProgramPointKind {
    Entry,
    Exit,
    /// A call region's by-value aggregate parameters as the call bound them:
    /// the memory just after each argument was copied into its parameter
    /// object. Only `R.parameter(name)` reads at it.
    Parameters,
}

/// A destination for forward execution. A loop back edge selects the
/// boundary of the current iteration, with an optional check of its loop.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionPoint {
    ProgramPoint(ProgramPointRef),
    BackEdge(Option<usize>),
}

impl ExecutionPoint {
    pub const FUNCTION_EXIT: Self = Self::ProgramPoint(ProgramPointRef {
        region: CodeRegionRef::Function,
        kind: ProgramPointKind::Exit,
    });
}

/// `witness(value, ...)`: instantiate the outermost existential binders
/// with the supplied values, in order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofWitness {
    values: Vec<ContractExpression>,
}

impl ProofWitness {
    pub(crate) fn single(value: ContractExpression) -> Self {
        Self {
            values: vec![value],
        }
    }

    pub(crate) fn new(values: Vec<ContractExpression>) -> Self {
        Self { values }
    }

    pub(crate) fn values(&self) -> impl Iterator<Item = &ContractExpression> {
        self.values.iter()
    }

    /// One single-binder witness per value, in order.
    pub(crate) fn singles(&self) -> impl Iterator<Item = Self> + '_ {
        self.values.iter().cloned().map(Self::single)
    }

    pub(crate) fn is_single(&self) -> bool {
        self.values.len() == 1
    }

    pub(crate) fn value(&self) -> &ContractExpression {
        debug_assert!(
            self.is_single(),
            "a multi-binder witness is applied value by value"
        );
        &self.values[0]
    }

    pub(crate) fn try_map_values<E>(
        &self,
        map: impl FnMut(&ContractExpression) -> Result<ContractExpression, E>,
    ) -> Result<Self, E> {
        Ok(Self {
            values: self.values.iter().map(map).collect::<Result<_, E>>()?,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofLetSatisfy {
    // Range existentials infer a machine-integer type during lowering.
    bindings: Vec<(String, Option<ClickType>)>,
    proposition: ClickProposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofChoice {
    name: String,
    source: ProofFactSource,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofFactSource {
    Requirement(usize),
}

/// A `.click` tactic that may search for a proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SmartTactic {
    /// Omitted proof: run the remaining C, then solve each outstanding goal.
    ImplicitTail,
    Solve,
}

/// The fixed state a proposition is evaluated in: the entry state, the
/// current state, the function's result if it has returned, and the states
/// recorded at named states.
#[derive(Clone, Copy)]
pub(in crate::surface) struct FixedStateFrame<'a> {
    pub(in crate::surface) pre_state: &'a ExecutionState,
    pub(in crate::surface) state: &'a ExecutionState,
    pub(in crate::surface) result: Option<FixedStateResult<'a>>,
    pub(in crate::surface) recorded_states: &'a RecordedStates,
}

impl<'a> FixedStateFrame<'a> {
    pub(in crate::surface) fn new(
        pre_state: &'a ExecutionState,
        state: &'a ExecutionState,
        result: Option<&'a ProgramValue>,
        recorded_states: &'a RecordedStates,
    ) -> Self {
        Self {
            pre_state,
            state,
            result: result.map(FixedStateResult::Native),
            recorded_states,
        }
    }
    pub(in crate::surface) fn with_retained_result(
        mut self,
        result: &'a crate::kernel::StoredExecutionValue,
    ) -> Self {
        self.result = Some(FixedStateResult::Retained(result));
        self
    }

    pub(in crate::surface) fn native_result(self) -> Option<std::borrow::Cow<'a, ProgramValue>> {
        self.result.map(|result| match result {
            FixedStateResult::Native(value) => std::borrow::Cow::Borrowed(value),
            FixedStateResult::Retained(value) => value.native(),
        })
    }
}

/// Borrow the published carrier; only a selected native consumer materializes it.
#[derive(Clone, Copy)]
pub(in crate::surface) enum FixedStateResult<'a> {
    Native(&'a ProgramValue),
    Retained(&'a crate::kernel::StoredExecutionValue),
}

/// A C function's parameters and the argument expressions bound to them,
/// position by position.
#[derive(Clone, Copy, Default)]
pub(crate) struct ParameterBinding<'a> {
    pub(crate) parameters: &'a [crate::languages::interface::ImportedParameter],
    pub(crate) arguments: &'a [ProgramExpression],
    /// Each parameter's position by name, when the caller built one: a
    /// lowering that reads a few parameters then looks up only those
    /// instead of building a map over every parameter.
    pub(crate) index: Option<&'a ParameterIndex>,
    /// Shared copies of these parameters and arguments, when the caller
    /// built them: a diagnostic captured on every refused attempt keeps a
    /// handle to them instead of copying both lists.
    pub(crate) naming: Option<&'a std::sync::Arc<ParameterNaming>>,
}

impl<'a> ParameterBinding<'a> {
    pub(crate) fn new(
        parameters: &'a [crate::languages::interface::ImportedParameter],
        arguments: &'a [ProgramExpression],
    ) -> Self {
        Self {
            parameters,
            arguments,
            index: None,
            naming: None,
        }
    }

    /// This binding with `index`, which must index its parameters.
    pub(crate) fn with_index(self, index: &'a ParameterIndex) -> Self {
        debug_assert_eq!(index.len(), self.parameters.len());
        Self {
            index: Some(index),
            ..self
        }
    }

    /// This binding with `naming`, which must copy its parameters and
    /// arguments.
    pub(crate) fn with_naming(self, naming: &'a std::sync::Arc<ParameterNaming>) -> Self {
        debug_assert_eq!(naming.parameters.len(), self.parameters.len());
        debug_assert_eq!(naming.arguments.len(), self.arguments.len());
        Self {
            naming: Some(naming),
            ..self
        }
    }
}

/// One copy of a proof's parameter declarations and argument expressions,
/// shared by every diagnostic the proof captures.
pub(crate) struct ParameterNaming {
    pub(crate) parameters: std::sync::Arc<[crate::languages::interface::ImportedParameter]>,
    pub(crate) arguments: std::sync::Arc<[ProgramExpression]>,
    pointer_sources: BTreeMap<Address, usize>,
    float_sources: BTreeMap<(ProgramType, Variable), usize>,
}

impl ParameterNaming {
    pub(crate) fn new(
        parameters: &[crate::languages::interface::ImportedParameter],
        arguments: &[ProgramExpression],
    ) -> Self {
        crate::instrumentation::record_deterministic_work(parameters.len() + arguments.len());
        let mut pointer_sources = BTreeMap::new();
        let mut float_sources = BTreeMap::new();
        for (index, argument) in arguments.iter().enumerate() {
            match argument {
                ProgramExpression::Value(ProgramValue::Pointer(pointer)) => {
                    pointer_sources
                        .entry(pointer.address().clone())
                        .or_insert(index);
                }
                ProgramExpression::Value(
                    value @ (ProgramValue::Float32(MachineTerm::Variable(variable))
                    | ProgramValue::Float64(MachineTerm::Variable(variable))),
                ) => {
                    float_sources
                        .entry((value.program_type(), *variable))
                        .or_insert(index);
                }
                _ => {}
            }
        }
        Self {
            parameters: parameters.into(),
            arguments: arguments.into(),
            pointer_sources,
            float_sources,
        }
    }

    pub(crate) fn float_source(
        &self,
        ty: ProgramType,
        variable: Variable,
    ) -> Option<(
        &crate::languages::interface::ImportedParameter,
        &ProgramExpression,
    )> {
        crate::instrumentation::record_deterministic_work(1);
        let index = *self.float_sources.get(&(ty, variable))?;
        Some((self.parameters.get(index)?, self.arguments.get(index)?))
    }

    pub(crate) fn pointer_source(
        &self,
        pointer: &Address,
    ) -> Option<(
        &crate::languages::interface::ImportedParameter,
        &ProgramExpression,
    )> {
        crate::instrumentation::record_deterministic_work(1);
        let index = *self.pointer_sources.get(pointer)?;
        Some((self.parameters.get(index)?, self.arguments.get(index)?))
    }
}

/// A function's parameter positions, built once for its entry.
pub(crate) struct ParameterIndex {
    positions: BTreeMap<String, usize>,
    slice_lengths: BTreeMap<String, usize>,
    len: usize,
}

impl ParameterIndex {
    pub(crate) fn new(parameters: &[crate::languages::interface::ImportedParameter]) -> Self {
        crate::instrumentation::record_deterministic_work(parameters.len());
        let mut slice_lengths = BTreeMap::new();
        let positions = parameters
            .iter()
            .enumerate()
            .map(|(position, parameter)| {
                if let Some(slice) = parameter.binding_name().slice_length_of() {
                    slice_lengths.insert(slice.to_owned(), position);
                }
                (parameter.name().to_owned(), position)
            })
            .collect();
        Self {
            positions,
            slice_lengths,
            len: parameters.len(),
        }
    }

    fn slice_length_position(&self, slice: &str) -> Option<usize> {
        crate::instrumentation::record_deterministic_work(1);
        self.slice_lengths.get(slice).copied()
    }

    pub(crate) fn position(&self, name: &str) -> Option<usize> {
        crate::instrumentation::record_deterministic_work(1);
        self.positions.get(name).copied()
    }

    fn len(&self) -> usize {
        self.len
    }
}

/// The pure definitions a specification is lowered against: its predicates
/// and its Click functions.
#[derive(Clone, Copy)]
struct SpecDefinitions<'a> {
    struct_sizes: Option<&'a BTreeMap<String, u32>>,
    termination_scope: Option<&'a std::sync::Arc<crate::kernel::OrdinaryTerminationScope>>,
    termination_tactics: Option<&'a BTreeSet<String>>,
    predicates: &'a PredicateEnvironment,
    functions: &'a ClickFunctionEnvironment,
}

impl<'a> SpecDefinitions<'a> {
    fn new(predicates: &'a PredicateEnvironment, functions: &'a ClickFunctionEnvironment) -> Self {
        Self {
            predicates,
            functions,
            struct_sizes: None,
            termination_scope: None,
            termination_tactics: None,
        }
    }

    fn with_termination_scope(
        mut self,
        scope: &'a std::sync::Arc<crate::kernel::OrdinaryTerminationScope>,
        tactics: &'a BTreeSet<String>,
    ) -> Self {
        self.termination_scope = Some(scope);
        self.termination_tactics = Some(tactics);
        self
    }

    fn with_struct_sizes(mut self, sizes: &'a BTreeMap<String, u32>) -> Self {
        self.struct_sizes = Some(sizes);
        self
    }

    fn pointer_element_width(&self, pointer: &crate::kernel::Pointer) -> Result<u32, String> {
        if let Some(crate::kernel::effective_type::CAccessClass::Struct(class)) =
            pointer.object_class()
        {
            return self
                .struct_sizes
                .and_then(|sizes| sizes.get(class.tag()))
                .copied()
                .ok_or_else(|| format!("struct `{}` has no known layout", class.tag()));
        }
        pointer
            .program_type()
            .pointee_type()
            .map(ProgramType::byte_width)
            .ok_or_else(|| "expected a sized pointer element".to_string())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PredicateEnvironment {
    program_function_names: std::sync::Arc<BTreeMap<String, String>>,
    definitions: BTreeMap<String, PredicateDefinition>,
    resource_state_dependent: BTreeSet<String>,
    contract_signatures: BTreeMap<String, InterfaceType>,
    contract_definitions: BTreeMap<String, ContractDefinition>,
    contract_value_parameters: Option<std::sync::Arc<ContractValueParameters>>,
}

// Named argument maps print in the same declaration order used by lowering.
type ContractValueParameters = BTreeMap<String, Vec<String>>;

fn contract_value_parameter_names(
    definitions: &[ContractDefinition],
) -> Option<std::sync::Arc<ContractValueParameters>> {
    let names = definitions
        .iter()
        .filter(|definition| !definition.value_parameters().is_empty())
        .map(|definition| {
            (
                definition.name().to_string(),
                definition.value_parameters().to_vec(),
            )
        })
        .collect::<ContractValueParameters>();
    (!names.is_empty()).then(|| std::sync::Arc::new(names))
}

impl PredicateEnvironment {
    fn new(definitions: &[PredicateDefinition]) -> Self {
        let mut resource_state_dependent = BTreeSet::new();
        let mut callers: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for definition in definitions {
            let mut counts = BTreeSet::new();
            validation::collect_resource_count_families(definition.body(), &mut counts);
            let mut predicates = BTreeSet::new();
            validation::collect_called_predicates(definition.body(), &mut predicates);
            if !counts.is_empty() || predicates.contains("held") {
                resource_state_dependent.insert(definition.name().to_string());
            }
            for predicate in predicates {
                callers
                    .entry(predicate)
                    .or_default()
                    .push(definition.name().to_string());
            }
        }
        let mut pending = resource_state_dependent.iter().cloned().collect::<Vec<_>>();
        while let Some(name) = pending.pop() {
            if let Some(dependents) = callers.get(&name) {
                for dependent in dependents {
                    if resource_state_dependent.insert(dependent.clone()) {
                        pending.push(dependent.clone());
                    }
                }
            }
        }
        Self {
            resource_state_dependent,
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
            program_function_names: Default::default(),
            contract_signatures: BTreeMap::new(),
            contract_definitions: BTreeMap::new(),
            contract_value_parameters: None,
        }
    }

    fn with_contracts(
        mut self,
        definitions: &[ContractDefinition],
        names: &std::sync::Arc<BTreeMap<String, String>>,
    ) -> Self {
        self.program_function_names = names.clone();
        self.contract_signatures = definitions
            .iter()
            .map(|definition| {
                (
                    definition.name().to_string(),
                    definition.function_pointer_type(),
                )
            })
            .collect();
        self.contract_definitions = definitions
            .iter()
            .map(|definition| (definition.name().to_string(), definition.clone()))
            .collect();
        self.contract_value_parameters = contract_value_parameter_names(definitions);
        self
    }

    fn get(&self, name: &str) -> Option<&PredicateDefinition> {
        self.definitions.get(name)
    }

    fn function_execution_name<'a>(&'a self, source: &'a str) -> &'a str {
        self.program_function_names
            .get(source)
            .map_or(source, String::as_str)
    }

    fn contract_signature(&self, name: &str) -> Option<InterfaceType> {
        self.contract_signatures.get(name).copied()
    }

    fn contract_definition(&self, name: &str) -> Option<&ContractDefinition> {
        self.contract_definitions.get(name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClickFunctionEnvironment {
    definitions: BTreeMap<String, ClickFunctionDefinition>,
    algebraic_type_definitions: BTreeMap<String, AlgebraicTypeDefinition>,
    /// Functions whose value provably cannot depend on C memory contents.
    /// See [`memory_independent_click_functions`].
    memory_independent: BTreeSet<String>,
    pointer_results: BTreeMap<String, Option<std::sync::Arc<crate::kernel::PurePointerResult>>>,
    pointer_type_error: Option<(String, String)>,
}

impl ClickFunctionEnvironment {
    fn new(definitions: &[ClickFunctionDefinition]) -> Self {
        Self::with_algebraic_types(definitions, &[])
    }

    fn with_algebraic_types(
        definitions: &[ClickFunctionDefinition],
        algebraic_type_definitions: &[AlgebraicTypeDefinition],
    ) -> Self {
        let (pointer_results, pointer_type_error) =
            pointer_result_types::pointer_result_types(definitions, algebraic_type_definitions);
        Self {
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
            algebraic_type_definitions: algebraic_type_definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
            memory_independent: memory_independent_click_functions(definitions),
            pointer_results,
            pointer_type_error,
        }
    }

    fn get(&self, name: &str) -> Option<&ClickFunctionDefinition> {
        self.definitions.get(name)
    }

    /// Whether this function's result is a function of its argument *values*
    /// alone. A pointer argument of such a function carries a memory state
    /// only as dead weight, and that state would otherwise make the same
    /// proposition a different term before and after any C write — which is
    /// what stops a body fact such as `rb_parent_is(left_model, p) == 1` from
    /// being discharged at a `fold` that follows one (gap 42).
    fn is_memory_independent(&self, name: &str) -> bool {
        self.memory_independent
            .contains(generic_instance_source_name(name))
    }
}

/// The declared name a possibly generic instance name came from. Generic
/// instantiation mangles `f` into `f::<T>` without changing the body, so the
/// body-derived classifications are looked up under the source name.
fn generic_instance_source_name(name: &str) -> &str {
    match name.find("::<") {
        Some(index) => &name[..index],
        None => name,
    }
}

/// Click functions whose bodies, transitively, read no C memory.
///
/// The classification is deliberately conservative and syntactic: any field
/// place, index, qualified global, program point selector, resource field or count,
/// predicate call, or C fragment beyond a bare name or literal makes a
/// function memory-dependent, and so does calling a memory-dependent or
/// undeclared function. It is computed once per environment from the declared
/// bodies, never on a verifier hot path.
fn memory_independent_click_functions(definitions: &[ClickFunctionDefinition]) -> BTreeSet<String> {
    let mut callers: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut dependent: Vec<&str> = Vec::new();
    let mut candidates: BTreeSet<String> = BTreeSet::new();
    let declared = definitions
        .iter()
        .map(|definition| definition.name())
        .collect::<BTreeSet<_>>();
    for definition in definitions {
        // A library primitive operation has no body and reads no memory.
        let Some(body) = definition.body() else {
            continue;
        };
        if lambdas::has_function_parameters(definition) {
            dependent.push(definition.name());
            continue;
        }
        let mut callees = Vec::new();
        let reads = contract_expression_reads_memory(body, &mut callees);
        let unknown_callee = callees
            .iter()
            .any(|callee| !declared.contains(generic_instance_source_name(callee)));
        if reads || unknown_callee {
            dependent.push(definition.name());
            continue;
        }
        candidates.insert(definition.name().to_string());
        for callee in &callees {
            let callee = generic_instance_source_name(callee);
            let Some(declared_callee) = declared.get(callee) else {
                continue;
            };
            callers
                .entry(*declared_callee)
                .or_default()
                .push(definition.name());
        }
    }
    // Propagate memory dependence backwards along the call graph, visiting
    // each edge at most once.
    while let Some(name) = dependent.pop() {
        for caller in callers.get(name).map(Vec::as_slice).unwrap_or_default() {
            if candidates.remove(*caller) {
                dependent.push(caller);
            }
        }
    }
    candidates
}

fn contract_expression_reads_memory(
    expression: &ContractExpression,
    callees: &mut Vec<String>,
) -> bool {
    match expression {
        ContractExpression::IntegerContext(value) => {
            contract_expression_reads_memory(value, callees)
        }

        ContractExpression::Proposition(proposition) => {
            click_proposition_reads_memory(proposition, callees)
        }
        ContractExpression::Resource(_) => false,
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => false,
        ContractExpression::Lambda { body, .. } => contract_expression_reads_memory(body, callees),
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            contract_expression_reads_memory(function, callees)
                || arguments
                    .iter()
                    .any(|argument| contract_expression_reads_memory(argument, callees))
        }

        ContractExpression::IntegerLiteral(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::ProgramBinding(_)
        | ContractExpression::ProgramExpression(
            ProgramExpression::Variable(crate::kernel::BindingName::Named(_))
            | ProgramExpression::Value(_),
        ) => false,
        // `address(p)` of a name is that pointer value's integer
        // representation: it reads nothing its operand does not.
        ContractExpression::CUnary {
            operand,
            lowered:
                ProgramExpression::Cast {
                    expression,
                    target_type: ProgramType::UInt64,
                    ..
                },
        } if matches!(
            expression.as_ref(),
            ProgramExpression::Variable(crate::kernel::BindingName::Named(_))
                | ProgramExpression::Value(_)
        ) =>
        {
            contract_expression_reads_memory(operand, callees)
        }
        ContractExpression::ProgramExpression(ProgramExpression::Cast {
            expression,
            target_type: ProgramType::UInt64,
            ..
        }) if matches!(
            expression.as_ref(),
            ProgramExpression::Variable(crate::kernel::BindingName::Named(_))
                | ProgramExpression::Value(_)
        ) =>
        {
            false
        }
        // A memory read, a program point selector, a resource observation, or any
        // C fragment richer than a name is conservatively memory-dependent.
        ContractExpression::QualifiedC { .. }
        | ContractExpression::ResourceField(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard
        | ContractExpression::ProgramExpression(_)
        | ContractExpression::CUnary { .. }
        | ContractExpression::MemoryLoad { .. }
        | ContractExpression::Field { .. }
        | ContractExpression::Index(_, _)
        | ContractExpression::ArrayIndex { .. }
        | ContractExpression::Old(_)
        | ContractExpression::Exact(_)
        | ContractExpression::At { .. } => true,
        ContractExpression::AlgebraicConstructor { arguments, .. }
        | ContractExpression::SequenceLiteral(arguments) => arguments
            .iter()
            .any(|argument| contract_expression_reads_memory(argument, callees)),
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            contract_expression_reads_memory(scrutinee, callees)
                || arms
                    .iter()
                    .any(|arm| contract_expression_reads_memory(&arm.body, callees))
        }
        ContractExpression::SequenceConcat(left, right)
        | ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::RustShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::RustShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            contract_expression_reads_memory(left, callees)
                || contract_expression_reads_memory(right, callees)
        }
        ContractExpression::Negate(inner) | ContractExpression::BitwiseNot(inner) => {
            contract_expression_reads_memory(inner, callees)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            click_proposition_reads_memory(condition, callees)
                || contract_expression_reads_memory(then_branch, callees)
                || contract_expression_reads_memory(else_branch, callees)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contract_expression_reads_memory(start, callees)
                || contract_expression_reads_memory(end, callees)
                || contract_expression_reads_memory(initial, callees)
                || contract_expression_reads_memory(body, callees)
        }
        ContractExpression::Let { value, body, .. } => {
            contract_expression_reads_memory(value, callees)
                || contract_expression_reads_memory(body, callees)
        }
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            contract_expression_reads_memory(receiver, callees)
                || arguments
                    .iter()
                    .any(|argument| contract_expression_reads_memory(argument, callees))
        }
        ContractExpression::Call { name, arguments } => {
            // Numeric conversions and exact integer operations are pure;
            // any memory read remains visible in their explicit arguments.
            if !integer_conversions::is_integer_conversion(name)
                && !integer_truncation::is_integer_truncation(name)
                && name != "to_nat"
            {
                callees.push(name.clone());
            }
            arguments
                .iter()
                .any(|argument| contract_expression_reads_memory(argument, callees))
        }
    }
}

fn click_proposition_reads_memory(
    proposition: &ClickProposition,
    callees: &mut Vec<String>,
) -> bool {
    match proposition {
        ClickProposition::Value(expression) => {
            contract_expression_reads_memory(expression, callees)
        }
        ClickProposition::Comparison { left, right, .. } => {
            contract_expression_reads_memory(left, callees)
                || contract_expression_reads_memory(right, callees)
        }
        ClickProposition::FloatClassification { expression, .. }
        | ClickProposition::Defined { expression }
        | ClickProposition::IsA {
            pointer: expression,
            ..
        } => contract_expression_reads_memory(expression, callees),
        // Resource separation, containment, loadability, states, and
        // predicates all observe the C state.
        ClickProposition::Separate { .. }
        | ClickProposition::ResourceViewable { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::At { .. }
        | ClickProposition::PredicateCall { .. } => true,
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            click_proposition_reads_memory(left, callees)
                || click_proposition_reads_memory(right, callees)
        }
        ClickProposition::Not(inner) => click_proposition_reads_memory(inner, callees),
        ClickProposition::ForAll { body, .. } | ClickProposition::Exists { body, .. } => {
            click_proposition_reads_memory(body, callees)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            contract_expression_reads_memory(start, callees)
                || contract_expression_reads_memory(end, callees)
                || click_proposition_reads_memory(body, callees)
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct ResourceEnvironment {
    definitions: BTreeMap<String, ResourceDefinition>,
    fold_sources: std::sync::Arc<std::sync::OnceLock<BTreeMap<String, ResourceFoldSource>>>,
    /// C layouts are file-local, but resource bodies are shared by every
    /// function in that file. Retain them so struct-pointer arithmetic in a
    /// composite body keeps its physical element width.
    struct_layouts: BTreeMap<String, crate::languages::interface::RecordLayout>,
}

#[derive(Debug)]
struct ResourceFoldSource {
    body: CompositeResourceBody,
    arms: BTreeMap<String, (Vec<(String, ClickType)>, CompositeResourceBody)>,
}

impl PartialEq for ResourceEnvironment {
    fn eq(&self, other: &Self) -> bool {
        self.definitions == other.definitions && self.struct_layouts == other.struct_layouts
    }
}
impl Eq for ResourceEnvironment {}

impl ResourceEnvironment {
    fn new(definitions: &[ResourceDefinition]) -> Self {
        Self::with_struct_layouts(definitions, &BTreeMap::new())
    }

    fn with_struct_layouts(
        definitions: &[ResourceDefinition],
        struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
    ) -> Self {
        Self {
            fold_sources: Default::default(),
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
            struct_layouts: struct_layouts.clone(),
        }
    }

    fn get(&self, name: &str) -> Option<&ResourceDefinition> {
        self.definitions.get(name)
    }

    fn fold_source(&self, name: &str) -> Result<&ResourceFoldSource, ClickError> {
        self.fold_sources
            .get()
            .and_then(|sources| sources.get(name))
            .ok_or_else(|| ClickError::new("resource fold source metadata was not prepared"))
    }

    fn struct_layouts(&self) -> &BTreeMap<String, crate::languages::interface::RecordLayout> {
        &self.struct_layouts
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TheoremEnvironment {
    /// A declaration-order prefix of the standard library's theorems, shared
    /// with every other environment in the process rather than copied: a
    /// verification pays for the library theorems it looks up, not for the
    /// whole library.
    standard_library: &'static [TheoremDefinition],
    /// The name index of the library selection `standard_library` is a
    /// prefix of.
    standard_library_index: &'static BTreeMap<String, usize>,
    standard_library_conclusions: &'static planning::theorems::TheoremConclusionIndex,
    discovery_library_end: usize,
    definition_conclusions: planning::theorems::TheoremConclusionIndex,
    /// Theorems declared after `standard_library`, by identity. The parser
    /// resolved every citation to one: a library theorem's is qualified, so
    /// no file theorem shares it, and a file refuses a duplicate theorem.
    definitions: BTreeMap<String, TheoremDefinition>,
}

impl TheoremEnvironment {
    fn new<'a>(definitions: impl IntoIterator<Item = &'a TheoremDefinition>) -> Self {
        static NO_LIBRARY: BTreeMap<String, usize> = BTreeMap::new();
        static NO_CONCLUSIONS: std::sync::LazyLock<planning::theorems::TheoremConclusionIndex> =
            std::sync::LazyLock::new(Default::default);
        Self::with_library_prefix(&[], &NO_LIBRARY, &NO_CONCLUSIONS, definitions)
    }

    /// The whole Click library followed by `definitions`. Built-in tactics
    /// apply library theorems by name whatever a file imports.
    fn with_standard_library<'a>(
        definitions: impl IntoIterator<Item = &'a TheoremDefinition>,
    ) -> Result<Self, ClickError> {
        let library = validation::full_library()?;
        Ok(Self::with_library_prefix(
            library.theorem_definitions(),
            library.theorem_index(),
            library.theorem_conclusions(),
            definitions,
        ))
    }

    /// Discovery selects laws visible in the source, so expansion can cite
    /// them without adding library imports.
    fn with_discovery_library(mut self, file: &ClickFile) -> Result<Self, ClickError> {
        let library = validation::file_library(file)?;
        self.standard_library_conclusions = library.theorem_conclusions();
        self.discovery_library_end = library.theorem_definitions().partition_point(|theorem| {
            self.standard_library_index
                .get(theorem.name())
                .is_some_and(|ordinal| *ordinal < self.standard_library.len())
        });
        Ok(self)
    }

    /// The theorems of the whole Click library before position `end`,
    /// followed by `definitions`.
    fn with_full_library_prefix<'a>(
        end: usize,
        definitions: impl IntoIterator<Item = &'a TheoremDefinition>,
    ) -> Result<Self, ClickError> {
        let library = validation::full_library()?;
        Ok(Self::with_library_prefix(
            &library.theorem_definitions()[..end],
            library.theorem_index(),
            library.theorem_conclusions(),
            definitions,
        ))
    }

    /// `standard_library` must be a prefix of the library selection that
    /// `standard_library_index` indexes.
    fn with_library_prefix<'a>(
        standard_library: &'static [TheoremDefinition],
        standard_library_index: &'static BTreeMap<String, usize>,
        standard_library_conclusions: &'static planning::theorems::TheoremConclusionIndex,
        definitions: impl IntoIterator<Item = &'a TheoremDefinition>,
    ) -> Self {
        let mut environment = Self {
            standard_library,
            standard_library_index,
            standard_library_conclusions,
            discovery_library_end: standard_library.len(),
            definition_conclusions: Default::default(),
            definitions: BTreeMap::new(),
        };
        for definition in definitions {
            environment.insert(clone_theorem_definition_iteratively(definition));
        }
        environment
    }

    fn get(&self, name: &str) -> Option<&TheoremDefinition> {
        self.definitions.get(name).or_else(|| {
            self.standard_library_index
                .get(name)
                .and_then(|index| self.standard_library.get(*index))
        })
    }

    fn conclusion_candidates<'a>(
        &'a self,
        goal: &ClickProposition,
    ) -> impl Iterator<Item = &'a planning::theorems::TheoremCandidate> {
        self.definition_conclusions
            .candidates(goal, usize::MAX)
            .chain(
                self.standard_library_conclusions
                    .candidates(goal, self.discovery_library_end),
            )
    }

    fn insert(&mut self, definition: TheoremDefinition) {
        self.definition_conclusions
            .insert(&definition, self.definitions.len());
        self.definitions
            .insert(definition.name().to_string(), definition);
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct VerifiedProgramTheorem {
    pub source_path: String,
    /// Fixed-size identity of all selected compiler imports on which this
    /// theorem depends, when verification used the prepared-import route.
    pub import_identity: Option<String>,
    /// Fixed-size identity of the C inputs, Click proof source, target/profile,
    /// and resource semantics under which this theorem was checked. `None`
    /// denotes a theorem assembled by a legacy internal path that has not yet
    /// crossed the shared verification boundary.
    pub artifact_identity: Option<verification::ProofArtifactIdentity>,
    /// The C implementation target this theorem was checked under. Set when
    /// the artifact crosses the shared verification boundary; a legacy
    /// internal path leaves the default target in place.
    pub target: crate::languages::c::target::CTarget,
    /// The CLI proof boundary under which this artifact was produced.
    pub selection: Option<ProofSelection>,
    /// Shared by every theorem one proof issued, like `proof_tactics`: the
    /// block carries the whole grouped proof, and a proof issues a theorem
    /// per path and claim.
    pub function_block: std::sync::Arc<FunctionBlock>,
    pub claim: VerifiedClaim,
    pub proof_kind: ProofKind,
    /// The source proof text, shared by every theorem one proof issued.
    pub proof_tactics: Option<std::sync::Arc<[ProofTactic]>>,
    pub expanded_proof: Option<ProofCertificate>,
    pub expansion_blocker: Option<String>,
    pub specification: FunctionSpecification,
    pub theorem: Theorem,
    pub concrete_loop_execution: bool,
    /// Shared by every theorem one proof issued: a grouped proof issues one
    /// theorem per path and claim over the same checked execution, so the
    /// `Arc` both avoids a per-theorem copy of every path and gives
    /// finalization an exact identity to visit that execution once.
    pub(crate) checked_execution: std::sync::Arc<CheckedFunctionExecution>,
    /// Exact proposition authority issued by the completed kernel proof and
    /// bound to this theorem's function path. Resource and effect claims keep
    /// their dedicated finalization checks instead.
    pub(crate) checked_proposition: Option<CheckedFunctionProposition>,
    pub(crate) frontier_loop_clauses: std::sync::Arc<[StructuralClause]>,
    pub(crate) frontier_loop_rules: std::sync::Arc<[VerifiedLoopRule]>,
    /// The entry the proof that issued this theorem was built from, shared
    /// by every theorem of that proof.
    pub(in crate::surface) entry_context: Option<std::sync::Arc<proof::ProofEntryContext>>,
    /// The checked function's source layout, which spells the certificate's
    /// step results when it is rendered after checking.
    pub(in crate::surface) source_layout: TheoremSourceLayout,
}

/// The source layout a verified theorem's certificate is spelled by. It is
/// presentation, not what the theorem states, so it never makes two
/// theorems unequal.
#[derive(Clone, Default)]
pub(in crate::surface) struct TheoremSourceLayout(
    pub(in crate::surface) Option<lowering::SourceExecutionLayout>,
);

impl PartialEq for TheoremSourceLayout {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for TheoremSourceLayout {}

// Retained executions and proof states share large graphs. Formatting a
// verification result (notably unwrap_err's unexpected-success panic) must
// identify the artifact without recursively dumping those graphs.
impl fmt::Debug for VerifiedProgramTheorem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let claim = match &self.claim {
            VerifiedClaim::Ensure { index, .. } => ("ensures", *index),
            VerifiedClaim::ExceptionalEnsure { index, .. } => ("exceptional ensures", *index),
        };
        f.debug_struct("VerifiedProgramTheorem")
            .field("source_path", &self.source_path)
            .field("function", &self.function_block.signature().name())
            .field("claim", &claim)
            .field("proof_kind", &self.proof_kind)
            .field("target", &self.target)
            .finish_non_exhaustive()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofSelection {
    pub entry_module: Option<String>,
    pub selected_proofs: Vec<String>,
    pub assumed_theorems: Vec<String>,
    pub assumed_functions: Vec<String>,
    /// Explicit runtime specifications on which this conditional artifact depends.
    pub runtime_assumptions: Vec<String>,
    /// Checked origin, canonical types, and specification identity for
    /// the selected modeled pthread projection, when present.
    pub modeled_pthread_binding: Option<crate::languages::c::thread_runtime::ModeledPthreadBinding>,
}

#[derive(Clone, Debug)]
pub struct VerifiedPureTheorem {
    pub theorem_definition: TheoremDefinition,
    pub ensure_index: usize,
    pub ensure_clause: EnsureClause,
    pub proof_kind: ProofKind,
    pub proof: Option<ProofCertificate>,
    contract_value_parameters: Option<std::sync::Arc<ContractValueParameters>>,
    pub requires: Vec<Proposition>,
    pub conclusion: Proposition,
    pub(crate) kernel_authority: Option<KernelVerifiedPureTheorem>,
    /// Retained source-proof evidence. Kernel axioms and execution/refinement
    /// rules retain their authority through their dedicated checker instead.
    pub(crate) checked_completion: Option<TheoremProofCompletion>,
}

#[derive(Clone)]
pub(crate) enum TheoremProofCompletion {
    Proposition(crate::kernel::proof::CheckedProposition),
}

impl std::fmt::Debug for TheoremProofCompletion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Proposition(completion) => f
                .debug_struct("PropositionCompletion")
                .field("closed_without_assumptions", &completion.is_closed())
                .finish(),
        }
    }
}

// Public theorem equality compares the declaration and its checked
// presentation, as before. Opaque retained proof handles are evidence,
// not a new structural equality or cache key for the verifier.
impl PartialEq for VerifiedPureTheorem {
    fn eq(&self, other: &Self) -> bool {
        self.theorem_definition == other.theorem_definition
            && self.ensure_index == other.ensure_index
            && self.ensure_clause == other.ensure_clause
            && self.proof_kind == other.proof_kind
            && self.proof == other.proof
            && self.requires == other.requires
            && self.conclusion == other.conclusion
            && self.kernel_authority == other.kernel_authority
    }
}
impl Eq for VerifiedPureTheorem {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VerifiedClaim {
    Ensure { index: usize, clause: EnsureClause },
    ExceptionalEnsure { index: usize, clause: EnsureClause },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofKind {
    Axiom,
    Pure,
    Solve,
    TacticScript,
    LoopVerification,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ReportDetail {
    /// The prepared program's accessor spellings, retained for lazy reports.
    model_accessors: Option<diagnostics::CapturedModelAccessors>,
    implicit_step: Option<&'static str>,
    missing_tactic_requirement: Option<String>,
    /// Instantiated declared theorem prerequisite, for discovery diagnostics only.
    missing_theorem_requirement: Option<String>,
    /// The Click declaration (a function block, named contract or theorem)
    /// this failure is about, when no C statement has run and no tactic has
    /// been checked: a contract that could not be set up at entry, or an
    /// `executes` theorem refused before its proof.
    declaration: Option<String>,
    /// The written tactic being checked when a failure with no proof-step
    /// site of its own arose: its claim and source occurrence.
    source_tactic: Option<(String, Vec<usize>)>,
    /// The resource fact a refused C operation needed and the state did not
    /// hold. Planning input, like an unresolved requirement: execution search opens the
    /// one folded resource whose body holds it (design/proof-reuse.md R4).
    missing_resource: Option<crate::kernel::ResourceFact>,
    /// The proposition a refused C operation needed, for the report's
    /// `goal:` line when no unresolved requirement carries it. Diagnostics
    /// only: no planner reads it.
    goal: Option<Proposition>,
    /// A written goal whose lowering had not completed when search stopped.
    written_goal: Option<String>,
    /// Whether a write and a live view concretely overlap, when reporting a write prerequisite.
    live_view_write_overlap: Option<bool>,
    /// The labels a refusal that prints its own legend numbered it with, so
    /// a trace of the same failure names the same states and values the
    /// same way instead of numbering them afresh.
    labels: Option<ReportLabels>,
}

impl ReportDetail {
    fn capture() -> Option<std::sync::Arc<Self>> {
        let model_accessors = diagnostics::CapturedModelAccessors::capture();
        let implicit_step = proof_trace::implicit_step();
        (model_accessors.is_some() || implicit_step.is_some()).then(|| {
            std::sync::Arc::new(Self {
                model_accessors,
                implicit_step,
                ..Self::default()
            })
        })
    }
}

/// A refusal's own state and value labels. Diagnostics only: two errors
/// are not told apart by them.
#[derive(Clone)]
struct ReportLabels(std::sync::Arc<proof_diagnostics::render::MemoryStateLabels>);

impl std::fmt::Debug for ReportLabels {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ReportLabels")
    }
}

impl PartialEq for ReportLabels {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Eq for ReportLabels {}

/// What the verifier is working on, for locating a failure that carries no
/// site of its own. This is diagnostics only: nothing reads it to decide a
/// proof.
#[derive(Default)]
struct AmbientProofSource {
    declaration: Option<String>,
    tactic: Option<(String, usize)>,
}

thread_local! {
    static AMBIENT_PROOF_SOURCE: std::cell::RefCell<AmbientProofSource> =
        std::cell::RefCell::new(AmbientProofSource::default());
}

/// Starts verifying the Click declaration `name`; no tactic of it has been
/// addressed yet.
/// The declaration whose proof is being checked, if any.
pub(in crate::surface) fn ambient_declaration() -> Option<String> {
    AMBIENT_PROOF_SOURCE.with(|ambient| ambient.borrow().declaration.clone())
}

pub(crate) fn enter_ambient_declaration(name: &str) {
    proof_diagnostics::render::clear_ambient_naming();
    diagnostics::enter_rust_spelling(None);
    AMBIENT_PROOF_SOURCE.with(|ambient| {
        *ambient.borrow_mut() = AmbientProofSource {
            declaration: Some(name.to_owned()),
            tactic: None,
        };
    });
}

/// Records that `claim_label`'s source tactic `source_index` is being
/// checked.
pub(crate) fn note_ambient_source_tactic(claim_label: &str, source_index: usize) {
    AMBIENT_PROOF_SOURCE.with(|ambient| {
        let mut ambient = ambient.borrow_mut();
        if ambient
            .tactic
            .as_ref()
            .is_none_or(|(claim, index)| claim != claim_label || *index != source_index)
        {
            ambient.tactic = Some((claim_label.to_owned(), source_index));
        }
    });
}

pub(crate) fn clear_ambient_proof_source() {
    proof_diagnostics::render::clear_ambient_naming();
    AMBIENT_PROOF_SOURCE.with(|ambient| *ambient.borrow_mut() = AmbientProofSource::default());
}

#[derive(Debug)]
pub struct ClickError {
    message: String,
    rendered: std::sync::OnceLock<Box<str>>,
    kind: ClickErrorKind,
    failed_tactic: Option<&'static str>,
    proof_refusal: Option<ProofRefusal>,
    verification_stop: Option<instrumentation::VerificationStop>,
    diagnostic: Option<std::sync::Arc<proof_diagnostics::ProofFailureDiagnostic>>,
    search_failures: Option<std::sync::Arc<Vec<proof_diagnostics::ProofSearchFailure>>>,
    unresolved_requirement: Option<std::sync::Arc<UnresolvedRequirement>>,
    /// Report detail few errors carry, shared behind one pointer so the
    /// error stays small enough to return by value.
    report_detail: Option<std::sync::Arc<ReportDetail>>,
    /// The refused statement or condition has several checked successors
    /// that are cases told apart by their path facts. A simple tactic does
    /// not split on them; a planner that can split may take over.
    /// Inside, the source condition a proof-level case split separates
    /// those cases on first, when one has a Click spelling.
    path_case_split: Option<std::sync::Arc<PathCaseSplit>>,
    timing_tactic: Option<Box<TimingTacticContext>>,
}

/// How a proof-level split separates a refusal's path cases.
#[derive(Clone, Debug, Eq, PartialEq)]
enum PathCaseSplit {
    /// No split has a Click spelling.
    Unspelled,
    /// A proof `if` on this source condition, first.
    Condition(ClickProposition),
    /// A proof `match` on an enum value, one arm per variant, as a Rust
    /// `match` of a value whose variant is not yet known needs.
    Match(ProofMatch),
}

/// The cause of a refused input or checked proof operation. `Proof` means
/// evidence was unavailable to this check; it is not a claim that C is unsafe.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClickErrorKind {
    Syntax,
    WorkLimitReached,
    TimedOut,
    Type,
    Proof,
    Unsupported,
    Internal,
}

/// The reason a proof operation was refused, when the verifier can classify it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofRefusal {
    Tactic,
    UnsuccessfulSearch,
    ImplicitStatementSearch,
    IncompleteProof,
    Contract,
}

/// A concrete failure outcome reported by verification.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VerificationOutcome {
    SyntaxError,
    TypeError,
    TacticError,
    UnsuccessfulSearch,
    IncompleteProof,
    ContractError,
    Unsupported,
    InternalError,
    WorkLimitReached,
    TimedOut,
}

impl VerificationOutcome {
    pub const ALL: [Self; 10] = [
        Self::SyntaxError,
        Self::TypeError,
        Self::TacticError,
        Self::UnsuccessfulSearch,
        Self::IncompleteProof,
        Self::ContractError,
        Self::Unsupported,
        Self::InternalError,
        Self::WorkLimitReached,
        Self::TimedOut,
    ];

    pub fn label(self) -> &'static str {
        match self {
            Self::SyntaxError => "syntax error",
            Self::TypeError => "type error",
            Self::TacticError => "tactic error",
            Self::UnsuccessfulSearch => "unsuccessful search",
            Self::IncompleteProof => "incomplete proof",
            Self::ContractError => "contract error",
            Self::Unsupported => "unsupported",
            Self::InternalError => "internal error",
            Self::WorkLimitReached => "work limit reached",
            Self::TimedOut => "timed out",
        }
    }
}

/// A diagnostic classified before terminal rendering starts.
pub struct VerificationDiagnostic<'a> {
    error: &'a ClickError,
    outcome: VerificationOutcome,
    missing_classification: bool,
}

impl<'a> VerificationDiagnostic<'a> {
    pub fn error(&self) -> &'a ClickError {
        self.error
    }

    pub fn outcome(&self) -> VerificationOutcome {
        self.outcome
    }

    pub fn concise_report_parts(&self) -> (String, Vec<String>) {
        self.error
            .render_concise_parts(self.outcome, self.missing_classification)
    }
}

/// The authored requirement and argument bindings behind a prepared theorem premise.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct TheoremRequirementSource {
    index: usize,
    clause: ClickProposition,
    bindings: std::sync::Arc<[(String, ContractExpression)]>,
}

/// A required kernel verification condition that a checked execution step
/// could not discharge through its exact routes.
///
/// This is planning input, not proof evidence.  It stays attached to the
/// ordinary error while that error gains diagnostic context, so a smart
/// caller can construct an explicit proof at the exact refused frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct UnresolvedRequirement {
    pub(in crate::surface) proposition: Proposition,
    pub(in crate::surface) context: Option<String>,
    pub(in crate::surface) introductions: crate::kernel::LoweringIntroductions,
    pub(in crate::surface) call_site: Option<std::sync::Arc<crate::kernel::CallRequirementSource>>,
    /// For the truthiness obligation an `assert` leaves on its false path
    /// (`0 == 1`, which holds only where that path is unreachable), the
    /// asserted condition: what a proof at the step's pre-state shows.
    pub(in crate::surface) assertion_condition: Option<crate::kernel::ProgramExpression>,
    pub(in crate::surface) theorem_source: Option<std::sync::Arc<TheoremRequirementSource>>,
    /// The defined successor of a C operation supplied this safety goal.
    pub(in crate::surface) statement_safety: bool,
    /// The Surface spelling the tactic that owes this requirement gave it
    /// where it created it, such as a `fold` body fact with the resource's
    /// arguments substituted. Proofs state the requirement this way.
    pub(in crate::surface) surface: Option<ClickProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TimingTacticContext {
    source_tactic_path: Option<Vec<usize>>,
    claim_label: String,
    tactic_index: usize,
    tactic_name: String,
    tactic_class: String,
    statement_index: usize,
    source_index: usize,
}

thread_local! {
    static ACTIVE_TIMING_TACTICS: std::cell::RefCell<Vec<TimingTacticContext>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

fn push_timing_tactic(context: TimingTacticContext) {
    ACTIVE_TIMING_TACTICS.with(|active| active.borrow_mut().push(context));
}

fn pop_timing_tactic(context: &TimingTacticContext) {
    ACTIVE_TIMING_TACTICS.with(|active| {
        let mut active = active.borrow_mut();
        if let Some(index) = active.iter().rposition(|candidate| candidate == context) {
            active.remove(index);
        }
    });
}

fn current_timing_tactic() -> Option<TimingTacticContext> {
    ACTIVE_TIMING_TACTICS.with(|active| active.borrow().last().cloned())
}

#[derive(Clone)]
pub struct ProgramVerificationSession {
    c_sources: Vec<(String, String)>,
    click_project: Option<ClickProject>,
    pub(crate) prepared_imports: Option<Vec<crate::languages::c::compiler_import::PreparedCImport>>,
    pub(crate) prepared_program_import: Option<crate::languages::PreparedProgram>,
    baseline_file: ClickFile,
    verified_function_environment: ExecutionEnvironment,
    environment_identity: verification::ProofArtifactIdentity,
    /// The kernel generation `verified_function_environment` was built
    /// under. Its states live in this thread's kernel tables, which the
    /// next fresh verification on the thread replaces.
    kernel_generation: u64,
    /// The kernel tables as they stood once that environment was built. Each
    /// check restores them first, so a check starts from exactly the
    /// environment's own state and leaves nothing behind for the next: a
    /// session's memory is bounded by its largest check, not their sum.
    kernel_state: crate::kernel::VerificationSessionState,
}

impl ClickFile {
    pub fn imports(&self) -> &[ImportDeclaration] {
        &self.imports
    }

    /// The `library/` identities of the Click library modules this file
    /// imports. Every library module is currently loaded implicitly, so an
    /// import only checks that its module exists.
    pub fn library_imports(&self) -> &[String] {
        &self.library_imports
    }

    /// Where the parser read the entry module's declarations and proofs.
    pub(in crate::surface) fn source_spans(&self) -> &std::sync::Arc<parser::SourceSpans> {
        &self.source_spans
    }

    pub(crate) fn entry_module(&self) -> Option<&str> {
        self.entry_module.as_deref()
    }

    pub fn verifying_sources(&self) -> &[String] {
        &self.verifying_sources
    }

    /// The language of this file's `verifying` sources.
    pub fn source_language(&self) -> crate::languages::SourceLanguage {
        crate::languages::SourceLanguage::of_sources(
            self.verifying_sources.iter().map(String::as_str),
        )
    }

    /// The declared C implementation target, if this file selects one.
    pub fn declared_c_target(&self) -> Option<crate::languages::c::target::CTarget> {
        self.c_target
    }

    /// The C implementation target this file's sources are preprocessed and
    /// verified under, defaulting to the supported kernel target.
    pub fn selected_c_target(&self) -> crate::languages::c::target::CTarget {
        self.c_target
            .unwrap_or(crate::languages::c::target::CTarget::SUPPORTED)
    }

    pub fn selected_thread_runtime(&self) -> crate::languages::c::thread_runtime::CThreadRuntime {
        self.thread_runtime
    }

    pub fn algebraic_type_definitions(&self) -> &[AlgebraicTypeDefinition] {
        &self.algebraic_type_definitions
    }

    pub fn predicate_definitions(&self) -> &[PredicateDefinition] {
        &self.predicate_definitions
    }

    pub fn click_function_definitions(&self) -> &[ClickFunctionDefinition] {
        &self.click_function_definitions
    }

    pub fn resource_definitions(&self) -> &[ResourceDefinition] {
        &self.resource_definitions
    }

    pub fn theorem_definitions(&self) -> &[TheoremDefinition] {
        &self.theorem_definitions
    }

    pub fn contract_definitions(&self) -> &[ContractDefinition] {
        &self.contract_definitions
    }

    pub fn function_blocks(&self) -> &[FunctionBlock] {
        &self.function_blocks
    }

    pub fn tactic_definitions(&self) -> &[TacticDefinition] {
        &self.tactic_definitions
    }

    fn declaration_owner(&self, identity: &DeclarationIdentity) -> Option<&str> {
        self.declaration_owners.get(identity).map(String::as_str)
    }

    fn function_is_selected(&self, name: &str) -> bool {
        self.entry_module.as_ref().is_none_or(|entry| {
            self.declaration_owner(&DeclarationIdentity::ProgramFunction(name.to_string()))
                .or_else(|| self.declaration_owner(&DeclarationIdentity::Tactic(name.to_string())))
                == Some(entry.as_str())
        })
    }

    fn theorem_is_selected(&self, name: &str) -> bool {
        match &self.entry_module {
            None => true,
            Some(entry) => {
                self.declaration_owner(&DeclarationIdentity::Theorem(name.to_string()))
                    == Some(entry.as_str())
            }
        }
    }
}

impl ImportDeclaration {}

impl AlgebraicTypeDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn type_parameters(&self) -> &[String] {
        &self.type_parameters
    }

    pub fn variants(&self) -> &[AlgebraicVariantDefinition] {
        &self.variants
    }

    pub fn is_primitive(&self) -> bool {
        self.primitive
    }
}

impl AlgebraicVariantDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fields(&self) -> &[AlgebraicFieldType] {
        &self.fields
    }
}

impl PredicateDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn type_parameters(&self) -> &[String] {
        &self.type_parameters
    }

    pub fn body(&self) -> &ClickProposition {
        &self.body
    }
}

impl ClickFunctionDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn type_parameters(&self) -> &[String] {
        &self.type_parameters
    }

    pub fn return_type(&self) -> &ClickType {
        &self.return_type
    }

    pub fn return_object_class(&self) -> Option<&crate::kernel::effective_type::CAccessClass> {
        self.return_object_class.as_ref()
    }

    pub fn decreases(&self) -> Option<&ContractExpression> {
        self.decreases.as_ref()
    }

    /// The definition, or `None` for a library primitive operation, which
    /// nothing unfolds or evaluates.
    pub fn body(&self) -> Option<&ContractExpression> {
        self.body.as_ref()
    }
}

impl ResourceDefinition {
    /// Whether this is a field-bearing `abstract resource`, which no proof
    /// may fold, unfold, or observe.
    pub fn is_sealed(&self) -> bool {
        self.sealed
    }

    pub fn fields(&self) -> &[ResourceFieldDefinition] {
        self.composite_body
            .as_ref()
            .map_or(&[], |body| &body.fields)
    }

    pub fn field_schema(&self) -> Option<&crate::kernel::ResourceFieldSchema> {
        self.field_schema.as_ref()
    }

    pub fn is_fieldless(&self) -> bool {
        self.fields().is_empty()
    }

    pub fn is_authorized(&self) -> bool {
        self.authorized
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn resource_parameters(&self) -> &[ResourceClause] {
        &self.resource_parameters
    }

    pub fn composite_body(&self) -> Option<&CompositeResourceBody> {
        self.composite_body.as_ref()
    }
}

impl CompositeResourceBody {
    /// The named child slots of this body, its unmatched part and every
    /// match arm, each with the resource it owns, or `None` when two arms
    /// give one slot name different resources. A child may name another
    /// declared resource, so a slot's resource is a property of the
    /// definition, which the parser and declaration expansion both read.
    /// For a body that matches on a field, that field and, for each arm's
    /// variant, the child slots the arm holds with the resource each owns,
    /// the unmatched part's included. A proof `match` on the field selects
    /// one arm, so a slot whose resource differs between arms has one there.
    pub(in crate::surface) fn arm_child_slot_resources(
        &self,
    ) -> Option<(String, BTreeMap<String, BTreeMap<String, String>>)> {
        let matched = self.matched.as_ref()?;
        let named = |body: &CompositeResourceBody| {
            body.contains
                .iter()
                .filter_map(|clause| match clause {
                    ResourceClause::Named { binding, resource } => match resource.as_ref() {
                        ResourceClause::Declared { name, .. } => {
                            Some((binding.name.clone(), name.clone()))
                        }
                        _ => None,
                    },
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let unmatched = named(self);
        let arms = matched
            .arms
            .iter()
            .map(|arm| {
                let mut slots = unmatched.iter().cloned().collect::<BTreeMap<_, _>>();
                slots.extend(named(&arm.body));
                (arm.variant.clone(), slots)
            })
            .collect();
        Some((matched.field.clone(), arms))
    }

    pub(in crate::surface) fn child_slot_resources(&self) -> BTreeMap<String, Option<String>> {
        let mut slots: BTreeMap<String, Option<String>> = BTreeMap::new();
        let bodies = std::iter::once(self).chain(
            self.matched
                .iter()
                .flat_map(|matched| &matched.arms)
                .map(|arm| &arm.body),
        );
        for body in bodies {
            for clause in &body.contains {
                let ResourceClause::Named { binding, resource } = clause else {
                    continue;
                };
                let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                    continue;
                };
                slots
                    .entry(binding.name.clone())
                    .and_modify(|existing| {
                        if existing.as_deref() != Some(name.as_str()) {
                            *existing = None;
                        }
                    })
                    .or_insert_with(|| Some(name.clone()));
            }
        }
        slots
    }

    pub fn condition(&self) -> Option<&ClickProposition> {
        self.condition.as_ref()
    }

    pub fn contains(&self) -> &[ResourceClause] {
        &self.contains
    }

    pub fn facts(&self) -> &[ClickProposition] {
        &self.facts
    }

    pub fn witnesses(&self) -> &[ResourceWitness] {
        &self.witnesses
    }
}

impl TheoremDefinition {
    /// Whether this is a Click library `axiom`, trusted without proof.
    pub fn is_axiom(&self) -> bool {
        self.axiom
    }

    /// Where the parser read this theorem's clauses.
    pub(in crate::surface) fn parsed_body(&self) -> &parser::DeclarationBody {
        &self.body
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn type_parameters(&self) -> &[String] {
        &self.type_parameters
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    pub fn ensures(&self) -> &[EnsureClause] {
        &self.ensures
    }

    /// The label of ensure `index`: `T.name` when the author named it,
    /// otherwise its clause kind and position among the theorem's clauses
    /// of that kind, `T.ensures_0` or `T.owns_0`.
    pub fn ensure_claim_label(&self, index: usize) -> String {
        let id = self
            .ensure_claim_ids
            .get(index)
            .copied()
            .unwrap_or_else(|| fallback_claim_id(&self.ensures, index, |index| index));
        claim_labels::claim_label(
            &self.name,
            self.ensures.get(index).and_then(EnsureClause::name),
            id,
        )
    }

    /// The ensure `label` names, by [`Self::ensure_claim_label`]. A
    /// flattened aggregate clause's members share a label; this is the
    /// first of them. An execution theorem's whole-contract label names
    /// its single postcondition too.
    pub fn ensure_index_by_label(&self, label: &str) -> Option<usize> {
        if self.executes.is_some() && label == claim_labels::contract_claim_label(&self.name) {
            return (!self.ensures.is_empty()).then_some(0);
        }
        label.strip_prefix(self.name.as_str())?.strip_prefix('.')?;
        (0..self.ensures.len()).find(|index| self.ensure_claim_label(*index) == label)
    }
}

/// The claim id of ensure `index` read off the clauses themselves, for a
/// block or theorem built without a source: its kind, and how many earlier
/// written clauses (by `source_clause`) have that kind. An index past the
/// clauses is an `ensures` at that position, as the implicit body-safety
/// claim is.
fn fallback_claim_id(
    ensures: &[EnsureClause],
    index: usize,
    source_clause: impl Fn(usize) -> usize,
) -> claim_labels::ClaimClauseId {
    let Some(clause) = ensures.get(index) else {
        return claim_labels::ClaimClauseId {
            kind: claim_labels::ClaimClauseKind::Ensures,
            index,
        };
    };
    let kind = claim_labels::ClaimClauseKind::of_ensure(clause);
    let source = source_clause(index);
    let mut written = BTreeSet::new();
    for (earlier, ensure) in ensures[..index].iter().enumerate() {
        let earlier = source_clause(earlier);
        if earlier != source && claim_labels::ClaimClauseKind::of_ensure(ensure) == kind {
            written.insert(earlier);
        }
    }
    claim_labels::ClaimClauseId {
        kind,
        index: written.len(),
    }
}

impl TheoremExecution {
    /// The conclusion's `as` map, in the target contract's parameter order.
    pub fn target_instances(&self) -> &[(String, String)] {
        &self.target_instances
    }
}

impl ContractDefinition {
    pub fn proof_parameters(&self) -> Option<&[ResourceClause]> {
        self.proof_parameters.as_deref()
    }
    pub fn name(&self) -> &str {
        self.function_block.signature().name()
    }

    pub fn function_block(&self) -> &FunctionBlock {
        &self.function_block
    }

    /// The value parameters, `let amount: int32;`, in declaration order.
    pub fn value_parameters(&self) -> &[String] {
        &self.value_parameters
    }

    /// The parameters of the function type the contract applies to: the
    /// signature's, without the trailing value parameters.
    pub fn call_parameters(&self) -> &[FunctionParameter] {
        let parameters = self.function_block.signature().parameters();
        &parameters[..parameters.len() - self.value_parameters.len()]
    }

    pub fn function_pointer_type(&self) -> InterfaceType {
        let parameter_types = self
            .call_parameters()
            .iter()
            .map(|parameter| {
                (
                    parameter.interface_type().to_kernel_type(),
                    parameter.pointee_is_constant(),
                )
            })
            .collect::<Vec<_>>();
        InterfaceType::FunctionPointer(
            crate::kernel::ProgramType::qualified_function_pointer_signature(
                self.function_block
                    .signature()
                    .return_type()
                    .to_kernel_type(),
                self.function_block.signature().return_pointee_is_constant(),
                &parameter_types,
            ),
        )
    }
}

impl FunctionBlock {
    /// Whether the block states `allocates(result, n)`.
    pub(in crate::surface) fn allocates_result(&self) -> bool {
        self.allocates_result
    }

    /// Where the parser read this block's clauses.
    pub(in crate::surface) fn parsed_body(&self) -> &parser::DeclarationBody {
        &self.body
    }

    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    /// The number of trailing signature parameters that are contract value
    /// parameters rather than C parameters.
    pub(in crate::surface) fn witness_count(&self) -> usize {
        self.witness_count
    }

    /// Adds a crate trait method's interface to this implementation's
    /// contract: its `ensures`, which the implementation's proof establishes
    /// with its own, each named `interface_ensures_<i>`, and its `requires`
    /// when the implementation writes none. A clause the implementation
    /// already states is not repeated. The interface's clauses are read with
    /// the implementation's names for its parameters.
    pub(in crate::surface) fn inherit_interface(
        &mut self,
        interface: &FunctionBlock,
        source: &str,
    ) -> Result<(), String> {
        let names = |block: &FunctionBlock| {
            block
                .signature
                .parameters()
                .iter()
                .map(|parameter| parameter.name().to_string())
                .collect::<Vec<_>>()
        };
        let (own, theirs) = (names(self), names(interface));
        if own.len() != theirs.len() {
            return Err(format!(
                "an implementation takes the parameters {source} does, ({})",
                theirs.join(", ")
            ));
        }
        let renames = theirs
            .iter()
            .zip(&own)
            .filter(|(from, to)| from != to)
            .map(|(from, to)| {
                (
                    from.clone(),
                    ContractExpression::ProgramExpression(
                        crate::kernel::program_expression::variable(to.clone()),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let renamed;
        let interface = if renames.is_empty() {
            interface
        } else {
            renamed = interface.renamed(&renames).map_err(|message| {
                format!(
                    "{source}'s clauses cannot be read with the implementation's parameter \
                     names: {message}"
                )
            })?;
            &renamed
        };
        if self.requires.is_empty() {
            self.requires = interface.requires.clone();
            self.requirement_source_clauses = interface.requirement_source_clauses.clone();
        }
        let written = self.ensures.len();
        let mut next_source = (0..written)
            .map(|index| self.ensure_source_clause(index) + 1)
            .max()
            .unwrap_or(0);
        for (index, clause) in interface.ensures.iter().enumerate() {
            if self.ensures[..written]
                .iter()
                .any(|own| own.ensure() == clause.ensure() && own.condition() == clause.condition())
            {
                continue;
            }
            if self.ensure_claim_ids.len() == self.ensures.len() {
                self.ensure_claim_ids.push(claim_labels::ClaimClauseId {
                    kind: claim_labels::ClaimClauseKind::Ensures,
                    index: self.ensures.len(),
                });
            }
            if self.ensure_source_clauses.len() == self.ensures.len() {
                self.ensure_source_clauses.push(next_source);
                next_source += 1;
            }
            let mut inherited = clause.clone();
            inherited.name = Some(format!("interface_ensures_{index}"));
            self.ensures.push(inherited);
        }
        Ok(())
    }

    /// This contract, without its proof, as the contract of `name`: a C++
    /// dispatch that stands for this block's virtual method.
    pub(in crate::surface) fn dispatch_alias(&self, name: &str) -> FunctionBlock {
        let mut alias = self.clone();
        alias.signature.name = name.to_string();
        alias.signature.c_source = None;
        alias.external = true;
        alias.grouped_proof = None;
        alias
    }

    /// This generic function's contract as its instance `name`, at the
    /// instance's parameter and result types: the clauses unchanged, since
    /// a clause of a generic contract reads its abstract values only by
    /// `==` and `!=`, which mean the same at every type. The instance is
    /// an external declaration: the generic function is verified once.
    pub(in crate::surface) fn generic_instance_alias(
        &self,
        name: &str,
        parameter_types: &[InterfaceType],
        return_type: InterfaceType,
    ) -> Result<FunctionBlock, String> {
        if parameter_types.len() != self.signature.parameters.len() {
            return Err(format!(
                "the instance `{name}` has {} parameters and its generic function {}",
                parameter_types.len(),
                self.signature.parameters.len()
            ));
        }
        let mut alias = self.dispatch_alias(name);
        for (parameter, interface_type) in
            alias.signature.parameters.iter_mut().zip(parameter_types)
        {
            if matches!(
                parameter.click_type,
                ClickType::Program(InterfaceType::Parameter(_))
            ) {
                parameter.click_type = ClickType::Program(*interface_type);
            }
        }
        if matches!(alias.signature.return_type, InterfaceType::Parameter(_)) {
            alias.signature.return_type = return_type;
        }
        Ok(alias)
    }

    /// This contract's clauses with each parameter in `renames` read as the
    /// expression it maps to.
    fn renamed(&self, renames: &BTreeMap<String, ContractExpression>) -> Result<Self, String> {
        let mut renamed = self.clone();
        renamed.requires = self
            .requires
            .iter()
            .map(|requirement| {
                Ok(match requirement {
                    Requirement::Proposition(proposition) => Requirement::Proposition(
                        lowering::substitute_click_proposition(proposition, renames)?,
                    ),
                    Requirement::Resource(resource) => Requirement::Resource(
                        verification::substitute_resource_clause_for_summary(resource, renames)?,
                    ),
                    Requirement::LoadableSegment { segment } => Requirement::LoadableSegment {
                        segment: verification::substitute_contract_segment(
                            segment,
                            &renames.into(),
                        )?,
                    },
                })
            })
            .collect::<Result<_, String>>()?;
        for clause in &mut renamed.ensures {
            clause.ensure = match &clause.ensure {
                Ensure::Proposition(proposition) => Ensure::Proposition(
                    lowering::substitute_click_proposition(proposition, renames)?,
                ),
                Ensure::Resource(resource) => Ensure::Resource(
                    verification::substitute_resource_clause_for_summary(resource, renames)?,
                ),
            };
            if let Some(condition) = &clause.condition {
                clause.condition =
                    Some(lowering::substitute_click_proposition(condition, renames)?);
            }
        }
        Ok(renamed)
    }

    pub fn parameter_struct_casts(&self) -> &BTreeMap<String, String> {
        &self.parameter_struct_casts
    }

    pub(in crate::surface) fn parameter_field_places(
        &self,
    ) -> &BTreeMap<crate::kernel::BindingName, Vec<FieldPlace>> {
        &self.parameter_field_places
    }

    pub(in crate::surface) fn pointee_field_places(&self) -> &BTreeMap<String, Vec<FieldPlace>> {
        &self.pointee_field_places
    }

    pub fn is_external(&self) -> bool {
        self.external
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    /// The source position of each resource requirement, in order: the
    /// 1-based-ready index of the clause the author wrote among the resource
    /// clauses they wrote, and how many of those there are. A flattened
    /// aggregate's members share one position, so the kernel evaluator and
    /// the surface loadability check name the clause as it was written.
    pub fn resource_requirement_positions(&self) -> Vec<(usize, usize)> {
        source_positions(
            self.requires
                .iter()
                .enumerate()
                .filter(|(_, requirement)| matches!(requirement, Requirement::Resource(_)))
                .map(|(index, _)| self.requirement_source_clauses.get(index).copied()),
        )
    }

    /// The written clause, counted among the function's `ensures`, `owns`
    /// and `produces` clauses, that ensure `index` came from. An aggregate
    /// resource clause is flattened into one ensure per member, so several
    /// ensures share the clause the author wrote and its one proof.
    pub fn ensure_source_clause(&self, index: usize) -> usize {
        self.ensure_source_clauses
            .get(index)
            .copied()
            .unwrap_or(index)
    }

    /// The label of ensure `index`: `f.name` when the author named it,
    /// otherwise the kind of clause it was written as and its position
    /// among the block's clauses of that kind (`f.ensures_0`, `f.owns_0`,
    /// `f.produces_0`). An index past the ensures (the implicit body-safety
    /// claim of a contract without any) is `f.ensures_<index>`.
    pub fn ensure_claim_label(&self, index: usize) -> String {
        let id = self
            .ensure_claim_ids
            .get(index)
            .copied()
            .unwrap_or_else(|| {
                fallback_claim_id(&self.ensures, index, |index| {
                    self.ensure_source_clause(index)
                })
            });
        claim_labels::claim_label(
            self.signature.name(),
            self.ensures.get(index).and_then(EnsureClause::name),
            id,
        )
    }

    /// The label of exceptional ensure `index`: `f.name` or
    /// `f.exceptional_ensures_<index>`.
    pub fn exceptional_ensure_claim_label(&self, index: usize) -> String {
        claim_labels::claim_label(
            self.signature.name(),
            self.exceptional_ensures
                .get(index)
                .and_then(EnsureClause::name),
            claim_labels::ClaimClauseId {
                kind: claim_labels::ClaimClauseKind::ExceptionalEnsures,
                index,
            },
        )
    }

    /// The label of the block's grouped proof, `f.contract`.
    pub fn contract_claim_label(&self) -> String {
        claim_labels::contract_claim_label(self.signature.name())
    }

    /// The label of `claim`.
    pub(in crate::surface) fn claim_label(&self, claim: expansion::ContractProofClaim) -> String {
        match claim {
            expansion::ContractProofClaim::Ensure(index) => self.ensure_claim_label(index),
            expansion::ContractProofClaim::ExceptionalEnsure(index) => {
                self.exceptional_ensure_claim_label(index)
            }
            expansion::ContractProofClaim::Grouped => self.contract_claim_label(),
        }
    }

    /// The claim `label` names, by [`Self::claim_label`]: the grouped proof
    /// when the block has one, then the first ensure or exceptional ensure
    /// with that label. A flattened aggregate clause's members share their
    /// clause's label; this selects the first, whose source proof they share.
    pub(in crate::surface) fn claim_by_label(
        &self,
        label: &str,
    ) -> Option<expansion::ContractProofClaim> {
        // Every label of this block starts with its name and a dot.
        label
            .strip_prefix(self.signature.name())?
            .strip_prefix('.')?;
        if label == self.contract_claim_label() && self.covering_proof().is_some() {
            return Some(expansion::ContractProofClaim::Grouped);
        }
        (0..self.ensures.len())
            .find(|index| self.ensure_claim_label(*index) == label)
            .map(expansion::ContractProofClaim::Ensure)
            .or_else(|| {
                (0..self.exceptional_ensures.len())
                    .find(|index| self.exceptional_ensure_claim_label(*index) == label)
                    .map(expansion::ContractProofClaim::ExceptionalEnsure)
            })
    }

    /// As [`Self::resource_requirement_positions`], for the resource
    /// `ensures` clauses.
    pub fn resource_ensure_positions(&self) -> Vec<(usize, usize)> {
        source_positions(
            self.ensures
                .iter()
                .enumerate()
                .filter(|(_, ensure)| matches!(ensure.ensure(), Ensure::Resource(_)))
                .map(|(index, _)| self.ensure_source_clauses.get(index).copied()),
        )
    }

    pub fn decreases(&self) -> Option<&FunctionDecrease> {
        self.decreases.as_ref()
    }

    pub fn recursion_peers(&self) -> &[String] {
        &self.recursion_peers
    }

    pub fn structural_clauses(&self) -> &StructuralClauses {
        &self.structural_clauses
    }

    pub fn constructs(&self) -> &[ResourceClause] {
        &self.constructs
    }

    pub fn ensures(&self) -> &[EnsureClause] {
        &self.ensures
    }

    pub fn exceptional_ensures(&self) -> &[EnsureClause] {
        &self.exceptional_ensures
    }

    /// Whether this block is a user-defined tactic's contract.
    pub(in crate::surface) fn is_tactic_procedure(&self) -> bool {
        self.tactic_procedure
    }

    /// The written grouped proof after the contract block, if any.
    pub fn grouped_proof(&self) -> Option<&SourceProof> {
        self.grouped_proof.as_deref()
    }

    /// The one proof of every claim without its own `by`: the written
    /// grouped proof, or the implicit tail when two or more claims omit theirs. Each
    /// claim with its own `by` keeps that proof. A single claim without one
    /// keeps its per-claim default, which is the same proof over the same
    /// single execution.
    pub fn covering_proof(&self) -> Option<&SourceProof> {
        static IMPLICIT_SOLVE: SourceProof = SourceProof::Tactic(SmartTactic::ImplicitTail);
        if let Some(proof) = &self.grouped_proof {
            return Some(proof);
        }
        (!self.external && !self.tactic_procedure && self.claims_without_proof() >= 2)
            .then_some(&IMPLICIT_SOLVE)
    }

    /// Whether `claim_proof`, a claim's own `by` clause, leaves that claim to
    /// the covering proof.
    pub fn covers_claim_proof(&self, claim_proof: &SourceProof) -> bool {
        matches!(claim_proof, SourceProof::Default) && self.covering_proof().is_some()
    }

    fn claims_without_proof(&self) -> usize {
        self.ensures
            .iter()
            .chain(&self.exceptional_ensures)
            .filter(|clause| matches!(clause.proof, SourceProof::Default))
            .count()
    }

    fn with_frontier_loop_clause(&self, clause: &StructuralClause, loop_index: usize) -> Self {
        self.with_bound_frontier_loop_clauses(&[clause.bound_to_loop(loop_index)])
    }

    /// Install the current complete clause for each C loop identity. An outer
    /// proof can register nested clauses before execution reaches their own
    /// frontiers; binding them there replaces that earlier view, including its
    /// proof-local scope. Repeated invariant spellings inside a clause remain
    /// separate declarations.
    fn with_bound_frontier_loop_clauses(&self, clauses: &[StructuralClause]) -> Self {
        let mut function = self.clone();
        for clause in clauses {
            function.structural_clauses.bind(clause.clone());
        }
        function
    }

    /// Check this block's structural clauses with `check` against
    /// `loop_count`, skipping those an earlier check of this list already
    /// passed ([`StructuralClauses::validate`]).
    pub(in crate::surface) fn validate_structural_clauses<E>(
        &mut self,
        loop_count: usize,
        check: impl FnMut(&StructuralClause) -> Result<(), E>,
    ) -> Result<(), E> {
        self.structural_clauses.validate(loop_count, check)
    }

    /// This block with every structural clause resolved through its own
    /// scope, for lowering. A block whose clauses carry no scope is borrowed
    /// as it is.
    pub(in crate::surface) fn with_resolved_structural_clauses(
        &self,
    ) -> Result<std::borrow::Cow<'_, Self>, String> {
        if !self.structural_clauses.any_scoped() {
            return Ok(std::borrow::Cow::Borrowed(self));
        }
        let mut function = self.clone();
        function.structural_clauses = self
            .structural_clauses
            .iter()
            .map(StructuralClause::resolved)
            .collect::<Result<Vec<_>, String>>()?
            .into();
        Ok(std::borrow::Cow::Owned(function))
    }
}

impl FunctionSignature {
    fn matches_c_definition(
        &self,
        source_path: &str,
        function: &crate::languages::interface::ImportedFunction,
    ) -> bool {
        let name = if let Some(source) = &self.c_source {
            if source != source_path {
                return false;
            }
            self.name
                .rsplit_once("::")
                .map_or(self.name.as_str(), |(_, name)| name)
        } else {
            &self.name
        };
        name == function.source_name()
    }

    /// The slice parameters of a signature written in Rust syntax; `None`
    /// for the C-shaped spelling.
    pub(crate) fn rust_slice_parameters(&self) -> Option<&[String]> {
        self.rust_spelling.slice_parameters()
    }

    /// The iterator each loop of this Rust function advances, by loop index.
    pub(crate) fn rust_loop_iterators(
        &self,
    ) -> &std::sync::Arc<[Option<crate::languages::interface::RustLoopIterator>]> {
        self.rust_spelling.loop_iterators()
    }

    pub(crate) fn with_rust_loop_iterators(
        mut self,
        iterators: &[Option<crate::languages::interface::RustLoopIterator>],
    ) -> Self {
        self.rust_spelling.1 = std::sync::Arc::from(iterators);
        self
    }

    pub fn returns_reference(&self) -> bool {
        self.return_reference
    }

    pub fn return_pointee_is_constant(&self) -> bool {
        self.return_pointee_constant
    }

    pub fn return_type(&self) -> InterfaceType {
        self.return_type
    }

    pub(crate) fn return_click_type(&self) -> ClickType {
        match &self.return_struct_name {
            Some(struct_name) if self.return_type.is_pointer() => ClickType::CObjectPointer {
                interface_type: self.return_type,
                struct_name: struct_name.clone(),
            },
            _ => ClickType::Program(self.return_type),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn exceptional_type(&self) -> Option<InterfaceType> {
        self.exceptional_type
    }

    /// Whether the signature declares `diverges`.
    pub fn diverges(&self) -> bool {
        self.diverges
    }

    /// Whether a parameter or the result is a value of an abstract type.
    /// Whether the signature mentions an abstract type parameter, `T` or
    /// `Option<T>`. An enum's carrier, `Option<u32>`'s, is concrete.
    pub fn has_abstract_types(&self) -> bool {
        fn abstract_type(name: crate::kernel::TypeParameterName) -> bool {
            let ty = name.algebraic_type();
            ty.rigid || ty.arguments.iter().any(abstract_value_type)
        }
        fn abstract_value_type(ty: &crate::kernel::AlgebraicValueType) -> bool {
            use crate::kernel::AlgebraicValueType as V;
            match ty {
                V::Parameter(_) => true,
                V::Program(crate::kernel::ProgramType::Parameter(name)) => abstract_type(*name),
                V::Algebraic { arguments, .. } => arguments.iter().any(abstract_value_type),
                _ => false,
            }
        }
        let is_abstract =
            |ty: InterfaceType| matches!(ty, InterfaceType::Parameter(name) if abstract_type(name));
        is_abstract(self.return_type)
            || self
                .parameters
                .iter()
                .any(|parameter| is_abstract(parameter.interface_type()))
    }
}

impl FunctionParameter {
    fn rust_slice_length(slice: &str) -> Self {
        let binding = crate::kernel::BindingName::slice_length(slice);
        Self {
            name: binding.source_name().to_owned(),
            slice_length: Some(binding),
            click_type: ClickType::Program(InterfaceType::UInt64(LongRank::Long)),
            struct_name: None,
            function_pointer_signature: None,
            constant: false,
            pointee_constant: false,
            reference: false,
        }
    }

    pub fn binding_name(&self) -> crate::kernel::BindingName {
        if let Some(binding) = &self.slice_length {
            binding.clone()
        } else if self.reference {
            crate::kernel::BindingName::reference_carrier(self.name.as_str())
        } else {
            self.name.clone().into()
        }
    }

    pub fn interface_type(&self) -> InterfaceType {
        match &self.click_type {
            ClickType::Resource => panic!("a Resource parameter has no C type"),
            ClickType::Parameter(_) => {
                panic!("a generic Click parameter has no concrete C type")
            }
            ClickType::Program(interface_type)
            | ClickType::CObjectPointer { interface_type, .. } => *interface_type,
            ClickType::Integer => panic!("a mathematical Integer parameter has no C type"),
            ClickType::Proposition | ClickType::Function { .. } => {
                panic!("a specification function has no C type")
            }
            ClickType::Algebraic(_) => {
                panic!("an algebraic Click parameter has no C type")
            }
        }
    }

    pub fn click_type(&self) -> &ClickType {
        &self.click_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref().or(match &self.click_type {
            ClickType::CObjectPointer { struct_name, .. } => Some(struct_name.as_str()),
            _ => None,
        })
    }

    pub fn function_pointer_signature(
        &self,
    ) -> Option<&crate::languages::interface::CallbackInterface> {
        self.function_pointer_signature.as_ref()
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub fn is_reference(&self) -> bool {
        self.reference
    }
}

impl Requirement {
    fn proposition(&self) -> Option<&ClickProposition> {
        match self {
            Self::Proposition(proposition) => Some(proposition),
            _ => None,
        }
    }

    /// The proposition a pure theorem's `requires` clause states.
    ///
    /// A theorem has no resource context: nothing is lent to it, nothing is
    /// consumed, and applying it separates nothing. What a range clause can
    /// still say there is the one thing a range says without an owner —
    /// that reads of it are defined — so `views v[lo..hi];` in a theorem is a
    /// hypothesis, and it is the same hypothesis `loadable(v[lo..hi])` states.
    /// Both spellings lower through this one normalization, so a theorem
    /// cannot mean two things by the same range, and the bare `loadable`
    /// requirement form works in a theorem for the same reason.
    ///
    /// `owns`, `consumes` and `produces` have no reading here at all, and
    /// stay refused where this returns `None`.
    pub(crate) fn theorem_proposition(&self) -> Option<ClickProposition> {
        match self {
            Self::Proposition(proposition) => {
                Some(clone_click_proposition_iteratively(proposition))
            }
            Self::LoadableSegment { segment } => Some(ClickProposition::Loadable {
                segment: segment.clone(),
            }),
            Self::Resource(resource) => theorem_resource_proposition(resource),
        }
    }
}

/// The readability hypothesis a theorem's resource clause states, if it states
/// one. Only a viewed memory range does: a view grants no write authority and
/// no separation, so the whole of what it claims in a pure scope is that its
/// bytes are loadable. An aggregate `views` clause names several ranges at
/// once and claims that of each of them.
fn theorem_resource_proposition(resource: &ResourceClause) -> Option<ClickProposition> {
    match resource {
        ResourceClause::ViewMemory(segment) => Some(ClickProposition::Loadable {
            segment: segment.clone(),
        }),
        ResourceClause::MemoryAggregate {
            access: ResourceAccessMode::View,
            segments,
        } => segments
            .iter()
            .map(|segment| ClickProposition::Loadable {
                segment: segment.clone(),
            })
            .reduce(|left, right| ClickProposition::And(Box::new(left), Box::new(right))),
        _ => None,
    }
}

fn requirement_contains_resource(requirement: &Requirement) -> bool {
    matches!(requirement, Requirement::Resource(_))
}

fn parameter_is_click_array_ref(parameter: &FunctionParameter) -> bool {
    parameter
        .click_type()
        .interface_type()
        .is_some_and(|interface_type| click_array_element_type(interface_type).is_some())
}

fn click_array_element_type(interface_type: InterfaceType) -> Option<ProgramType> {
    interface_type
        .pointee_type()
        .map(InterfaceType::to_kernel_type)
}

impl EnsureClause {
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// Whether this resource ensure returns a borrowed resource, evaluated at
    /// the function's entry state rather than its exit.
    pub fn borrowed(&self) -> bool {
        self.borrowed
    }

    /// The pre-state guard of a conditional resource ensure, if any.
    pub fn condition(&self) -> Option<&ClickProposition> {
        self.condition.as_ref()
    }

    pub fn ensure(&self) -> &Ensure {
        &self.ensure
    }

    pub fn proof(&self) -> &SourceProof {
        &self.proof
    }
}

impl StructuralClause {
    pub fn region(&self) -> &CodeRegion {
        &self.region
    }

    pub fn label(&self) -> Option<&str> {
        self.label.as_deref()
    }

    pub fn decreases(&self) -> Option<&TerminationMeasure> {
        self.decreases.as_ref()
    }

    /// Whether the loop head declares `diverges`.
    pub fn diverges(&self) -> bool {
        self.diverges
    }

    pub fn items(&self) -> &[StructuralItem] {
        &self.items
    }

    /// The region's declared resource clauses, in source order.
    pub fn resources(&self) -> &[ResourceClause] {
        &self.resources
    }

    pub fn initialize_proof(&self) -> Option<&SourceProof> {
        self.initialize_proof.as_ref()
    }

    pub fn preserve_proof(&self) -> Option<&SourceProof> {
        self.preserve_proof.as_ref()
    }

    pub fn otherwise_proof(&self) -> Option<&SourceProof> {
        self.otherwise_proof.as_ref()
    }

    fn bound_to_loop(&self, loop_index: usize) -> Self {
        let mut bound = self.clone();
        bound.region = CodeRegion::Loop(loop_index);
        bound
    }

    /// This clause tagged with the proof locals it was written under.
    pub(in crate::surface) fn with_scope(
        &self,
        scope: impl Into<BinderMap<ContractExpression>>,
    ) -> Self {
        let mut clause = self.clone();
        clause.scope = scope.into();
        clause
    }

    /// This clause with its own scope resolved into its written terms, for
    /// lowering. The result carries no scope.
    pub(in crate::surface) fn resolved(&self) -> Result<Self, String> {
        if self.scope.is_empty() {
            return Ok(self.clone());
        }
        let mut clause = self.with_substituted_bindings(&self.scope)?;
        clause.scope = BinderMap::new();
        Ok(clause)
    }

    /// This clause with the proof locals it names resolved: invariants,
    /// declared-resource arguments, and the `decreases` measure may spell a
    /// proof `match` arm's bindings or a `let { ... } = unfold(...)` name, which are in
    /// scope for a loop written inside that arm exactly as for a `have` goal
    /// there. SymbolicMemory segments are left as written; they name C places.
    pub(in crate::surface) fn with_substituted_bindings(
        &self,
        substitutions: &BinderMap<ContractExpression>,
    ) -> Result<Self, String> {
        let mut clause = self.clone();
        clause.items = self
            .items
            .iter()
            .map(|item| {
                let claim = crate::surface::lowering::substitute_click_proposition(
                    &item.claim,
                    substitutions,
                )?;
                Ok(StructuralItem {
                    claim,
                    name: item.name.clone(),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        clause.resources = self
            .resources
            .iter()
            .map(|resource| substitute_resource_clause_bindings(resource, substitutions))
            .collect::<Result<Vec<_>, String>>()?;
        clause.decreases = match &self.decreases {
            Some(measure) => {
                let mut components = Vec::with_capacity(measure.components.len());
                let mut written = Vec::with_capacity(measure.components.len());
                for (index, component) in measure.components.iter().enumerate() {
                    components.push(crate::surface::lowering::substitute_contract_expression(
                        component,
                        substitutions,
                    )?);
                    // Only a component that names a proof local changes
                    // meaning; substitution may otherwise re-spell a C
                    // fragment without changing what it reads.
                    let names_scope =
                        crate::surface::lowering::contract_expression_referenced_names(component)
                            .iter()
                            .any(|name| substitutions.contains_key(name));
                    written.push(
                        measure
                            .written
                            .as_ref()
                            .and_then(|previous| previous[index].clone())
                            .or_else(|| names_scope.then(|| component.clone())),
                    );
                }
                let written = written.iter().any(Option::is_some).then_some(written);
                Some(TerminationMeasure {
                    components,
                    written,
                })
            }
            None => None,
        };
        Ok(clause)
    }
}

/// Resolves proof-local names in the argument positions of a resource
/// clause. Only declared-resource arguments and quantities are written
/// terms; memory segments name C places and are left as written.
fn substitute_resource_clause_bindings(
    resource: &ResourceClause,
    substitutions: &BinderMap<ContractExpression>,
) -> Result<ResourceClause, String> {
    Ok(match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => ResourceClause::Conditional {
            condition: crate::surface::lowering::substitute_click_proposition(
                condition,
                substitutions,
            )?,
            resource: Box::new(substitute_resource_clause_bindings(
                resource,
                substitutions,
            )?),
        },
        ResourceClause::Named { binding, resource } => ResourceClause::Named {
            binding: binding.clone(),
            resource: Box::new(substitute_resource_clause_bindings(
                resource,
                substitutions,
            )?),
        },
        ResourceClause::Quantified { quantity, resource } => ResourceClause::Quantified {
            quantity: crate::surface::lowering::substitute_contract_expression(
                quantity,
                substitutions,
            )?,
            resource: Box::new(substitute_resource_clause_bindings(
                resource,
                substitutions,
            )?),
        },
        ResourceClause::Declared {
            type_schema,
            resource_type_arguments,
            resource_arguments,
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => ResourceClause::Declared {
            type_schema: type_schema.clone(),
            resource_type_arguments: resource_type_arguments
                .iter()
                .map(|resource| substitute_resource_clause_bindings(resource, substitutions))
                .collect::<Result<_, _>>()?,
            resource_arguments: resource_arguments.clone(),
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    crate::surface::lowering::substitute_contract_expression(
                        argument,
                        substitutions,
                    )
                })
                .collect::<Result<Vec<_>, String>>()?,
            parameter_types: parameter_types.clone(),
        },
        ResourceClause::ViewMemory(_)
        | ResourceClause::OwnMemory(_)
        | ResourceClause::MemoryAggregate { .. } => resource.clone(),
        ResourceClause::Iterated(clause) => ResourceClause::Iterated(Box::new(
            crate::surface::lowering::substitute_iterated_clause(
                clause,
                &crate::surface::lowering::ContractSubstitutions::from(substitutions),
            )?,
        )),
    })
}

impl StructuralItem {
    /// How a diagnostic names this invariant: by its label when it has one,
    /// by its position in the loop header otherwise.
    pub(crate) fn title(&self, index: usize) -> String {
        match &self.name {
            Some(name) => format!("invariant `{name}`"),
            None => format!("invariant {index}"),
        }
    }

    pub fn proposition(&self) -> &ClickProposition {
        &self.claim
    }
}

impl SourceProof {
    pub fn uses_implicit_tail(&self) -> bool {
        matches!(
            self,
            Self::Default | Self::Tactic(SmartTactic::ImplicitTail)
        )
    }

    pub fn tactics(&self) -> Option<&[ProofTactic]> {
        match self {
            Self::Default => None,
            Self::Tactic(_) => None,
            Self::Script(tactics) => Some(tactics),
        }
    }

    pub(crate) fn collect_termination_loop_clauses<'a>(
        &'a self,
        clauses: &mut Vec<&'a StructuralClause>,
    ) {
        let Self::Script(tactics) = self else {
            return;
        };
        for tactic in tactics {
            tactic.collect_termination_loop_clauses(clauses);
        }
    }
}

impl ProofTactic {
    pub(crate) fn collect_termination_loop_clauses<'a>(
        &'a self,
        clauses: &mut Vec<&'a StructuralClause>,
    ) {
        if let Self::Loop(clause) = self {
            clauses.push(clause);
        }
        for child in self.children() {
            let (TacticChild::Continuing(proof) | TacticChild::Obligation(proof)) = child;
            for tactic in proof.tactics().unwrap_or_default() {
                tactic.collect_termination_loop_clauses(clauses);
            }
        }
    }
}

impl VerifiedProgramTheorem {
    /// The concrete C implementation assumptions used by this verifier.
    /// Results are not claims of portability to other target profiles.
    pub fn target(&self) -> crate::languages::c::target::CTarget {
        self.target
    }

    pub fn proof_kind(&self) -> ProofKind {
        self.proof_kind
    }

    pub fn proof_tactics(&self) -> Option<&[ProofTactic]> {
        self.proof_tactics.as_deref()
    }

    pub fn expanded_proof_tactics(&self) -> Option<Vec<ProofTactic>> {
        self.expanded_proof
            .as_ref()
            .map(ProofCertificate::to_proof_tactics)
    }

    pub fn expansion_blocker(&self) -> Option<&str> {
        self.expansion_blocker.as_deref()
    }

    pub fn expanded_proof_certificate(&self) -> Result<ProofCertificate, ClickError> {
        self.expanded_proof.clone().ok_or_else(|| {
            ClickError::new(format!(
                "proof expansion is unavailable for `{}`: {}",
                self.function_block.signature().name(),
                self.expansion_blocker
                    .as_deref()
                    .unwrap_or("verification did not record a surface expansion")
            ))
        })
    }

    /// Spells this theorem's step results by its function's source layout
    /// while alive, as checking did.
    pub(in crate::surface) fn step_result_spelling_scope(
        &self,
    ) -> Option<diagnostics::StepResultSpellingScope> {
        self.source_layout
            .0
            .as_ref()
            .map(diagnostics::StepResultSpellingScope::enter)
    }

    pub fn expanded_proof_source(&self) -> Result<String, ClickError> {
        let _contract_value_parameters = self.contract_value_parameter_scope();
        let _spelling = self.step_result_spelling_scope();
        let _reference_result_source = diagnostics::ReferenceResultSourceScope::enter(
            self.function_block.signature().returns_reference(),
        );
        let _reference_carriers = diagnostics::ParameterPlaceScope::enter(&self.function_block);
        expansion::require_surface_expansion(format_proof_certificate(
            &self.expanded_proof_certificate()?,
        ))
    }

    fn contract_value_parameter_scope(&self) -> Option<printing::ContractValueParameterScope> {
        self.entry_context
            .as_ref()?
            .contract_value_parameters
            .as_ref()
            .map(printing::ContractValueParameterScope::enter)
    }

    pub fn ensure_clause(&self) -> Option<&EnsureClause> {
        match &self.claim {
            VerifiedClaim::Ensure { clause, .. }
            | VerifiedClaim::ExceptionalEnsure { clause, .. } => Some(clause),
        }
    }
}

impl VerifiedPureTheorem {
    pub fn proof_tactics(&self) -> Option<Vec<ProofTactic>> {
        self.proof_certificate()
            .ok()
            .map(|proof| proof.to_proof_tactics())
    }

    pub fn proof_certificate(&self) -> Result<ProofCertificate, ClickError> {
        if let Some(TheoremProofCompletion::Proposition(completion)) = &self.checked_completion
            && completion.proposition() != &self.conclusion
        {
            return Err(ClickError::new(
                "theorem presentation does not match its retained completion",
            ));
        }
        self.proof.clone().ok_or_else(|| {
            ClickError::new(format!(
                "pure theorem `{}` ensure {} has no surface certificate",
                self.theorem_definition.name(),
                self.ensure_index
            ))
        })
    }

    pub fn expanded_proof_source(&self) -> Result<String, ClickError> {
        let _contract_value_parameters = self
            .contract_value_parameters
            .as_ref()
            .map(printing::ContractValueParameterScope::enter);
        expansion::require_surface_expansion(format_proof_certificate(&self.proof_certificate()?))
    }
}

/// The reason with its proof context taken out, and the context lines the
/// command line shows.
///
/// A refusal's whole-context `proof context:` section is dropped with
/// everything after it, as it always was: it lists the entire ambient context
/// in kernel spellings. An unclosed goal's section
/// ([`diagnostics::GOAL_PROOF_CONTEXT_HEADER`]) lists only the path's case
/// and the facts bearing on the goal, so its non-empty lists are shown. What follows the lists is
/// the enclosing failure's own premise and search report, which the full
/// report and `--trace-proof` carry; it is dropped here as before.
fn split_proof_context(reason: &str) -> (&str, Vec<&str>) {
    let whole = reason.find("\nproof context:");
    let goal_header = format!("\n{}", diagnostics::GOAL_PROOF_CONTEXT_HEADER);
    let goal = reason.find(&goal_header);
    match (whole, goal) {
        (Some(whole), goal) if goal.is_none_or(|goal| whole < goal) => {
            (&reason[..whole], Vec::new())
        }
        (_, Some(goal)) => {
            let lists = reason[goal + goal_header.len()..]
                .lines()
                .map(str::trim)
                .skip_while(|line| line.is_empty())
                .take_while(|line| {
                    line.starts_with("case: ")
                        || line.starts_with("pure facts: ")
                        || line.starts_with("resource facts: ")
                })
                .filter(|line| !line.ends_with(": []"))
                .collect();
            (&reason[..goal], lists)
        }
        _ => (reason, Vec::new()),
    }
}

/// The lines of a concise report's reason, each with whether it is nested
/// under the line before it. A `label: detail` line prints its label and its
/// detail on two lines, as the headline's `context: detail` chain does. Two
/// kinds of line are already laid out and stay whole: an entry the reason
/// indents under a list heading (a cell walk's `address: ...; width: ...`
/// fields), and a legend definition (`state#3 = loop effect: may write
/// ...`), whose colon belongs to the definition. Splitting those at every
/// colon scattered one entry over several lines.
fn concise_reason_lines(reason: &str) -> Vec<(bool, &str)> {
    let mut lines = reason.lines();
    let mut result = Vec::new();
    let segments = |line| {
        concise_error_segments(line)
            .into_iter()
            .map(|segment| (false, segment))
            .collect::<Vec<_>>()
    };
    if let Some(headline) = lines.next() {
        result.extend(segments(headline));
    }
    for line in lines {
        let nested = line.starts_with("   ");
        let trimmed = line.trim();
        let definition = trimmed
            .find(" = ")
            .is_some_and(|equals| trimmed.find(": ").is_none_or(|colon| equals < colon));
        if nested || definition {
            result.push((nested, trimmed));
        } else {
            result.extend(segments(trimmed));
        }
    }
    result.retain(|(_, line)| !line.is_empty());
    result
}

/// Split only diagnostic context separators, not colons in Click binders,
/// quoted source, or nested expressions.
fn concise_error_segments(reason: &str) -> Vec<&str> {
    let mut segments = Vec::new();
    let mut start = 0;
    let mut depths = [0_usize; 3];
    let mut quote = None;
    let mut escaped = false;
    for (index, character) in reason.char_indices() {
        if let Some(delimiter) = quote {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == delimiter {
                quote = None;
            }
            continue;
        }
        match character {
            '`' | '"' => quote = Some(character),
            '\'' if !reason[..index]
                .chars()
                .next_back()
                .is_some_and(char::is_alphanumeric) =>
            {
                quote = Some(character);
            }
            '(' => depths[0] += 1,
            ')' => depths[0] = depths[0].saturating_sub(1),
            '[' => depths[1] += 1,
            ']' => depths[1] = depths[1].saturating_sub(1),
            '{' => depths[2] += 1,
            '}' => depths[2] = depths[2].saturating_sub(1),
            ':' if depths == [0; 3] && reason[index + 1..].starts_with(' ') => {
                segments.push(reason[start..index].trim());
                start = index + 2;
            }
            _ => {}
        }
    }
    segments.push(reason[start..].trim());
    segments
}

impl std::fmt::Display for ClickError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}

impl ClickError {
    fn reported_kind(message: &str) -> ClickErrorKind {
        // A few kernel checker interfaces still return strings. They already
        // mark their own invariant failures explicitly; retain that signal
        // until those interfaces return a typed internal error.
        if message.starts_with("internal error") || message.contains(": internal error") {
            ClickErrorKind::Internal
        } else {
            ClickErrorKind::Proof
        }
    }

    /// A summary is one error's own statement. A rendered diagnostic (the
    /// stage, location, premises and search candidates `message()` appends)
    /// is not part of one: an error built from another error's rendered text
    /// would report that whole block as its summary. Wrap an error with
    /// `with_context`, or quote its `raw_summary()`, instead. A summary that
    /// arrives with a rendered block anyway keeps only the text before it.
    fn summary_without_rendered_diagnostic(mut summary: String) -> String {
        const RENDERED_SECTIONS: [&str; 2] = ["\n  stage: ", "\n  search candidates:"];
        let rendered = RENDERED_SECTIONS
            .iter()
            .filter_map(|section| summary.find(section))
            .min();
        debug_assert!(
            rendered.is_none(),
            "an error summary contains another error's rendered diagnostic: {summary}"
        );
        if let Some(rendered) = rendered {
            summary.truncate(rendered);
        }
        summary
    }

    fn new(message: impl Into<String>) -> Self {
        let message = Self::summary_without_rendered_diagnostic(message.into());
        let stop = instrumentation::exceeded_verification_stop();
        let message = match &stop {
            // Deliberate limit diagnostics already include the active context
            // and often add useful target/premise detail. Preserve those;
            // replace only an unrelated semantic error constructed from a
            // conservative false/none after the limit fired.
            Some((_, context)) if !message.contains(context) => {
                format!("verification budget exhausted inside {context}")
            }
            _ => message,
        };
        let kind = Self::reported_kind(&message);
        Self {
            message: diagnostics::bound_error_message(message),
            rendered: std::sync::OnceLock::new(),
            kind,
            failed_tactic: None,
            proof_refusal: None,
            verification_stop: stop.map(|(kind, _)| kind),
            diagnostic: None,
            search_failures: None,
            unresolved_requirement: None,
            report_detail: ReportDetail::capture(),
            path_case_split: None,
            timing_tactic: current_timing_tactic().map(Box::new),
        }
    }

    pub(crate) fn with_diagnostic(
        summary: impl Into<String>,
        mut diagnostic: proof_diagnostics::ProofFailureDiagnostic,
    ) -> Self {
        let summary = Self::summary_without_rendered_diagnostic(summary.into());
        diagnostic.reason = Self::summary_without_rendered_diagnostic(diagnostic.reason);
        let stop = instrumentation::exceeded_verification_stop();
        let summary = match &stop {
            Some((_, context)) if !summary.contains(context) => {
                format!("verification budget exhausted inside {context}")
            }
            _ => summary,
        };
        let kind = Self::reported_kind(&summary);
        Self {
            message: diagnostics::bound_error_message(summary),
            rendered: std::sync::OnceLock::new(),
            kind,
            failed_tactic: None,
            proof_refusal: None,
            verification_stop: stop.map(|(kind, _)| kind),
            diagnostic: Some(std::sync::Arc::new(diagnostic)),
            search_failures: None,
            unresolved_requirement: None,
            report_detail: ReportDetail::capture(),
            path_case_split: None,
            timing_tactic: current_timing_tactic().map(Box::new),
        }
    }

    pub(crate) fn with_diagnostic_if_missing(
        mut self,
        diagnostic: proof_diagnostics::ProofFailureDiagnostic,
    ) -> Self {
        if self.diagnostic.is_none() {
            self.diagnostic = Some(std::sync::Arc::new(diagnostic));
            self.rendered = std::sync::OnceLock::new();
        }
        self
    }

    pub fn message(&self) -> &str {
        if let Some(diagnostic) = &self.diagnostic {
            self.rendered.get_or_init(|| {
                let _accessors = self.report_model_accessor_scope();
                bound_diagnostic_message(proof_diagnostics::render_terminal_message(
                    &self.message,
                    diagnostic,
                    self.search_failures
                        .as_deref()
                        .map_or(&[][..], Vec::as_slice),
                ))
                .into_boxed_str()
            })
        } else if let Some(failures) = &self.search_failures {
            self.rendered.get_or_init(|| {
                let _accessors = self.report_model_accessor_scope();
                bound_diagnostic_message(proof_diagnostics::render_search_failures(
                    &self.message,
                    failures,
                ))
                .into_boxed_str()
            })
        } else {
            &self.message
        }
    }

    /// Terminal-facing classification and the checked simple tactic, when one
    /// was attempted. `message()` stays the stable cause text used by tools
    /// that compare or aggregate diagnostics.
    pub fn report(&self) -> String {
        let _accessors = self.report_model_accessor_scope();
        // A requested proof trace keeps its typed notation throughout.
        let typed_trace = self
            .diagnostic
            .as_ref()
            .is_some_and(|diagnostic| proof_trace::enabled_for(&diagnostic.claim_label))
            .then(proof_diagnostics::render::TypedNotationScope::enter);
        let mut memory_state_labels = proof_diagnostics::render::MemoryStateLabels::ambient();
        // The prerequisite and the rest of this report share the captured
        // proof's names, in ordinary reports as well as typed traces. A fresh
        // renderer here loses match binders even though the diagnostic state
        // still retains their exact values.
        let rendered_message = self.diagnostic.as_ref().map(|diagnostic| {
            proof_diagnostics::render_terminal_message_labeled(
                &self.message,
                diagnostic,
                self.search_failures
                    .as_deref()
                    .map_or(&[][..], Vec::as_slice),
                &mut memory_state_labels,
            )
        });
        let message = rendered_message
            .as_deref()
            .unwrap_or_else(|| self.message());
        let (summary, context) = message.split_once('\n').unwrap_or((message, ""));
        let mut report = format!("{summary}\n  error kind: {}", self.report_label());
        if let Some(tactic) = self.failed_tactic {
            report.push_str("\n  tactic: ");
            report.push_str(tactic);
        }
        if let Some(requirement) = &self.unresolved_requirement {
            report.push_str("\n  goal: ");
            report.push_str(
                &self.render_requirement_goal(&requirement.proposition, &mut memory_state_labels),
            );
            if let Some(context) = &requirement.context {
                report.push_str("\n  check: ");
                report.push_str(context);
            }
        }
        if !context.is_empty() {
            report.push('\n');
            report.push_str(context);
        }
        if matches!(
            self.kind,
            ClickErrorKind::Proof | ClickErrorKind::Unsupported
        ) && let Some(trace) = self.diagnostic.as_ref().and_then(|diagnostic| {
            diagnostic.state.as_ref()?.proof_trace(
                &diagnostic.claim_label,
                &mut memory_state_labels,
                &|_| None,
                &|_, _| None,
                &|_, _| false,
                None,
                diagnostic.failing_path,
            )
        }) {
            report.push('\n');
            report.push_str(&trace);
        }
        if typed_trace.is_some() {
            report
        } else {
            bound_diagnostic_message(report)
        }
    }

    /// The failure and its supporting context for an ordinary CLI report.
    /// Keeping these separate lets the CLI put source excerpts and trace
    /// instructions in their own readable sections.
    pub fn concise_report_parts(&self) -> (String, Vec<String>) {
        self.verification_diagnostic().concise_report_parts()
    }

    fn render_concise_parts(
        &self,
        outcome: VerificationOutcome,
        missing_classification: bool,
    ) -> (String, Vec<String>) {
        let _accessors = self.report_model_accessor_scope();
        let reason = if self.verification_stopped() {
            self.message.as_str()
        } else {
            self.diagnostic
                .as_ref()
                .map_or(self.message.as_str(), |diagnostic| {
                    diagnostic.reason.as_str()
                })
        };
        let (reason, proof_context) = split_proof_context(reason);
        let requirement_reason = self
            .missing_tactic_requirement()
            .filter(|_| !self.verification_stopped())
            .map(|required| format!("requirement `{required}` not satisfied"));
        let reason = requirement_reason.as_deref().unwrap_or(reason);
        let (mut report, reason, _certification_obligation) = if self.kind == ClickErrorKind::Proof
            && let Some(rest) = reason.strip_prefix("could not certify contract for `")
            && let Some((function, detail)) = rest.split_once("`: ")
        {
            let obligation = detail
                .strip_prefix(
                    "exact symbolic execution did not establish every contract claim; execution path ",
                )
                .and_then(|rest| {
                    rest.split_once(
                        " is invalid: the execution path has an unproved verification condition: ",
                    )
                })
                .and_then(|(index, obligation)| {
                    (!index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit()))
                        .then_some(obligation)
                });
            (
                format!(
                    "{} in `{function}` during contract certification:",
                    outcome.label()
                ),
                obligation.unwrap_or(detail),
                obligation.is_some(),
            )
        } else if (reason.starts_with("could not prove ")
            || reason.starts_with("Click cannot yet verify "))
            && let Some(function) = self
                .proof_claim_label()
                .and_then(|claim| claim.split_once('.'))
                .map(|(function, _)| function)
        {
            (
                format!("{} in `{function}`:", outcome.label()),
                reason,
                false,
            )
        } else {
            (format!("{}:", outcome.label()), reason, false)
        };
        if missing_classification {
            report.push_str("\n  Click did not classify this verifier failure.");
        }
        for (nested, line) in concise_reason_lines(reason) {
            report.push_str(if nested { "\n    " } else { "\n  " });
            report.push_str(line);
        }
        // The facts the refusal was checked against, as the library message
        // lists them: each list is already bounded by the diagnostic item
        // limit, and an empty list says nothing the reader can use.
        if !proof_context.is_empty() {
            report.push_str("\n  proof context");
            for line in proof_context {
                report.push_str("\n  ");
                report.push_str(line);
            }
        }
        let mut context = Vec::new();
        if let Some(step) = self.implicit_tactic_step() {
            context.push(format!("refused by: implicit step ({step})"));
        }
        if let Some(tactic) = self.failed_tactic {
            context.push(format!("tactic: {tactic}"));
        }
        if let Some(required) = self.missing_tactic_requirement() {
            context.push(format!("requires: {required}"));
        }
        // These are failures recorded at the actual view-certificate stages,
        // rather than inferred semantic explanations. Keep their bounded
        // reasons visible in ordinary CLI errors as well as proof traces.
        if let Some(failures) = &self.search_failures {
            for failure in failures
                .iter()
                .filter(|failure| failure.strategy.starts_with("solve view "))
                .take(8)
            {
                context.push(format!(
                    "construction failure: {}: {}",
                    failure.strategy, failure.reason
                ));
            }
        }
        if let Some(diagnostic) = &self.diagnostic
            && let Some(state) = diagnostic.state.as_ref()
        {
            let mut labels = proof_diagnostics::render::MemoryStateLabels::ambient();
            state.register_names(&mut labels);
            if !proof_trace::enabled_for(&diagnostic.claim_label) {
                let requirement =
                    proof_diagnostics::render_failed_requirement(state.as_ref(), &mut labels);
                if !requirement.is_empty() {
                    context.push(requirement);
                }
                if !proof_diagnostics::requirement_is_goal(state.as_ref())
                    && let Some(goal) = diagnostic.render_goal(&mut labels)
                {
                    context.push(format!("goal: {goal}"));
                }
                if diagnostic.checks.is_some() {
                    let recent = state
                        .premises(8)
                        .into_iter()
                        .filter(|premise| !proof_diagnostics::is_internal_premise(premise))
                        .cloned()
                        .collect::<Vec<_>>();
                    let premises = state.kernel_goal().map_or_else(
                        || recent.clone(),
                        |goal| diagnostics::pure_facts_relevant_to(goal, &recent),
                    );
                    if !premises.is_empty() {
                        let mut available = format!(
                            "premises in scope (showing up to 8 relevant facts from {} recorded premises):",
                            state.premise_count(),
                        );
                        for premise in premises.iter().take(8) {
                            available.push_str("\n  ");
                            available.push_str(
                                &proof_diagnostics::render::render_proposition_labeled(
                                    premise,
                                    &mut labels,
                                ),
                            );
                        }
                        context.push(available);
                    }
                }
                if let Some(checks) = &diagnostic.checks
                    && (!checks.reads.is_empty() || !checks.walks.is_empty())
                {
                    context.push(proof_diagnostics::render_check_observations(
                        checks,
                        &mut labels,
                        false,
                    ));
                }
                let legend = labels.trace_legend();
                if !legend.is_empty() {
                    context.push(legend);
                }
            }
            if self.failed_tactic == Some("close")
                && let Some(Proposition::Exists { .. }) = state.kernel_goal()
            {
                context.push(
                    "help: choose a witness with `witness(<value>);`, then prove its body"
                        .to_string(),
                );
            }
        }
        // A refused step's goal is the requirement it could not establish,
        // read at the statement's pre-state.
        let traced = self
            .diagnostic
            .as_ref()
            .is_some_and(|diagnostic| proof_trace::enabled_for(&diagnostic.claim_label));
        if !traced && !context.iter().any(|line| line.starts_with("goal: ")) {
            // The failed state names the locals that hold the goal's values.
            let mut labels = proof_diagnostics::render::MemoryStateLabels::ambient();
            if let Some(state) = self
                .diagnostic
                .as_ref()
                .and_then(|diagnostic| diagnostic.state.as_ref())
            {
                state.register_names(&mut labels);
            }
            if let Some(goal) = self.unresolved_requirement_goal() {
                context.push(format!(
                    "goal: {}",
                    self.render_requirement_goal(goal, &mut labels)
                ));
                let legend = labels.trace_legend();
                if !legend.is_empty() {
                    context.push(legend.trim().to_owned());
                }
                // A C statement's requirement is a goal at its pre-state.
                if matches!(goal, Proposition::Predicate { name, .. }
                    if name.starts_with(crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX))
                {
                    context.push(
                        "help: establish bounds for this pointer value, for example by preserving the complete pointer across writes; C address equality alone does not establish bounds"
                            .to_owned(),
                    );
                } else if report.contains("\n  C statement at ")
                    && self
                        .report_detail
                        .as_ref()
                        .and_then(|detail| detail.live_view_write_overlap)
                        != Some(true)
                {
                    context.push(
                        "help: to prove the goal explicitly, step to this statement and prove it there with `have <goal> by { ... }`"
                            .to_owned(),
                    );
                }
            } else if let Some(resource) = self.missing_resource() {
                context.push(format!(
                    "goal: {}",
                    proof_diagnostics::render::render_resource_fact_spelled(resource, &mut labels)
                ));
            }
        }
        if !context.iter().any(|line| line.starts_with("goal: "))
            && let Some(goal) = self
                .report_detail
                .as_ref()
                .and_then(|detail| detail.written_goal.as_deref())
        {
            context.push(format!("goal: {goal}"));
        }
        (report, context)
    }

    /// A source-facing verification failure. The full `report()` retains
    /// bounded kernel premises and search context for `--trace-proof`.
    pub fn concise_report(&self) -> String {
        let (mut report, context) = self.concise_report_parts();
        if !context.is_empty() {
            report.push_str("\n\n");
            report.push_str(&context.join("\n"));
        }
        bound_diagnostic_message(report)
    }

    /// Trace context to append after the same source-facing error header used
    /// by ordinary `click verify`. No repeated error classification or tactic
    /// metadata belongs in this section.
    pub fn trace_context_report(&self) -> Option<String> {
        self.trace_context_report_with_tactic_locations(
            &|_| None,
            &|_, _| None,
            &|_, _| false,
            None,
        )
    }

    /// Render a trace with source labels resolved by the CLI at the terminal
    /// boundary, without making proof checking depend on source lookup.
    pub fn trace_context_report_with_tactic_locations(
        &self,
        tactic_location: &dyn Fn(&[usize]) -> Option<(String, crate::source::SourcePosition)>,
        branch_arm: &dyn Fn(&[usize], &crate::source::SourcePosition) -> Option<usize>,
        have_body_contains: &dyn Fn(&[usize], &crate::source::SourcePosition) -> bool,
        target: Option<&crate::source::SourcePosition>,
    ) -> Option<String> {
        let _accessors = self.report_model_accessor_scope();
        let diagnostic = self.diagnostic.as_ref()?;
        if !matches!(
            self.kind,
            ClickErrorKind::Proof | ClickErrorKind::Unsupported | ClickErrorKind::Internal
        ) || !proof_trace::enabled_for(&diagnostic.claim_label)
        {
            return None;
        }
        let _typed = proof_diagnostics::render::TypedNotationScope::enter();
        let mut labels = self
            .report_detail
            .as_ref()
            .and_then(|detail| detail.labels.as_ref())
            .map_or_else(
                proof_diagnostics::render::MemoryStateLabels::ambient,
                |labels| labels.0.as_ref().clone(),
            );
        let context = proof_diagnostics::render_trace_context_with_requirement(
            diagnostic,
            self.search_failures
                .as_deref()
                .map_or(&[][..], Vec::as_slice),
            self.unresolved_requirement_goal(),
            self.missing_resource(),
            &mut labels,
        );
        let trace = diagnostic
            .state
            .as_ref()
            .and_then(|state| {
                state.proof_trace(
                    &diagnostic.claim_label,
                    &mut labels,
                    tactic_location,
                    branch_arm,
                    have_body_contains,
                    target,
                    diagnostic.failing_path,
                )
            })
            .map(|trace| {
                trace
                    .lines()
                    .map(|line| line.strip_prefix("  ").unwrap_or(line))
                    .collect::<Vec<_>>()
                    .join("\n")
            });
        match (context.is_empty(), trace) {
            (true, None) => None,
            (true, Some(trace)) => Some(trace),
            (false, None) => Some(context),
            (false, Some(trace)) => Some(format!("{trace}\n\n{context}")),
        }
    }

    pub fn proof_source_tactic_path(&self) -> Option<&[usize]> {
        self.diagnostic
            .as_ref()?
            .origin
            .source_tactic_path
            .as_deref()
    }

    pub fn kind(&self) -> ClickErrorKind {
        use instrumentation::VerificationStop;
        match self.verification_stop {
            Some(VerificationStop::Search) => ClickErrorKind::Proof,
            Some(VerificationStop::Checking) => ClickErrorKind::Internal,
            Some(VerificationStop::RunWork) => ClickErrorKind::WorkLimitReached,
            Some(VerificationStop::WallClock) => ClickErrorKind::TimedOut,
            None => self.kind,
        }
    }

    /// Whether this error came from a budget or crash-containment stop.
    pub fn verification_stopped(&self) -> bool {
        self.verification_stop.is_some()
    }

    /// The implicit proof operation that refused this tactic, if any.
    pub fn implicit_tactic_step(&self) -> Option<&'static str> {
        if self.proof_refusal() == Some(ProofRefusal::Tactic) {
            self.report_detail.as_ref()?.implicit_step
        } else {
            None
        }
    }

    /// The proof refusal the terminal report attributes to this error.
    pub fn proof_refusal(&self) -> Option<ProofRefusal> {
        match self.verification_stop {
            Some(instrumentation::VerificationStop::Search) => {
                return Some(match self.proof_refusal {
                    Some(ProofRefusal::ImplicitStatementSearch) => {
                        ProofRefusal::ImplicitStatementSearch
                    }
                    _ => ProofRefusal::UnsuccessfulSearch,
                });
            }
            Some(_) => return None,
            None => {}
        }
        if self.kind != ClickErrorKind::Proof {
            return None;
        }
        self.proof_refusal.or_else(|| {
            let checked_step = self.diagnostic.as_ref().is_some_and(|diagnostic| {
                diagnostic.origin.stage == proof_diagnostics::ProofDiagnosticStage::CheckedStep
            });
            (self.failed_tactic.is_some()
                || self.proof_source_tactic_path().is_some()
                || checked_step)
                .then_some(ProofRefusal::Tactic)
        })
    }

    pub fn verification_diagnostic(&self) -> VerificationDiagnostic<'_> {
        let kind = self.kind();
        let refusal = self.proof_refusal();
        let outcome = match kind {
            ClickErrorKind::Syntax => VerificationOutcome::SyntaxError,
            ClickErrorKind::Type => VerificationOutcome::TypeError,
            ClickErrorKind::WorkLimitReached => VerificationOutcome::WorkLimitReached,
            ClickErrorKind::TimedOut => VerificationOutcome::TimedOut,
            ClickErrorKind::Unsupported => VerificationOutcome::Unsupported,
            ClickErrorKind::Internal => VerificationOutcome::InternalError,
            ClickErrorKind::Proof => match refusal {
                Some(ProofRefusal::Tactic) => VerificationOutcome::TacticError,
                Some(ProofRefusal::UnsuccessfulSearch | ProofRefusal::ImplicitStatementSearch) => {
                    VerificationOutcome::UnsuccessfulSearch
                }
                Some(ProofRefusal::IncompleteProof) => VerificationOutcome::IncompleteProof,
                Some(ProofRefusal::Contract) => VerificationOutcome::ContractError,
                None => VerificationOutcome::InternalError,
            },
        };
        VerificationDiagnostic {
            error: self,
            outcome,
            missing_classification: kind == ClickErrorKind::Proof && refusal.is_none(),
        }
    }

    fn report_label(&self) -> &'static str {
        self.verification_diagnostic().outcome().label()
    }

    pub(crate) fn with_proof_refusal(mut self, refusal: ProofRefusal) -> Self {
        // Preserve the innermost refusal through wrappers. The implicit closer
        // can replace a checked tactic's refusal after searching for its requirement.
        if self.proof_refusal.is_none()
            || self.proof_refusal == Some(ProofRefusal::Tactic)
                && refusal == ProofRefusal::ImplicitStatementSearch
                && self.unresolved_requirement.is_some()
        {
            self.proof_refusal = Some(refusal);
        }
        self
    }

    /// The claim that supplied this proof failure's checked state, if any.
    fn missing_tactic_requirement(&self) -> Option<&str> {
        self.report_detail
            .as_ref()?
            .missing_tactic_requirement
            .as_deref()
    }

    /// The Click declaration this failure is about, when it has no tactic
    /// or C statement to name: the terminal report shows where it is
    /// written.
    pub fn proof_declaration(&self) -> Option<&str> {
        self.report_detail.as_ref()?.declaration.as_deref()
    }

    /// The claim and source tactic path the terminal report excerpts: the
    /// failing step's own site, or else the tactic that was being checked
    /// when a failure with no site arose.
    pub fn proof_source_site(&self) -> Option<(&str, &[usize])> {
        if let (Some(claim), Some(path)) =
            (self.proof_claim_label(), self.proof_source_tactic_path())
        {
            return Some((claim, path));
        }
        let (claim, path) = self.report_detail.as_ref()?.source_tactic.as_ref()?;
        Some((claim, path))
    }

    /// Locates a proof failure that names no source by what the verifier
    /// was working on: the tactic being checked, or else the declaration
    /// being verified. A failure that already has a site keeps it.
    pub(crate) fn located_by_ambient_source(mut self) -> Self {
        if self.kind != ClickErrorKind::Proof
            || self.proof_source_site().is_some()
            || self.proof_declaration().is_some()
        {
            return self;
        }
        let (declaration, tactic) = AMBIENT_PROOF_SOURCE.with(|ambient| {
            let ambient = ambient.borrow();
            (ambient.declaration.clone(), ambient.tactic.clone())
        });
        if declaration.is_none() && tactic.is_none() {
            return self;
        }
        let detail = std::sync::Arc::make_mut(self.report_detail.get_or_insert_default());
        match tactic {
            Some((claim, source_index)) => {
                detail.source_tactic = Some((claim, vec![source_index]));
            }
            None => detail.declaration = declaration,
        }
        self
    }

    /// Shows a failure that names no source the declaration that was being
    /// checked when it arose, whatever kind of failure it is. Declaration
    /// checking has no tactic to name.
    pub(crate) fn located_by_ambient_declaration(mut self) -> Self {
        if self.proof_source_site().is_some() || self.proof_declaration().is_some() {
            return self;
        }
        let declaration = AMBIENT_PROOF_SOURCE.with(|ambient| ambient.borrow().declaration.clone());
        if let Some(declaration) = declaration {
            std::sync::Arc::make_mut(self.report_detail.get_or_insert_default()).declaration =
                Some(declaration);
        }
        self
    }

    /// Records the Click declaration this failure is about. A failure
    /// already attributed keeps its declaration.
    pub(crate) fn at_declaration(mut self, name: &str) -> Self {
        let detail = std::sync::Arc::make_mut(self.report_detail.get_or_insert_default());
        if detail.declaration.is_none() {
            detail.declaration = Some(name.to_owned());
        }
        self
    }

    pub fn proof_claim_label(&self) -> Option<&str> {
        self.diagnostic
            .as_ref()
            .map(|diagnostic| diagnostic.claim_label.as_str())
    }

    pub(crate) fn with_kind(mut self, kind: ClickErrorKind) -> Self {
        if self.kind != ClickErrorKind::Internal {
            self.kind = kind;
        }
        self.rendered = std::sync::OnceLock::new();
        self
    }

    pub(crate) fn with_failed_tactic(mut self, tactic: &'static str) -> Self {
        if self.failed_tactic.is_none() {
            self.failed_tactic = Some(tactic);
            self.rendered = std::sync::OnceLock::new();
        }
        self
    }

    pub(in crate::surface) fn missing_resource(&self) -> Option<&crate::kernel::ResourceFact> {
        self.report_detail.as_ref()?.missing_resource.as_ref()
    }

    pub(in crate::surface) fn with_missing_resource(
        mut self,
        resource: &crate::kernel::ResourceFact,
    ) -> Self {
        std::sync::Arc::make_mut(self.report_detail.get_or_insert_default()).missing_resource =
            Some(resource.clone());
        self
    }

    /// Records the resource a refused C operation was missing, when that is
    /// what refused it.
    pub(in crate::surface) fn with_runtime_missing_resource(
        self,
        error: &crate::kernel::RuntimeError,
    ) -> Self {
        match error {
            crate::kernel::RuntimeError::MissingResource { resource } => {
                self.with_missing_resource(resource)
            }
            _ => self,
        }
    }

    pub(crate) fn with_missing_tactic_requirement(mut self, required: String) -> Self {
        std::sync::Arc::make_mut(self.report_detail.get_or_insert_default())
            .missing_tactic_requirement = Some(required);
        self.rendered = std::sync::OnceLock::new();
        self
    }

    /// Marks a refusal whose statement or condition has path cases that a
    /// case split on their facts would separate.
    pub(crate) fn with_path_case_split(mut self) -> Self {
        self.path_case_split = Some(std::sync::Arc::new(PathCaseSplit::Unspelled));
        self
    }

    /// Whether this refusal is a simple tactic declining to split path cases.
    pub(crate) fn is_path_case_split(&self) -> bool {
        self.path_case_split.is_some()
    }

    /// Records the condition a proof-level case split separates this
    /// refusal's path cases on first.
    pub(crate) fn with_path_case_condition(mut self, condition: ClickProposition) -> Self {
        self.path_case_split = Some(std::sync::Arc::new(PathCaseSplit::Condition(condition)));
        self
    }

    /// The condition a proof-level case split separates this refusal's path
    /// cases on first, when one has a Click spelling.
    pub(crate) fn path_case_condition(&self) -> Option<&ClickProposition> {
        match self.path_case_split.as_deref() {
            Some(PathCaseSplit::Condition(condition)) => Some(condition),
            _ => None,
        }
    }

    /// Records the proof `match` that separates this refusal's path cases:
    /// the variants of an enum value a Rust `match` selects among.
    pub(crate) fn with_path_case_match(mut self, split: ProofMatch) -> Self {
        self.path_case_split = Some(std::sync::Arc::new(PathCaseSplit::Match(split)));
        self
    }

    /// The proof `match` that separates this refusal's path cases, when they
    /// are an enum value's variants.
    pub(crate) fn path_case_match(&self) -> Option<&ProofMatch> {
        match self.path_case_split.as_deref() {
            Some(PathCaseSplit::Match(split)) => Some(split),
            _ => None,
        }
    }

    /// The bounded cause text, without rendering proof state or premises.
    pub(crate) fn raw_summary(&self) -> &str {
        &self.message
    }

    pub(crate) fn diagnostic(&self) -> Option<&proof_diagnostics::ProofFailureDiagnostic> {
        self.diagnostic.as_deref()
    }

    /// The requirement a refused step could not establish, as the goal an
    /// explicit proof would prove at the step's pre-state.
    fn unresolved_requirement_goal(&self) -> Option<&Proposition> {
        // An assertion's false-path obligation is `0 == 1`; its goal is the
        // asserted condition, recorded for the report.
        if self
            .unresolved_requirement
            .as_ref()
            .is_some_and(|requirement| requirement.assertion_condition.is_some())
            && let Some(goal) = self
                .report_detail
                .as_ref()
                .and_then(|detail| detail.goal.as_ref())
        {
            return Some(goal);
        }
        self.unresolved_requirement
            .as_ref()
            .map(|requirement| &requirement.proposition)
            .or_else(|| self.report_detail.as_ref()?.goal.as_ref())
    }

    /// Records the goal an assertion's refused truthiness obligation stands
    /// for, when the pre-state evaluates its condition to one.
    pub(in crate::surface) fn with_reported_assertion_goal(
        self,
        goal: Option<Proposition>,
    ) -> Self {
        match goal {
            Some(goal) => self.with_reported_goal(goal),
            None => self,
        }
    }

    fn report_model_accessor_scope(&self) -> Option<diagnostics::ModelAccessorScope> {
        Some(
            self.report_detail
                .as_ref()?
                .model_accessors
                .as_ref()?
                .enter(),
        )
    }

    /// Records `goal`, the proposition a refused C operation needed, for the
    /// report alone.
    pub(in crate::surface) fn with_reported_goal(mut self, goal: Proposition) -> Self {
        std::sync::Arc::make_mut(self.report_detail.get_or_insert_default()).goal = Some(goal);
        self.rendered = std::sync::OnceLock::new();
        self
    }

    pub(in crate::surface) fn with_unlowered_goal(mut self, goal: String) -> Self {
        std::sync::Arc::make_mut(self.report_detail.get_or_insert_default()).written_goal =
            Some(goal);
        self
    }

    pub(in crate::surface) fn with_missing_theorem_requirement(mut self, fact: String) -> Self {
        std::sync::Arc::make_mut(self.report_detail.get_or_insert_default())
            .missing_theorem_requirement = Some(fact);
        self.rendered = std::sync::OnceLock::new();
        self
    }

    pub(in crate::surface) fn missing_theorem_requirement(&self) -> Option<&str> {
        self.report_detail
            .as_ref()?
            .missing_theorem_requirement
            .as_deref()
    }

    pub(in crate::surface) fn unresolved_requirement(&self) -> Option<&UnresolvedRequirement> {
        self.unresolved_requirement.as_deref()
    }

    fn render_requirement_goal(
        &self,
        goal: &Proposition,
        labels: &mut proof_diagnostics::render::MemoryStateLabels,
    ) -> String {
        if self
            .report_detail
            .as_ref()
            .is_some_and(|detail| detail.live_view_write_overlap.is_some())
        {
            return proof_diagnostics::render::render_view_separation_goal(goal, labels);
        }
        proof_diagnostics::render::render_proposition_labeled(goal, labels)
    }

    pub(in crate::surface) fn with_unresolved_requirement(
        mut self,
        obligation: &ProofObligation,
    ) -> Self {
        if let Some(overlap) = obligation.live_view_write_overlap() {
            std::sync::Arc::make_mut(self.report_detail.get_or_insert_default())
                .live_view_write_overlap = Some(overlap);
        }
        self.unresolved_requirement = Some(std::sync::Arc::new(UnresolvedRequirement {
            proposition: obligation.proposition().clone(),
            context: diagnostics::describe_proof_obligation_context(obligation),
            introductions: obligation.introductions().cloned().unwrap_or_default(),
            call_site: obligation.call_requirement_site().cloned(),
            assertion_condition: None,
            theorem_source: None,
            statement_safety: obligation.is_signed_arithmetic_bound(),
            surface: None,
        }));
        self
    }

    pub(in crate::surface) fn with_statement_safety_goal(self, goal: Proposition) -> Self {
        let mut error = self
            .with_reported_goal(goal.clone())
            .with_unresolved_requirement(&ProofObligation::verification_condition(goal));
        std::sync::Arc::make_mut(error.unresolved_requirement.as_mut().unwrap()).statement_safety =
            true;
        error
    }

    pub(in crate::surface) fn with_safety_preparation_error(self, detail: &str) -> Self {
        self.with_rewritten_place(|reason| Some(format!("{detail}\n{reason}")))
            .with_kind(ClickErrorKind::Internal)
    }

    /// Records a simple tactic's requirement that no execution obligation
    /// carries: the lowered `proposition`, its Surface spelling, and what
    /// owes it.
    pub(in crate::surface) fn with_spelled_requirement(
        mut self,
        proposition: Proposition,
        surface: ClickProposition,
        context: String,
    ) -> Self {
        self.unresolved_requirement = Some(std::sync::Arc::new(UnresolvedRequirement {
            proposition,
            context: Some(context),
            introductions: Default::default(),
            call_site: None,
            assertion_condition: None,
            theorem_source: None,
            statement_safety: false,
            surface: Some(surface),
        }));
        self
    }

    pub(in crate::surface) fn with_theorem_requirement_source(
        mut self,
        source: TheoremRequirementSource,
    ) -> Self {
        let requirement = self
            .unresolved_requirement
            .as_mut()
            .expect("attached theorem premise");
        std::sync::Arc::make_mut(requirement).theorem_source = Some(std::sync::Arc::new(source));
        self
    }

    /// Records the asserted condition behind an `assert`'s false-path
    /// truthiness requirement; see [`UnresolvedRequirement::assertion_condition`].
    pub(in crate::surface) fn with_assertion_condition(
        mut self,
        condition: Option<&crate::kernel::ProgramExpression>,
    ) -> Self {
        if let (Some(condition), Some(requirement)) =
            (condition, self.unresolved_requirement.as_mut())
        {
            std::sync::Arc::make_mut(requirement).assertion_condition = Some(condition.clone());
        }
        self
    }

    pub(crate) fn with_check_observations(
        mut self,
        checks: proof_diagnostics::CheckObservations,
    ) -> Self {
        // The innermost proof refusal owns its observations. An enclosing
        // scope's capture may be empty because the nested collector already
        // consumed them; preserve that more precise record.
        if let Some(diagnostic) = &mut self.diagnostic
            && diagnostic.checks.is_none()
        {
            std::sync::Arc::make_mut(diagnostic).checks = Some(std::sync::Arc::new(checks));
            self.rendered = std::sync::OnceLock::new();
        }
        self
    }

    /// Names the function outcome path this failure lies on, so its trace
    /// shows the arm of a terminal join that holds it.
    pub(crate) fn with_failing_path(mut self, path_index: usize) -> Self {
        if let Some(diagnostic) = self.diagnostic.as_mut() {
            std::sync::Arc::make_mut(diagnostic).failing_path = Some(path_index);
            self.rendered = std::sync::OnceLock::new();
        }
        self
    }

    pub(crate) fn with_search_failures(
        mut self,
        failures: Vec<proof_diagnostics::ProofSearchFailure>,
    ) -> Self {
        if !failures.is_empty() {
            self.search_failures = Some(std::sync::Arc::new(failures));
            self.rendered = std::sync::OnceLock::new();
        }
        self
    }

    /// Restates where a refusal happened: `rewrite` maps the leading place of
    /// the cause text (`` `claim` tactic N ``) to the place a reader wrote,
    /// in the summary and in the attached diagnostic alike. A message whose
    /// place `rewrite` does not recognize is kept as it is.
    pub(in crate::surface) fn with_rewritten_place(
        mut self,
        rewrite: impl Fn(&str) -> Option<String>,
    ) -> Self {
        if let Some(message) = rewrite(&self.message) {
            self.message = message;
            self.rendered = std::sync::OnceLock::new();
        }
        if let Some(diagnostic) = &self.diagnostic
            && let Some(reason) = rewrite(&diagnostic.reason)
        {
            let mut diagnostic = diagnostic.as_ref().clone();
            diagnostic.reason = reason;
            self.diagnostic = Some(std::sync::Arc::new(diagnostic));
            self.rendered = std::sync::OnceLock::new();
        }
        self
    }

    /// Attributes a failure no written tactic owns to the written tactic
    /// that generated the failing step, so the report can show its source.
    /// A failure that already names a written tactic keeps it.
    pub(crate) fn attributed_to_source_tactic(mut self, source_index: usize) -> Self {
        if let Some(diagnostic) = self.diagnostic.as_mut()
            && diagnostic.origin.source_tactic_path.is_none()
        {
            std::sync::Arc::make_mut(diagnostic)
                .origin
                .source_tactic_path = Some(vec![source_index]);
        }
        self
    }

    /// Records the labels this refusal's own legend used, so its trace
    /// continues that numbering.
    pub(crate) fn with_report_labels(
        mut self,
        labels: proof_diagnostics::render::MemoryStateLabels,
    ) -> Self {
        std::sync::Arc::make_mut(self.report_detail.get_or_insert_default()).labels =
            Some(ReportLabels(std::sync::Arc::new(labels)));
        self
    }

    pub(crate) fn with_context(self, prefix: impl AsRef<str>) -> Self {
        self.with_prefix(format!("{}: ", prefix.as_ref()))
    }

    pub(crate) fn with_prefix(self, prefix: impl AsRef<str>) -> Self {
        let summary = format!("{}{}", prefix.as_ref(), self.message);
        Self {
            message: diagnostics::bound_error_message(summary),
            rendered: std::sync::OnceLock::new(),
            kind: self.kind,
            failed_tactic: self.failed_tactic,
            proof_refusal: self.proof_refusal,
            verification_stop: self.verification_stop,
            diagnostic: self.diagnostic,
            search_failures: self.search_failures,
            unresolved_requirement: self.unresolved_requirement,
            report_detail: self.report_detail,
            path_case_split: self.path_case_split,
            timing_tactic: self.timing_tactic,
        }
    }

    fn emit_timing_failure(&self) {
        if !instrumentation::enabled() {
            return;
        }
        if let Some(tactic) = &self.timing_tactic {
            instrumentation::emit(VerificationEvent::TacticFailed(TacticEvent {
                source_tactic_path: tactic.source_tactic_path.clone(),
                claim: tactic.claim_label.clone(),
                tactic_index: tactic.tactic_index,
                tactic_name: tactic.tactic_name.clone(),
                class: tactic.tactic_class.clone(),
                statement_index: tactic.statement_index,
                source_index: tactic.source_index,
            }));
        }
    }
}

impl Clone for ClickError {
    fn clone(&self) -> Self {
        Self {
            message: self.message.clone(),
            rendered: std::sync::OnceLock::new(),
            kind: self.kind,
            failed_tactic: self.failed_tactic,
            proof_refusal: self.proof_refusal,
            verification_stop: self.verification_stop,
            diagnostic: self.diagnostic.clone(),
            search_failures: self.search_failures.clone(),
            unresolved_requirement: self.unresolved_requirement.clone(),
            report_detail: self.report_detail.clone(),
            path_case_split: self.path_case_split.clone(),
            timing_tactic: self.timing_tactic.clone(),
        }
    }
}

impl PartialEq for ClickError {
    fn eq(&self, other: &Self) -> bool {
        self.message == other.message
            && self.kind == other.kind
            && self.failed_tactic == other.failed_tactic
            && self.proof_refusal == other.proof_refusal
            && self.verification_stop == other.verification_stop
            && self.diagnostic == other.diagnostic
            && self.search_failures == other.search_failures
            && self.unresolved_requirement == other.unresolved_requirement
            && self.report_detail == other.report_detail
            && self.path_case_split == other.path_case_split
            && self.timing_tactic == other.timing_tactic
    }
}

impl Eq for ClickError {}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod retained_frame_tests {
    use super::*;
    mod scaling_tests {
        include!("scaling_tests/surface/retained_frame_tests.rs");
    }
}
