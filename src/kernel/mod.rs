//! Experimental rich kernel for systems-code proofs.
//!
//! This module keeps the LCF shape: `Theorem` is an abstract object whose
//! constructor is not public. Public theorem constructors in this module are
//! Click axioms: trusted built-in operations that produce theorem objects
//! directly.
//!
pub(crate) mod api;

/// Version of the resource and stable-view semantics used by proof
/// artifacts.  This is deliberately separate from source and compiler
/// identities: changing the authority interpretation must invalidate an old
/// certificate even when its inputs are byte-identical.
pub const RESOURCE_SEMANTICS_VERSION: u32 = 74;

pub(crate) mod assumptions;
mod equality_graph;
mod eval;
mod fold_read_summary;
mod functions;
mod owned_footprint_reach;
mod population_access;
// Population authority: checked anchor lifetimes, registrations and the C
// creation ledger.
mod population_authority;
pub(crate) use population_authority::c_creation::CheckedPopulationAuthorityExchange;
pub(crate) use population_authority::c_creation::CheckedPopulationMemberExchange;
mod quantified_frame;
mod resource_description;
mod thread_confinement;
pub(crate) use functions::ResourceBodyClauseRecord;
pub(crate) use functions::TacticApplicationRefusal;
pub(crate) use functions::assume_scalar_object_inputs;
pub(crate) use functions::interface_join_instance_fields;
pub(crate) use functions::project_interface_native_spans;
#[cfg(test)]
pub(crate) use functions::rewrite_resource_instance;
pub(crate) use functions::rewrite_resource_instance_selecting_children;
pub(crate) use functions::{
    InstantiatedCompositeResourceFacts, instantiate_composite_resource_facts,
    instantiate_private_member_body_facts,
};
pub(crate) use functions::{
    assume_checked_native_composite_places, c_independent_function_input_state,
    c_state_with_assumed_native_record_inputs,
};
pub use resource_description::{ResourceDescription, ResourceReference};
pub(crate) use thread_confinement::propagate_population_reach;
mod iterated;
pub(crate) use iterated::{IteratedStep, apply_iterated_step, plan_iterated_guard_store};
// V0-V6 of the stable-view migration build the checked semantic spine before
// V7 routes ordinary calls through it.
mod loans;
#[cfg(test)]
pub(crate) use loans::LoanLedger;
#[cfg(test)]
pub(crate) use loans::LoanRefusal;
pub(crate) use loans::owned_reservation_miss_for;
pub(crate) use loans::{
    CheckedLoanCallEvidenceSequence, LoanViewBinding, concat_checked_loan_evidence,
    empty_checked_loan_evidence_sequence,
};
pub use loans::{
    LoanOriginKind, LoanOverlapStatus, LoanRefusalCategory, LoanRefusalDiagnostic,
    LoanRefusalOperation, LoanRefusalSubject,
};
mod integer_truncation_laws;
mod loops;
mod memory_provenance;
pub(crate) mod model_fields;
mod mutexes;
mod named_authority;
pub(crate) use integer_truncation_laws::{
    integer_truncation_law_requirements, prove_integer_truncation_law,
};
mod nat_integer;
pub(crate) use nat_integer::{check_nat_integer_law, is_conversion_nat_type, is_nat_integer_image};
mod primitives;
pub(crate) mod proof;
mod publication;
mod pure_functions;
pub(crate) mod sorry;
#[cfg(test)]
pub(crate) use fold_read_summary::registered_fold_read_summary;
pub use fold_read_summary::{
    CFoldReadDefinition, CheckedFoldReadSummary, FoldReadDecline, register_fold_read_definition,
};
pub(crate) use fold_read_summary::{FoldFrameRefusal, frame_fold_application_transport};
pub use pure_functions::{
    CPureFunctionDefinition, CPureFunctionParameter, register_pure_function_definition,
};
pub(crate) use quantified_frame::{QuantifiedFrameRefusal, frame_quantified_transport};
pub(crate) mod reasoning;
#[cfg(test)]
pub(crate) use reasoning::variable_collection::count_cells_collected;
pub(crate) mod resource_tracker;
mod spec;
pub(crate) use spec::{
    SpecCaptureRefusal, capture_spec_algebraic_value, capture_spec_integer_value,
    capture_spec_integer_value_with_guards,
};
mod termination;
// Checked internal fork/join; binding to imported pthread declarations is a
// separate checkpoint, so no C execution path invokes these rules yet.
mod threads;

pub use api::*;
pub(crate) use assumptions::current_memory_loads_in_term;
pub(crate) use assumptions::proposition_has_free_bitvector_variable;
pub(crate) use assumptions::{
    PureFactContextIdScope, arm_frame_composite_definitions, capture_implicit_reasoning_provenance,
    collect_reasoning_provenance, finite_forall_goal_instances,
    record_implicit_reasoning_provenance, with_search_attempt_rollback,
};
pub(crate) use equality_graph::logical_pointer_read_term;
pub(crate) use eval::canonical_condition_fact;
pub(crate) use eval::canonical_form_of_load;
pub(crate) use eval::canonical_form_of_typed_load;
pub(crate) use eval::canonical_term;
pub(crate) use eval::canonicalized_offset_index_term;
#[cfg(test)]
pub(crate) use eval::count_canonical_at_creation_violations;
pub(crate) use eval::is_load_variable;
pub(crate) use eval::is_load_variable_defining_fact;
pub(crate) use eval::load_access_width_at_address_or_widest;
pub(crate) use eval::load_access_width_or_widest;
pub(crate) use eval::load_term_access_width;
#[cfg(test)]
pub(crate) use eval::load_variable_for_cell_with_origin;
pub(crate) use eval::load_variable_for_term;
pub(crate) use eval::offsets_have_same_canonical_form;
pub(crate) use eval::proposition_mentions_registered_load_variable;
#[cfg(test)]
pub(crate) use eval::record_load_variable_defining_fact;
pub(crate) use eval::registered_load_bytes_for_variable;
pub(crate) use eval::registered_load_for_variable;
pub(crate) use eval::registered_load_origin_for_variable;
pub(crate) use eval::resolve_pending_heap_allocations;
pub(crate) use eval::terms_have_same_canonical_form;
#[cfg(test)]
pub(crate) use eval::{
    load_variable_registry_len, with_load_variable_range, with_load_variable_registry_capacity,
};
pub(crate) use eval::{
    registered_load_kind_for_variable, registered_load_origin_term_for_variable,
    registered_load_term_for_variable,
};
pub(crate) use functions::ResourceModelArmDecision;
pub(crate) use functions::ResourceModelArmSelection;
pub(crate) use functions::ResourceRewriteRefusal;
pub(crate) use functions::c_type_spelling;
pub(crate) use functions::checked_composite_projection_evidence;
pub(crate) use functions::decide_resource_model_arm;
pub(crate) use functions::establish_resource_derived_loop_frames;
pub(crate) use functions::evaluate_guarded_contract_condition_with_loop_entry;
pub(crate) use functions::guard_contract_refusal;
pub(crate) use functions::initialize_c_function_globals;
pub(crate) use functions::initialize_c_program_storage;
#[cfg(test)]
pub(crate) use functions::measure_resource_clause_attempts;
pub(crate) use functions::modified_by_value_aggregate_parameter_with_current_ensure_in_source;
pub(crate) use functions::publish_instance_arms;
pub(crate) use functions::select_resource_model_arm;
pub(crate) use functions::stable_symbolic_pointer_cell_value;
pub(crate) use functions::symbolic_call_result;
pub(crate) use functions::unreturned_allocation_at_function_exit;
pub(crate) use functions::unreturned_allocation_with_checked_returned_resources;
pub(crate) use functions::{StorageWriteOutsideFootprint, storage_writes_outside_owned_footprint};
pub(crate) use functions::{arm_algebraic_payload_spelling, arm_binding_program_spelling};
pub(crate) use functions::{
    contract_entry_partition_facts, evaluate_function_resource_context_with_metadata,
    project_contract_memory_effects, quantified_resource_requirement_assumptions,
    resource_clause_position_note, resource_clause_stall_note, unmatched_instance_body_views,
    validate_resource_derived_loop_frames,
};
pub use loops::CLoopBinder;
#[cfg(test)]
pub(crate) use loops::c_loop_state_components_match_at_back_edge;
pub(crate) use loops::{
    c_loop_binder_state_components_match_at_back_edge, c_loop_binders,
    c_loop_condition_may_continue, c_loop_state_with_loop_binders_rebound,
    loop_structural_descent_failure,
};
pub use memory_provenance::*;
pub(crate) use model_fields::algebraic_value_variable;
pub(crate) use primitives::resource_context_has_symbolic_range_read;
pub use primitives::*;
pub(crate) use reasoning::memory_effect_write_pointers;
pub(crate) use reasoning::memory_resolution::{
    ClosureFactCheck, closure_memoized_fact_check, with_closure_failure_memo,
};
pub(crate) use reasoning::resolve_load_variables_from_registry;
pub(crate) use reasoning::resolve_minted_load_variables;
pub(crate) use reasoning::substitute_integer_variable_in_pure_proposition;
pub(crate) use reasoning::substitute_pointer_variable_in_proposition;
pub use reasoning::{LoweringIntroduction, LoweringIntroductions};
pub(crate) use reasoning::{
    collect_bitvector_variables, collect_c_value_bitvector_variables,
    collect_spec_algebraic_expression_bitvector_variables, collect_spec_integer_bound_variables,
    collect_spec_integer_variables,
};
pub use termination::{
    CTerminationRefusal, CTerminationVerdicts, CUnsuitableCallback, c_termination_height_plan,
    c_verified_function_termination_rules,
};

/// The bitvector variables one condition fact mentions, including those
/// inside load pointers and memories. Facts sharing none of these cannot
/// constrain each other or a goal that mentions none of them, which premise
/// search uses to skip candidate pairs no derivation could connect.
pub(crate) fn condition_fact_variables(
    proposition: &primitives::Proposition,
) -> std::collections::BTreeSet<primitives::Variable> {
    let mut variables = std::collections::BTreeSet::new();
    if let primitives::Proposition::ConditionIs(condition, _) = proposition {
        reasoning::collect_condition_bitvector_variables(condition, &mut variables);
    }
    variables
}

mod prelude {
    pub(super) use super::api::*;
    pub(super) use super::eval::*;
    pub(super) use super::functions::*;
    pub(super) use super::loops::*;
    pub(super) use super::primitives::*;
    pub(super) use super::reasoning::*;
    pub(super) use super::spec::*;
    pub(super) use super::{ExecutionFactSource, ExecutionFacts};
    pub(super) use std::collections::{BTreeMap, BTreeSet};
}

/// The kernel vocabulary the Surface proposition planner is built from.
///
/// The planner in `src/surface/planning/proposition_search.rs` used to be a
/// kernel module, so it names kernel types directly. This is the complete,
/// deliberately enumerated list of what it may reach: the proposition and
/// term vocabulary, the derivation records it produces, the checked context
/// operations it advances state through, and the exact queries and frozen
/// atomic checkers it calls at its leaves. Nothing here issues authority --
/// a `PropositionDerivation` is inert until `check` validates it -- and
/// nothing under `src/kernel/` imports this module.
pub(crate) mod planning_api {
    pub(crate) use super::assumptions::proposition_reasoning::forall_loadable_range_parts;
    pub(crate) use super::assumptions::{
        algebraic_constructor_field_equalities, collect_proposition_conjuncts,
        proposition_derivation, reasoning_interrupted, simp_reasoning_interrupted,
    };
    pub(crate) use super::reasoning::order_reasoning::{
        FiniteForAllRange, collect_forall_chain, collect_or_cases, finite_forall_ranges,
        signed_i64_bitvector_constant,
    };
    pub(crate) use super::reasoning::path_facts::solve_builtin_prop;
    pub(crate) use super::reasoning::substitute_bitvector_variable_in_proposition;
    pub(crate) use super::reasoning::substitute_machine_constant_in_pure_proposition;
    #[cfg(test)]
    pub(crate) use super::reasoning::variable_collection::collect_condition_bitvector_variables;
    pub(crate) use super::reasoning::variable_collection::{
        collect_atomic_connection_keys, collect_proposition_bitvector_variables,
        collect_proposition_connection_variables, collect_proposition_frame_variables,
    };
}

#[cfg(test)]
mod tests;

thread_local! {
    static VERIFICATION_SESSION_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Counts the fresh sessions started on this thread, so state retained
    /// past a session (a reusable surface verification session's snapshots)
    /// can tell whether a later fresh session replaced the tables it names.
    static VERIFICATION_SESSION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The generation of this thread's current kernel tables: it advances each
/// time an outermost `VerificationSession` starts fresh. Snapshots and other
/// arena ids minted under one generation are meaningless under another, so a
/// caller that keeps kernel-derived state after its session ends compares
/// this value before reusing that state.
pub fn verification_session_generation() -> u64 {
    VERIFICATION_SESSION_GENERATION.with(std::cell::Cell::get)
}

/// The state a session's tables held at one moment, captured by
/// [`VerificationSession::capture_state`] and reinstalled by
/// [`VerificationSession::restore_state`].
#[derive(Clone)]
pub struct VerificationSessionState {
    generation: u64,
    arena: primitives::CMemoryArenaState,
    loads: eval::LoadRegistryState,
    model_fields: model_fields::ModelFieldRegistryState,
    blocks: primitives::BlockRegistriesState,
    pure_functions:
        std::collections::BTreeMap<String, std::sync::Arc<pure_functions::CPureFunctionDefinition>>,
    fold_reads: fold_read_summary::FoldReadSummariesState,
}

/// One verification's worth of kernel thread-local state.
///
/// The kernel keeps per-thread tables that are correct only within one
/// verification: the memory arena (snapshot ids and their DAG derivations;
/// interning dedups by content, so a later verification's snapshot with the
/// same content — a call havoc of a same-named callee, say — would inherit
/// the first verification's derivation and its mutable ranges), the load
/// registry (names are content-addressed, but their origins are live
/// snapshots of the arena that minted them), and the memo tables keyed by
/// arena ids or by fact-set content. Entering a session at the outermost
/// verification boundary starts a fresh arena and empties every such table,
/// so two verifications on one thread are as independent as two threads.
/// Nested entries (a verification inside a verification) keep the session.
/// `verifications_on_one_thread_are_independent` is the regression.
pub struct VerificationSession {
    fresh: bool,
}

impl VerificationSession {
    pub fn enter() -> Self {
        let outermost = VERIFICATION_SESSION_DEPTH.with(|depth| {
            let current = depth.get();
            depth.set(current + 1);
            current == 0
        });
        if outermost {
            VERIFICATION_SESSION_GENERATION
                .with(|generation| generation.set(generation.get().wrapping_add(1)));
            primitives::start_fresh_c_memory_arena();
            eval::clear_load_variable_registry();
            model_fields::clear_model_field_registry();
            primitives::clear_block_alignment_registry();
            primitives::clear_aggregate_selection_matches();
            primitives::clear_never_address_taken_locals();
            pure_functions::clear_pure_function_definitions();
            fold_read_summary::clear_fold_read_summaries();
            memory_provenance::clear_canonical_form_caches();
            memory_provenance::clear_provenance_memos();
            reasoning::memory_resolution::clear_canonical_memory_cache();
            reasoning::memory_resolution::clear_memory_resolution_memos();
            assumptions::clear_assumption_memos();
            assumptions::clear_context_inconsistency_memos();
            assumptions::clear_frame_expansion_memo();
            api::clear_borrowed_input_root_memo();
            reasoning::variable_collection::clear_shared_memory_variables();
            functions::clear_automatic_lifetime_retirement();
        }
        Self { fresh: outermost }
    }

    /// Joins this thread's current tables as a nested entry without
    /// clearing them, for a caller that retains state built under those
    /// tables (a reusable surface verification session) and checks it
    /// against them. Verifications inside the guard join too, instead of
    /// starting fresh tables that would invalidate the retained state.
    pub fn resume() -> Self {
        VERIFICATION_SESSION_DEPTH.with(|depth| depth.set(depth.get() + 1));
        Self { fresh: false }
    }

    /// Captures the state this thread's tables hold for the current
    /// session: the memory arena and every registry a session entry clears.
    /// Memo caches are not captured; they only remember answers.
    ///
    /// A reusable session captures this once its retained environment is
    /// built, and restores it before each check. The capture shares storage
    /// with the live tables, so it costs one handle per table entry.
    pub fn capture_state() -> VerificationSessionState {
        VerificationSessionState {
            generation: verification_session_generation(),
            arena: primitives::capture_c_memory_arena(),
            loads: eval::capture_load_variable_registry(),
            model_fields: model_fields::capture_model_field_registry(),
            blocks: primitives::capture_block_registries(),
            pure_functions: pure_functions::capture_pure_function_definitions(),
            fold_reads: fold_read_summary::capture_fold_read_summaries(),
        }
    }

    /// How many entries this thread's memory arena and load registries hold,
    /// for regressions that a reusable session's checks leave nothing behind.
    #[cfg(test)]
    pub fn state_entry_count() -> usize {
        primitives::c_memory_arena_entry_count() + eval::load_registry_entry_count()
    }

    /// Returns this thread's tables to a captured state and drops every memo
    /// cache, so a check starts from exactly what the capture's holder built
    /// and nothing an earlier check interned, named, or memoized remains.
    ///
    /// Without this, each check on a reusable session leaves its snapshots'
    /// storage pinned, its load names registered, and its memo entries
    /// cached, and the tables grow with every check. Anything created after
    /// the capture is meaningless after a restore; the holder keeps only
    /// state that existed when it captured.
    ///
    /// Returns `false`, changing nothing, when the tables belong to another
    /// session generation: the capture's ids would name nothing there.
    pub fn restore_state(state: &VerificationSessionState) -> bool {
        if verification_session_generation() != state.generation {
            return false;
        }
        primitives::restore_c_memory_arena(&state.arena);
        eval::restore_load_variable_registry(&state.loads);
        model_fields::restore_model_field_registry(&state.model_fields);
        primitives::restore_block_registries(&state.blocks);
        primitives::clear_aggregate_selection_matches();
        pure_functions::restore_pure_function_definitions(&state.pure_functions);
        fold_read_summary::restore_fold_read_summaries(&state.fold_reads);
        memory_provenance::clear_canonical_form_caches();
        memory_provenance::clear_provenance_memos();
        reasoning::memory_resolution::clear_canonical_memory_cache();
        reasoning::memory_resolution::clear_memory_resolution_memos();
        assumptions::clear_assumption_memos();
        assumptions::clear_context_inconsistency_memos();
        assumptions::clear_frame_expansion_memo();
        api::clear_borrowed_input_root_memo();
        reasoning::variable_collection::clear_shared_memory_variables();
        functions::clear_automatic_lifetime_retirement();
        true
    }

    /// Whether this entry started the session (and so cleared the kernel's
    /// tables), as opposed to joining an enclosing one. Callers holding
    /// their own per-verification caches of kernel snapshots clear them on
    /// a fresh session.
    pub fn is_fresh(&self) -> bool {
        self.fresh
    }
}

/// Drops every memoized answer that may depend on which locals the session
/// considers never address-taken. Used only when that set shrinks mid-session,
/// which no caller does today; see `record_never_address_taken_locals`.
pub fn clear_memory_resolution_memos_and_caches() {
    reasoning::memory_resolution::clear_memory_resolution_memos();
    reasoning::memory_resolution::clear_canonical_memory_cache();
    memory_provenance::clear_provenance_memos();
    assumptions::clear_assumption_memos();
}

/// Begins a new load-origin epoch for the function about to be verified;
/// see `registered_load_origin_for_variable`. Ids stay session-wide.
pub fn begin_load_origin_epoch() {
    eval::begin_load_origin_epoch();
}

impl Drop for VerificationSession {
    fn drop(&mut self) {
        VERIFICATION_SESSION_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

mod execution_facts;
pub use execution_facts::{ExecutionFactSource, ExecutionFacts, ExecutionFactsIter};
