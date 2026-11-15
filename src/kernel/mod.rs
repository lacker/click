//! Experimental rich kernel for systems-code proofs.
//!
//! This module keeps the LCF shape: `Theorem` is an abstract object whose
//! constructor is not public. Public theorem constructors in this module are
//! Click axioms: trusted built-in operations that produce theorem objects
//! directly.
//!
pub(crate) mod api;
pub mod program_expression;
mod region_footprint;
pub use region_footprint::RegionFootprint;
mod source_access;
mod source_loans;
pub(crate) use source_access::{
    ExecutedReferenceAccess, ExecutedReferenceBoundary, ReferenceAccessKind,
    ReferenceAccessSourceId, ReferenceBorrowSourceId,
};
pub use source_access::{StatementAssignSource, StatementStoreSource};
pub use source_loans::{ScalarReferenceEnd, ScalarReferenceScope};
pub(crate) use source_loans::{
    ScalarReferencePlanFamily, ScalarReferencePlanKey, ScalarReferenceScopeKey,
    ScalarReferenceScopePlan, ScalarReferenceSourcePlan,
};

/// Version of the resource and stable-view semantics used by proof
/// artifacts.  This is deliberately separate from source and compiler
/// identities: changing the authority interpretation must invalidate an old
/// certificate even when its inputs are byte-identical.
pub const RESOURCE_SEMANTICS_VERSION: u32 = 75;

pub(crate) mod assumptions;
mod difference_graph;
pub(crate) mod effective_type;
mod equality_graph;
mod eval;
mod execution_value;
pub(crate) use eval::typed_reads::{
    FieldScope as TransportFieldScope, ReadScope as TransportReadScope,
    record_field as record_transport_field,
};
pub use execution_value::{ExecutionValue, StoredExecutionValue, StoredMemoryValue};
pub(crate) mod fact_collections;
pub(crate) mod fact_stability;
mod fold_read_summary;
mod functions;
mod owned_footprint_reach;
mod pointer_designations;
mod population_access;
// Population authority: checked anchor lifetimes, registrations and the C
// creation ledger.
mod population_authority;
pub(crate) use population_authority::storage_creation::CheckedPopulationAuthorityExchange;
pub(crate) use population_authority::storage_creation::CheckedPopulationMemberExchange;
mod quantified_frame;
mod resource_description;
mod thread_confinement;
pub(crate) use functions::ResourceBodyClauseRecord;
pub(crate) use functions::TacticApplicationRefusal;
pub(crate) use functions::interface_join_instance_fields;
pub(crate) use functions::memory_range_is_initialized;
#[cfg(test)]
pub(crate) use functions::rewrite_resource_instance;
pub(crate) use functions::rewrite_resource_instance_selecting_children;
pub(crate) use functions::selected_instance_child_names;
pub(crate) use functions::{
    InstantiatedCompositeResourceFacts, instantiate_composite_resource_facts,
    instantiate_private_member_body_facts,
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
    CheckedLoanCallEvidenceSequence, CheckedLoanTransition, LoanViewBinding,
    concat_checked_loan_evidence, empty_checked_loan_evidence_sequence,
};
pub use loans::{
    LoanOriginKind, LoanOverlapStatus, LoanRefusalCategory, LoanRefusalDiagnostic,
    LoanRefusalOperation, LoanRefusalSubject,
};
mod byte_representation_laws;
mod integer_truncation_laws;
mod resource_conjunction;
pub(crate) use byte_representation_laws::prove_uint32_from_le_bytes;
mod separation_laws;
pub use resource_conjunction::ResourceConjunction;
pub(crate) use separation_laws::{
    observe_memory_view, prove_resource_law, prove_viewable_restrict, resource_viewable,
};
pub(crate) use separation_laws::{
    prove_separation_adjacent_ranges, prove_separation_contains_element,
    prove_separation_distinct_elements, prove_separation_elements, prove_separation_rebase,
    prove_separation_restrict, prove_separation_subrange,
};
mod loops;
pub(crate) mod machine_integer;
mod memory_provenance;
pub(crate) mod model_fields;
mod mutexes;
mod named_authority;
pub(crate) use integer_truncation_laws::{
    integer_truncation_law_requirements, prove_integer_truncation_law,
};
mod nat_integer;
pub(crate) use nat_integer::{check_nat_integer_law, is_conversion_nat_type, is_nat_integer_image};
mod object_types;
pub(crate) use object_types::is_checked_call_type_fact;
mod primitives;
#[cfg(test)]
pub(crate) use primitives::take_whole_normalization_facts;
pub(crate) mod proof;
mod publication;
pub(crate) mod sorry;
#[cfg(test)]
pub(crate) use fold_read_summary::registered_fold_read_summary;
pub use fold_read_summary::{
    CheckedFoldReadSummary, FoldReadDecline, FoldReadDefinition, register_fold_read_definition,
};
pub(crate) use fold_read_summary::{FoldFrameRefusal, frame_fold_application_transport};
pub(crate) use quantified_frame::{QuantifiedFrameRefusal, frame_quantified_transport};
pub(crate) mod reasoning;
#[cfg(test)]
pub(crate) use reasoning::variable_collection::count_cells_collected;
pub(crate) mod resource_tracker;
mod spec;
pub(crate) use spec::LOOP_ITERATIONS_VARIABLE;
pub use spec::required_constructions::is_required_construction;
pub(crate) use spec::{
    SpecCaptureRefusal, algebraic_argument_evaluation_guards, capture_spec_algebraic_value,
    capture_spec_integer_value, capture_spec_integer_value_with_guards,
    refine_object_pointer_argument_using_facts, with_preserved_integer_comparisons,
};
mod termination;
// Checked internal fork/join; binding to imported pthread declarations is a
// separate checkpoint, so no C execution path invokes these rules yet.
mod threads;

pub use api::*;
pub(crate) use assumptions::current_memory_loads_in_term;
pub(crate) use assumptions::proposition_has_free_bitvector_variable;
pub(crate) use assumptions::{
    PureFactContextIdScope, SelectedFacts, arm_frame_composite_definitions,
    capture_implicit_reasoning_provenance, collect_reasoning_provenance,
    finite_forall_goal_instances, record_implicit_reasoning_provenance,
    with_search_attempt_rollback,
};
pub(crate) use equality_graph::{
    ReadEqualityCheckpoint, ReadEqualityDelta, logical_pointer_read_term,
};
pub(crate) use eval::canonical_condition_fact;
pub(crate) use eval::canonical_form_of_load;
pub(crate) use eval::canonical_term;
pub(crate) use eval::canonicalized_offset_index_term;
#[cfg(test)]
pub(crate) use eval::count_canonical_at_creation_violations;
#[cfg(test)]
pub(crate) use eval::duplicate_read_names;
pub(crate) use eval::holds_by_read_over_write;
pub(crate) use eval::is_load_variable;
pub(crate) use eval::is_load_variable_defining_fact;
pub(crate) use eval::is_store_fact;
pub(crate) use eval::load_access_width_at_address_or_widest;
pub(crate) use eval::load_access_width_or_widest;
pub(crate) use eval::load_term_access_width;
pub(crate) use eval::load_variable_for_cell_with_origin;
pub(crate) use eval::load_variable_for_term;
pub(crate) use eval::offsets_have_same_canonical_form;
pub(crate) use eval::pointer_read_over_immediate_store;
pub(crate) use eval::proposition_mentions_load_variable;
pub(crate) use eval::proposition_mentions_scalar_read;
pub(crate) use eval::read_over_write_program_value;
pub(crate) use eval::read_over_write_value;
#[cfg(test)]
pub(crate) use eval::record_load_variable_defining_fact;
pub(crate) use eval::registered_load_bytes_for_variable;
pub(crate) use eval::registered_load_for_variable;
pub(crate) use eval::registered_load_origin_for_variable;
pub(crate) use eval::resolve_pending_heap_allocations;
pub(crate) use eval::scalar_read_observation;
pub(crate) use eval::terms_have_same_canonical_form;
pub(crate) use eval::{
    UndefinedBehaviorSite, locate_undefined_behavior, locate_undefined_behavior_in_condition,
};
pub(crate) use eval::{arithmetic_comparison_form, comparison_form};
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
pub(crate) use functions::StorageWriteOutsideFootprint;
pub(crate) use functions::arm_algebraic_payload_spelling;
pub(crate) use functions::checked_composite_projection_evidence;
pub(crate) use functions::decide_resource_model_arm;
pub(crate) use functions::establish_resource_derived_loop_frames;
pub(crate) use functions::evaluate_guarded_contract_condition_with_loop_entry;
pub(crate) use functions::guard_contract_refusal;
pub(crate) use functions::initialize_program_function_globals;
pub(crate) use functions::initialize_program_program_storage;
#[cfg(test)]
pub(crate) use functions::measure_resource_clause_attempts;
pub(crate) use functions::modified_by_value_aggregate_parameter_with_current_ensure_in_source;
pub(crate) use functions::program_type_spelling;
pub(crate) use functions::publish_instance_arms;
pub(crate) use functions::select_resource_model_arm;
pub(crate) use functions::symbolic_call_result;
pub(crate) use functions::with_static_pointer_read_cached;
pub(crate) use functions::{
    contract_entry_partition_facts, evaluate_function_resource_context_with_metadata,
    quantified_resource_requirement_assumptions, resource_clause_position_note,
    resource_clause_stall_note, unmatched_instance_body_views,
};
pub use loops::LoopBinder;
#[cfg(test)]
pub(crate) use loops::loop_state_components_match_at_back_edge;
pub(crate) use loops::memory_range_extent_refusal;
pub(crate) use loops::{
    loop_binder_state_components_match_at_back_edge, loop_binders, loop_condition_may_continue,
    loop_state_with_loop_binders_rebound, loop_structural_descent_failure,
};
// Used through other modules' glob imports of `crate::kernel`, which the unused
// import lint does not see once nothing here is `pub`.
#[allow(unused_imports)]
pub(crate) use memory_provenance::*;
pub(crate) use model_fields::algebraic_value_variable;
pub(crate) use primitives::ABSTRACT_VALUE_WIDTH;
pub(crate) use primitives::resource_context_has_symbolic_range_read;
pub use primitives::*;
pub(crate) use reasoning::memory_effect_write_pointers;
pub(crate) use reasoning::memory_resolution::{
    ClosureFactCheck, closure_memoized_fact_check, with_closure_failure_memo,
};
pub(crate) use reasoning::resolve_load_variables_from_registry;
pub(crate) use reasoning::resolve_minted_load_variables;
pub(crate) use reasoning::substitute_integer_variable_in_pure_proposition;
pub(crate) use reasoning::try_resolve_load_variables_from_registry;
pub use reasoning::{LoweringIntroduction, LoweringIntroductions};
pub(crate) use reasoning::{
    collect_bitvector_variables, collect_program_value_bitvector_variables,
    collect_spec_algebraic_expression_bitvector_variables, collect_spec_integer_bound_variables,
    collect_spec_integer_variables,
};
pub(crate) use reasoning::{
    substitute_pointer_value_in_proposition, substitute_pointer_variable_in_proposition,
};
pub(crate) use spec::is_verified_load_variable_defining_fact;
pub(crate) use spec::program_value_word32_term;
pub(crate) use termination::{
    ProgramContractBodies, ProgramContractFailure, ProgramContractGoal, ProgramContractProof,
    ProgramTerminationInputs,
};
pub use termination::{
    TerminationRefusal, TerminationVerdicts, UnsuitableCallback, program_function_callees,
    program_termination_height_plan, program_verified_function_termination_rules,
};

mod prelude {
    pub(super) use super::api::*;
    pub(super) use super::eval::*;
    pub(super) use super::functions::*;
    pub(super) use super::loops::*;
    pub(super) use super::primitives::*;
    pub(super) use super::reasoning::*;
    pub(super) use super::spec::*;
    pub(super) use super::{
        ExecutionFactSource, ExecutionFacts, ExecutionValue, StoredExecutionValue,
        StoredMemoryValue,
    };
    pub(super) use std::collections::{BTreeMap, BTreeSet};
}

/// The kernel vocabulary exposed to proposition discovery.
///
/// The planner in `src/kernel/search/proposition_search.rs` uses this
/// deliberately enumerated vocabulary: the proposition and
/// term vocabulary, the derivation records it produces, the checked context
/// operations it advances state through, and the exact queries and frozen
/// atomic checkers it calls at its leaves. Nothing here issues authority --
/// a `PropositionDerivation` is inert until `check` validates it -- and
/// explicit proof operations do not use it to enter proposition search.
pub(crate) mod planning_api {
    /// Atomic answers depend on these scoped memory-reasoning modes as well
    /// as on the selected fact context.
    pub(crate) fn atomic_derivation_modes() -> (bool, bool) {
        (
            super::api::extended_dag_bridging_active(),
            super::api::explicit_dag_check_active(),
        )
    }

    pub(crate) use super::assumptions::proposition_reasoning::forall_loadable_range_parts;
    pub(crate) use super::assumptions::{
        algebraic_constructor_field_equalities, collect_proposition_conjuncts,
        proposition_derivation, reasoning_interrupted, solve_reasoning_interrupted,
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
    /// past a session (a reusable surface verification session's states)
    /// can tell whether a later fresh session replaced the tables it names.
    static VERIFICATION_SESSION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// The generation of this thread's current kernel tables: it advances each
/// time an outermost `VerificationSession` starts fresh. Memory states and other
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
    arena: primitives::MemoryArenaState,
    loads: eval::LoadRegistryState,
    model_fields: model_fields::ModelFieldRegistryState,
    blocks: primitives::BlockRegistriesState,
    fold_reads: fold_read_summary::FoldReadSummariesState,
    conjunctions: resource_conjunction::Registry,
    required_constructions: spec::required_constructions::RequiredConstructionsState,
}

/// One verification's worth of kernel thread-local state.
///
/// The kernel keeps per-thread tables that are correct only within one
/// verification: the memory arena (state ids and their DAG derivations;
/// interning dedups by content, so a later verification's state with the
/// same content — a call havoc of a same-named callee, say — would inherit
/// the first verification's derivation and its mutable ranges), the load
/// registry (names are content-addressed, but their origins are live
/// states of the arena that minted them), and the memo tables keyed by
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
            // Structural operand identities read no registry or proof state;
            // retain them across function epochs and state restores.
            proof::signed_arithmetic::clear_shared_operand_keys();
            proof::clear_selected_atom_cache();
            proof::clear_rewritten_load_syntax_cache();
            proof::equality_rewrite::clear_shared_exact_rewrite_cache();
            primitives::clear_shared_machine_variable_cache();
            reasoning::order_reasoning::clear_fold_affine_bases();
            VERIFICATION_SESSION_GENERATION
                .with(|generation| generation.set(generation.get().wrapping_add(1)));

            resource_conjunction::clear();
            spec::required_constructions::clear_required_constructions();
            primitives::start_fresh_memory_arena();
            eval::clear_load_variable_registry();
            model_fields::clear_model_field_registry();
            primitives::clear_block_alignment_registry();
            primitives::clear_never_address_taken_locals();
            fold_read_summary::clear_fold_read_summaries();
            eval::clear_load_canonicalization_caches();
            eval::pointer_tags::clear_tag_bound_cache();
            memory_provenance::clear_canonical_form_caches();
            memory_provenance::clear_provenance_memos();
            reasoning::memory_resolution::clear_canonical_memory_cache();
            reasoning::memory_resolution::clear_memory_resolution_memos();
            assumptions::clear_assumption_memos();
            primitives::clear_integer_bridge_memo();
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
            arena: primitives::capture_memory_arena(),
            loads: eval::capture_load_variable_registry(),
            model_fields: model_fields::capture_model_field_registry(),
            blocks: primitives::capture_block_registries(),
            fold_reads: fold_read_summary::capture_fold_read_summaries(),
            conjunctions: resource_conjunction::capture(),
            required_constructions: spec::required_constructions::capture_required_constructions(),
        }
    }

    /// How many entries this thread's memory arena and load registries hold,
    /// for regressions that a reusable session's checks leave nothing behind.
    #[cfg(test)]
    pub fn state_entry_count() -> usize {
        primitives::memory_arena_entry_count()
            + eval::load_registry_entry_count()
            + resource_conjunction::len()
    }

    /// Returns this thread's tables to a captured state and drops every memo
    /// cache, so a check starts from exactly what the capture's holder built
    /// and nothing an earlier check interned, named, or memoized remains.
    ///
    /// Without this, each check on a reusable session leaves its states'
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

        resource_conjunction::restore(&state.conjunctions);
        spec::required_constructions::restore_required_constructions(&state.required_constructions);
        primitives::restore_memory_arena(&state.arena);
        eval::restore_load_variable_registry(&state.loads);
        model_fields::restore_model_field_registry(&state.model_fields);
        primitives::restore_block_registries(&state.blocks);
        fold_read_summary::restore_fold_read_summaries(&state.fold_reads);
        eval::clear_load_canonicalization_caches();
        memory_provenance::clear_canonical_form_caches();
        memory_provenance::clear_provenance_memos();
        reasoning::memory_resolution::clear_canonical_memory_cache();
        reasoning::memory_resolution::clear_memory_resolution_memos();
        assumptions::clear_assumption_memos();
        primitives::clear_integer_bridge_memo();
        api::clear_borrowed_input_root_memo();
        reasoning::variable_collection::clear_shared_memory_variables();
        functions::clear_automatic_lifetime_retirement();
        true
    }

    /// Whether this entry started the session (and so cleared the kernel's
    /// tables), as opposed to joining an enclosing one. Callers holding
    /// their own per-verification caches of kernel states clear them on
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
#[cfg(test)]
pub(crate) use execution_facts::indexed_execution_facts;
pub use execution_facts::{ExecutionFactSource, ExecutionFacts, ExecutionFactsIter};

// Search has no authority to construct proof successors.
pub(crate) mod search;

pub(crate) use spec::prepare_spec_integer_argument;
