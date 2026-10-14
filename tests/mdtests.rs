use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{
    CInput, MdTestExpectation, prepare_mdtest_inputs, read_c_inputs_for_project,
    read_click_project, read_mdtest, read_mdtest_project_if_needed, source_refs,
};
use click::instrumentation::{self, ArtifactReuseRejection, HiddenPrerequisiteRoute};
use click::surface::{
    c0_tactic_source_position, project_tactic_source_position, verify_c0_project,
    verify_c0_sources, verify_program_prepared_project,
};

#[path = "support/limits.rs"]
mod limits;
#[path = "support/tactic_work.rs"]
mod tactic_work;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
/// Set by the gate when the pinned C++ exporter is not installed.
const SKIP_CPP_FRONTEND: &str = "CLICK_SKIP_CPP_FRONTEND";
const BUBBLE_SORT3_WORK_LIMIT: usize = 100_000;
/// The explicit frame refusal takes about 175,000 units with scoped failure
/// reuse, versus 513,000 when its proof routes repeat the same questions.
const PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT: usize = 250_000;

/// Known-broken mdtests, skipped by default so the suite is a meaningful
/// green gate. Run one with `MDTEST_FILTER=<name>`, or all of them with
/// `CLICK_RUN_QUARANTINED=1`. Each entry names the reason; remove entries as
/// they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// Mdtests the ten-minute gate leaves to the nightly run
/// (`scripts/check.sh --nightly`), with the time each took in the parallel
/// gate on four cores (2026-10-13). The gate runs a fixture only if it takes
/// under half a second (`docs/internals/testing.md`). Shared `.click` lemma
/// libraries stay in the gate so it checks both sides of their imports. Run
/// one with `MDTEST_FILTER=<name>`.
const NIGHTLY: &[&str] = &[
    "a_bounded_symbolic_read_of_an_initialized_local_array_is_initialized.md", // 0.6s
    "a_frame_holds_across_a_write_at_a_64_bit_index.md",                       // 0.7s
    "a_freed_cell_is_not_read_through_another_owner_after_a_loop.md",          // 1.2s
    "a_pointer_saved_before_a_loop_is_not_read_through_the_owner_after_it.md", // 1.0s
    "a_read_back_across_a_store_that_misses_its_cell_is_the_earlier_store.md", // 0.5s
    "a_store_at_a_bounded_index_inside_an_owned_array_parameter_is_authorized.md", // 0.9s
    "a_store_below_an_owned_global_range_is_refused.md",                       // 0.6s
    "a_table_of_three_named_callback_contracts_calls_one.md",                  // 0.5s
    "a_wide_store_after_a_root_call_is_not_the_old_tag.md",                    // 0.6s
    "abutting_contract_ranges_keep_each_clause_at_certification.md",           // 0.7s
    "aggregate_static_objects.md",                                             // 0.7s
    "augment_rotate_callback.md",                                              // 3.5s
    "augment_rotate_callback_rejects_consumed_shape.md",                       // 3.1s
    "augment_rotate_callback_rejects_extra_write.md",                          // 2.9s
    "augment_rotate_model_callback_rejects_relink.md",                         // 1.8s
    "authority_certifies_observed_child_views.md",                             // 1.4s
    "authority_exact_symbolic_population_total.md",                            // 0.5s
    "authority_four_effect_exchange.md",                                       // 0.6s
    "authority_ordinary_exit_refolds_a_consumed_family.md",                    // 2.0s
    "authority_pool_checkout_helper_without_slot_rejected.md",                 // 0.6s
    "authority_pool_cleanup_field_quantity.md",                                // 0.8s
    "authority_pool_control_two_members.md",                                   // 4.0s
    "authority_pool_private_body_alias_birth.md",                              // 0.7s
    "authority_symbolic_batch_cleanup_helper.md",                              // 0.7s
    "authority_two_control_birth_helpers.md",                                  // 1.6s
    "authority_wildcard_contained_resource.md",                                // 0.8s
    "authority_wildcard_transfer_private_body.md",                             // 0.5s
    "auto_proves_a_conservation_equation.md",                                  // 2.5s
    "borrowing_composite_survives_an_owning_call.md",                          // 2.3s
    "branch_interface_keeps_model_pointer_names.md",                           // 0.8s
    "branch_interface_rejects_changed_aliased_wide_word.md",                   // 1.0s
    "branching_graph_dfs.md",                                                  // 6.2s
    "bubble_pass3_max_suffix.md",                                              // 0.9s
    "bubble_sort3_loop_permutation.md",                                        // 1.3s
    "bubble_sort3_loop_sorted.md",                                             // 0.6s
    "bubble_sort3_two_pass_sorted.md",                                         // 0.9s
    "byte_count_of_two_merged_branches_matches_the_c_count.md",                // 1.2s
    "c_chained_field_access.md",                                               // 1.1s
    "c_contract_executes_status.md",                                           // 0.6s
    "c_contract_executes_status_nested.md",                                    // 0.9s
    "c_decreases_matched_arm_child.md",                                        // 0.8s
    "c_decreases_resource_recursive_in_loop.md",                               // 0.5s
    "c_decreases_resource_recursive_in_loop_rejects_parent.md",                // 0.5s
    "c_decreases_resource_rejects_unrelated.md",                               // 0.6s
    "c_decreases_resource_tree_child.md",                                      // 1.0s
    "c_named_function_contract_accepts_symbolic_mutable_subrange.md",          // 0.6s
    "c_named_function_contract_frames_guarded_composite.md",                   // 0.8s
    "c_named_function_contract_refinement_theorem.md",                         // 0.7s
    "c_switch.md",                                                             // 0.5s
    "call_frames_pointer_after_named_unfolds.md",                              // 1.0s
    "call_frees_owned_allocation_beside_borrowed_view.md",                     // 1.0s
    "call_keeps_a_field_bearing_region_beside_the_lent_one.md",                // 1.6s
    "call_keeps_an_uncached_flat_field_beside_folded_state.md",                // 0.7s
    "call_postcondition_reads_a_two_hop_cell_inside_a_folded_view.md",         // 1.0s
    "call_refuses_a_kept_range_inside_the_allocation_it_retires.md",           // 0.5s
    "call_rejects_changed_pointer_after_named_unfolds.md",                     // 0.5s
    "call_rejects_lending_the_allocation_it_transfers.md",                     // 1.6s
    "call_retires_allocation_beside_a_view_stated_separate.md",                // 1.3s
    "call_retires_allocation_beside_unrelated_owner.md",                       // 1.2s
    "call_retires_the_allocation_it_was_lent_not_the_one_it_returns.md",       // 0.9s
    "composite_resource_owned_buffer_len_cap_data.md",                         // 2.7s
    "composite_resource_owner_buffer_hidden_separate_projection.md",           // 0.6s
    "consecutive_reallocating_calls_keep_the_returned_allocation_readable.md", // 1.9s
    "consumed_population_count_in_ensured_predicate.md",                       // 0.6s
    "contract_owns_composite_argument.md",                                     // 1.2s
    "contract_owns_through_composite_field.md",                                // 0.7s
    "copy_n_segment_invariant.md",                                             // 1.4s
    "cpp_guard_unwind_before_second.md",                                       // 1.4s
    "cpp_one_guard_unwind.md",                                                 // 1.0s
    "cpp_single_guard_throw_step.md",                                          // 1.1s
    "cpp_two_guard_unwind.md",                                                 // 1.8s
    "cstr_dynamic_indexed_read.md",                                            // 0.6s
    "cstr_strlen_through_identity_casts.md",                                   // 0.5s
    "entry_alignment_premise_expands.md",                                      // 1.4s
    "execute_order_reasoning_terminates.md",                                   // 0.7s
    "expand_sequential_null_checks.md",                                        // 1.4s
    "explicit_transport_failure_is_prompt.md",                                 // 1.5s
    "field_borrow_parent_drop.md",                                             // 0.7s
    "field_borrow_parent_drop_rejects_stale_value.md",                         // 0.7s
    "field_derived_precise_effect_after_metadata_write.md",                    // 4.4s
    "fill_tail_rejects_tail_segment_unchanged.md",                             // 1.2s
    "forall_array_segment_rejects_overwritten_cell.md",                        // 0.5s
    "fork_join_worker_direct_contract.md",                                     // 4.9s
    "global_array_resource_element_types.md",                                  // 0.5s
    "guarded_quantified_postcondition_after_loop_expands.md",                  // 0.6s
    "have_body_simp_using_names_an_arm_binding.md",                            // 0.6s
    "heap_free_matching_allocation_authority.md",                              // 0.7s
    "holder_drop_exchanges_two_separately_held_references.md",                 // 1.2s
    "initialized_aggregate_static_arrays.md",                                  // 0.8s
    "initialized_aggregate_static_objects.md",                                 // 0.7s
    "integer_sum_range_fold.md",                                               // 0.7s
    "interior_pointer_pieces_rejoin_after_an_external_call.md",                // 0.7s
    "iterated_ownership_allocate_one.md",                                      // 0.6s
    "iterated_ownership_claim_loop.md",                                        // 1.1s
    "iterated_ownership_gather_fresh_heap_map.md",                             // 0.7s
    "iterated_ownership_gather_scatter.md",                                    // 1.4s
    "iterated_ownership_release_loop.md",                                      // 1.4s
    "iterated_ownership_released_cells_feed_an_external_claim.md",             // 1.4s
    "iterated_ownership_run_scan_crosses_its_locals_ending.md",                // 1.1s
    "joined_pointer_field_read_rewrites_model_alias.md",                       // 0.7s
    "joined_pointer_field_store_rejects_overwritten_value.md",                 // 0.6s
    "joined_pointer_field_store_rewrites_model_alias.md",                      // 0.9s
    "load_variable_naming_epoch.md",                                           // 0.7s
    "loop_ascending_produces_wrong_arguments.md",                              // 0.9s
    "loop_ascending_walk_to_root.md",                                          // 1.1s
    "loop_break_exit_refold_join.md",                                          // 0.6s
    "loop_disjunctive_guard_entry_join.md",                                    // 0.5s
    "loop_entry_keeps_unfolded_state_fields_beside_its_owned_map.md",          // 0.6s
    "loop_entry_memory_capture_byte_sum.md",                                   // 1.1s
    "loop_frame_keeps_a_two_hop_map_beside_a_written_array.md",                // 1.6s
    "loop_frame_keeps_two_header_cells_of_a_field_map.md",                     // 0.8s
    "loop_frame_rejects_rewritten_base_field.md",                              // 1.9s
    "loop_invariant_through_loaded_pointer_field.md",                          // 10.1s
    "loop_invariant_through_padded_pointer_field.md",                          // 10.1s
    "loop_phase_body_reads_arm_bindings.md",                                   // 0.8s
    "loop_quantified_viewable_invariant_bounded_by_its_views_clause.md",       // 0.5s
    "loop_quantified_viewable_invariant_one_prefix_too_wide_is_refused.md",    // 1.1s
    "loop_semantically_duplicate_invariants.md",                               // 1.2s
    "loop_symbolic_disjoint_array_store_frame.md",                             // 0.6s
    "loop_three_invariant_initialization.md",                                  // 1.0s
    "mutex_population_missing_value_relation.md",                              // 0.6s
    "mutex_population_separate_body.md",                                       // 0.6s
    "named_root_call_preserves_aliased_pointer_field.md",                      // 6.8s
    "named_root_call_preserves_wide_field_read_congruence.md",                 // 1.2s
    "nested_loop_cursor_view_authority.md",                                    // 0.8s
    "normalize_using_rejects_changed_pointer_value.md",                        // 0.6s
    "opaque_call_scoped_composite_reallocation.md",                            // 1.9s
    "opaque_reallocating_call_does_not_carry_an_unstated_value.md",            // 0.8s
    "pointer_read_alias_after_loop_helper.md",                                 // 1.0s
    "pointer_read_alias_rejects_changed_field.md",                             // 0.6s
    "pointer_store_equation_follows_loaded_alias.md",                          // 0.5s
    "pointer_store_through_loaded_alias.md",                                   // 0.5s
    "population_conservation_local_mutex.md",                                  // 0.7s
    "population_consumption_at_close.md",                                      // 1.5s
    "population_initialized_cleanup.md",                                       // 0.8s
    "proof_branch_composite_old_memory_interface.md",                          // 0.6s
    "pure_click_functions.md",                                                 // 1.0s
    "qualified_static_resource.md",                                            // 0.5s
    "quantified_frame_rejects_a_recursive_call_on_the_array.md",               // 0.6s
    "rb_ascending_walk_to_root.md",                                            // 2.4s
    "rb_ascent_parent_link_guard.md",                                          // 1.1s
    "rb_augment_callbacks_const_suite.md",                                     // 1.5s
    "rb_augment_callbacks_helper.md",                                          // 0.8s
    "rb_augment_callbacks_helper_consumes_suite.md",                           // 0.8s
    "rb_augment_callbacks_helper_mutates_body.md",                             // 0.9s
    "rb_augment_callbacks_helper_mutates_body_stepwise.md",                    // 0.9s
    "rb_augment_callbacks_helper_owns.md",                                     // 1.0s
    "rb_augment_callbacks_helper_owns_cell_separate.md",                       // 1.0s
    "rb_augment_callbacks_helper_owns_without_separate.md",                    // 1.0s
    "rb_augment_callbacks_helper_rejects_changed_cell.md",                     // 0.8s
    "rb_augment_callbacks_rejects_mismatch.md",                                // 1.4s
    "rb_child_load_identity_rejects_a_wrong_color.md",                         // 1.0s
    "rb_first_last.md",                                                        // 8.0s
    "rb_first_rejects_wrong_frame_parent.md",                                  // 1.4s
    "rb_next.md",                                                              // 15.9s
    "rb_next_rejects_a_dropped_context.md",                                    // 16.2s
    "rb_parent_family.md",                                                     // 1.0s
    "rb_prev.md",                                                              // 15.5s
    "rb_prev_rejects_a_dropped_context.md",                                    // 16.5s
    "rb_produces_through_the_root_cell.md",                                    // 0.6s
    "rb_pure_null_pointer_argument.md",                                        // 0.5s
    "rb_refutes_the_unfolded_frame.md",                                        // 0.6s
    "rb_replace_node.md",                                                      // 4.0s
    "rb_replace_node_keeps_parent_link.md",                                    // 0.9s
    "rb_replace_node_with_children.md",                                        // 2.5s
    "reallocation_frees_old_cells_beside_their_owner.md",                      // 1.4s
    "resource_arm_binding_struct_base.md",                                     // 0.9s
    "resource_field_memory_endpoint.md",                                       // 0.5s
    "resource_fold_copied_packed_word.md",                                     // 0.6s
    "resource_refuted_arm_model_fact.md",                                      // 0.8s
    "resource_tree_node_init.md",                                              // 0.6s
    "resource_unfold_binds_scalar_field.md",                                   // 0.6s
    "resource_unfold_names_unmatched_body_cells.md",                           // 0.8s
    "result_parameter_false_array_postcondition.md",                           // 0.6s
    "return_fold_retains_readable_ranges_after_store.md",                      // 8.0s
    "rotation_model_preserved.md",                                             // 1.0s
    "rotation_model_rejects_swapped_order.md",                                 // 0.7s
    "search_terminates_by_unmarked_count.md",                                  // 1.2s
    "shared_child_three_parent_links_and_spare_reference.md",                  // 0.7s
    "shared_heap_detach_leak_diagnostic.md",                                   // 0.5s
    "shared_heap_detach_old_resource_handoff.md",                              // 0.8s
    "shared_heap_one_heap_parent_missing_child_ref.md",                        // 2.0s
    "shared_heap_population_certification.md",                                 // 3.8s
    "shared_heap_population_lifecycles.md",                                    // 7.2s
    "shared_heap_read_after_final_release_rejected.md",                        // 0.6s
    "shared_heap_two_parent_branch_release.md",                                // 3.8s
    "shared_heap_two_parent_caller.md",                                        // 4.0s
    "sort3_sorted.md",                                                         // 1.2s
    "static_array_parity_aggregate.md",                                        // 0.7s
    "static_array_parity_fixed_multidimensional.md",                           // 0.9s
    "static_array_parity_multidimensional.md",                                 // 0.9s
    "static_array_parity_scalar.md",                                           // 0.8s
    "static_local_arrays.md",                                                  // 0.8s
    "stdlib_every_symbol.md",                                                  // 0.9s
    "store_does_not_preserve_a_fold_over_the_range.md",                        // 0.5s
    "store_through_a_derived_pointer_cancels_the_base.md",                     // 2.8s
    "stored_pointer_identity_rejects_overwrite_after_call.md",                 // 1.0s
    "stored_pointer_identity_survives_resource_call.md",                       // 1.1s
    "struct_aggregate_resources.md",                                           // 1.9s
    "struct_conditional_value.md",                                             // 0.8s
    "struct_wide_integer_arrays.md",                                           // 0.6s
    "three_consecutive_reallocating_calls_keep_the_returned_allocation_readable.md", // 2.8s
    "transport_carries_a_kept_slot_cell_across_a_call.md",                     // 1.2s
    "two_opaque_reallocating_calls_do_not_carry_an_unstated_value.md",         // 0.6s
    "uint64_read_survives_store_and_resource_call.md",                         // 0.5s
    "unfold_region_then_write_a_descriptor_of_its_type.md",                    // 0.9s
    "wide_read_model_alias_in_separate_match_arms.md",                         // 0.8s
    "wide_read_model_arm_rejects_changed_word.md",                             // 0.7s
];

/// The artifact reuse rejection ratchet (`docs/internals/testing.md`): count
/// contract certification rejections of checked execution artifacts over the
/// whole unfiltered corpus, by reason. A count may only fall; lower its pin
/// when it does.
const ARTIFACT_REUSE_REJECTION_BASELINE: &[(ArtifactReuseRejection, usize)] = &[];

/// The hidden prerequisite ratchet (`docs/internals/testing.md`): count the
/// prerequisites simple statement checking derived by a search the proof does
/// not retain, over the whole unfiltered corpus, by route and top rule. A
/// count may only fall; `issues/simplify-step.md` drives it to zero.
const HIDDEN_PREREQUISITE_BASELINE: &[((HiddenPrerequisiteRoute, &str), usize)] = &[(
    (HiddenPrerequisiteRoute::StepObligation, "ContextualAtomic"),
    2,
)];

#[test]
fn mdtests() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mdtests_dir = manifest_dir.join("mdtests");
    let mut paths = fs::read_dir(&mdtests_dir)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", mdtests_dir.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("failed to read mdtest directory entry: {error}"))
                .path()
        })
        // Imported theorem bodies are interfaces to their importers. Run each
        // local Click library as its own entry so the gate checks those bodies.
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "md" || extension == "click")
        })
        .collect::<Vec<_>>();
    let filtered = if let Ok(filter) = std::env::var("MDTEST_FILTER") {
        paths.retain(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().contains(&filter))
        });
        true
    } else {
        false
    };
    if !filtered && std::env::var_os(RUN_QUARANTINED).is_none() {
        paths.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            let quarantine = name.and_then(|name| {
                QUARANTINED
                    .iter()
                    .find(|(quarantined, _)| *quarantined == name)
            });
            match quarantine {
                Some((name, reason)) => {
                    println!("SKIPPING quarantined mdtest `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
    }
    // A gate run leaves the slow fixtures to the nightly run.
    let skipped_nightly = !filtered && std::env::var_os("CLICK_NIGHTLY").is_none() && {
        for name in NIGHTLY {
            assert!(
                mdtests_dir.join(name).is_file(),
                "nightly mdtest `{name}` does not exist; remove it from NIGHTLY in tests/mdtests.rs"
            );
        }
        let before = paths.len();
        paths.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            !name.is_some_and(|name| NIGHTLY.contains(&name))
        });
        println!(
            "SKIPPING {} nightly mdtests (NIGHTLY in tests/mdtests.rs)",
            before - paths.len()
        );
        true
    };
    // A gate run on a machine without the pinned C++ toolchain
    // (`scripts/check.sh`) leaves out the mdtests that need its exporter.
    let skipped_cpp = std::env::var_os(SKIP_CPP_FRONTEND).is_some() && {
        let before = paths.len();
        paths.retain(|path| {
            let cpp = path.extension().is_some_and(|extension| extension == "md")
                && read_mdtest(path).is_ok_and(|mdtest| mdtest.cpp_source.is_some());
            if cpp {
                println!(
                    "SKIPPING C++ mdtest `{}`: {SKIP_CPP_FRONTEND} is set",
                    path.display()
                );
            }
            !cpp
        });
        paths.len() != before
    };
    let filtered = filtered || skipped_cpp;
    paths.sort();
    // CI splits the corpus across jobs to stay inside the gate's time
    // budget: `MDTEST_PARTITION=k/n` keeps every n-th file from the k-th,
    // over the sorted names, so the shards cover the corpus exactly once.
    let partitioned = if let Ok(partition) = std::env::var("MDTEST_PARTITION") {
        let (shard, total) = partition
            .split_once('/')
            .and_then(|(shard, total)| {
                Some((shard.parse::<usize>().ok()?, total.parse::<usize>().ok()?))
            })
            .filter(|(shard, total)| (1..=*total).contains(shard))
            .unwrap_or_else(|| {
                panic!("MDTEST_PARTITION must be `k/n` with 1 <= k <= n, got `{partition}`")
            });
        let mut index = 0;
        paths.retain(|_| {
            index += 1;
            (index - 1) % total == shard - 1
        });
        true
    } else {
        false
    };
    let filtered_by_name = filtered;
    // Without its nightly fixtures the corpus is partial, as in a partition:
    // the hidden prerequisite ratchet still catches a rise but cannot see a
    // fall, and the artifact reuse ratchet waits for a whole-corpus run.
    let partial = partitioned || skipped_nightly;
    let filtered = filtered || partial;

    assert!(
        !paths.is_empty(),
        "expected at least one mdtest in `{}`",
        mdtests_dir.display()
    );

    // Verify files on every core. Tactic correctness is enforced by
    // deterministic work budgets, not by how much CPU time happens to be
    // available to each file, so concurrency cannot change a verdict. Peak
    // memory stays small: on 2026-09-11 the whole corpus peaked at 171 MB
    // serially and 291 MB on 8 workers.
    let _ = instrumentation::take_artifact_reuse_rejection_census();
    let _ = instrumentation::take_hidden_prerequisite_census();
    let _ = instrumentation::take_backwards_memory_derivation_census();
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let failures = limits::run_parallel(&paths, workers, |path| run_mdtest_in_thread(path));
    let census = instrumentation::take_artifact_reuse_rejection_census();
    let hidden_prerequisites = instrumentation::take_hidden_prerequisite_census();
    // Which producers still end a step on a snapshot older than itself, so
    // that the step is recorded on no history. A knowledge-losing forget
    // cannot: its mark makes the result a node no earlier snapshot can be
    // (`CMemory::mark_forgotten_from`). Anything else here is a producer
    // whose steps are invisible to every history-based rule, and this line
    // is how a corpus run names it.
    eprintln!(
        "backwards memory derivations over the corpus: {:?}",
        instrumentation::take_backwards_memory_derivation_census()
    );
    if failures.is_empty() {
        if !filtered
            && std::env::var_os(RUN_QUARANTINED).is_none()
            && let Some(mismatch) = instrumentation::artifact_reuse_rejection_census_mismatch(
                &census,
                ARTIFACT_REUSE_REJECTION_BASELINE,
            )
        {
            panic!("artifact reuse rejection ratchet (tests/mdtests.rs baselines):\n{mismatch}");
        }
        if !filtered_by_name
            && std::env::var_os(RUN_QUARANTINED).is_none()
            && let Some(mismatch) = instrumentation::hidden_prerequisite_census_mismatch(
                &hidden_prerequisites,
                HIDDEN_PREREQUISITE_BASELINE,
                partial,
            )
        {
            panic!("hidden prerequisite ratchet (tests/mdtests.rs baselines):\n{mismatch}");
        }
        return;
    }

    let mut message = format!("{} of {} mdtests failed:\n", failures.len(), paths.len());
    for (index, diagnostics) in failures {
        message.push_str(&format!("\n`{}` {diagnostics}\n", paths[index].display()));
    }
    panic!("{message}");
}

fn run_mdtest_in_thread(path: &Path) -> Result<(), String> {
    let path = path.to_path_buf();
    let thread_name = path.file_stem().and_then(|name| name.to_str()).map_or_else(
        || "click-mdtest".to_string(),
        |name| format!("mdtest-{name}"),
    );
    // One line as each fixture starts and one as it finishes, on stderr so
    // the gate can stream them: a stall shows as a started fixture that
    // never finishes, and a slow fixture is visible while it runs, not only
    // in the total afterwards.
    let name = path.display().to_string();
    eprintln!("mdtest `{name}` started");
    let started = std::time::Instant::now();
    let result = limits::spawn("mdtest verifier", thread_name, move || {
        run_mdtest_attempt(&path)
    })?;
    eprintln!(
        "mdtest `{name}` {} in {:.2}s",
        if result.is_ok() { "passed" } else { "failed" },
        started.elapsed().as_secs_f64()
    );
    result
}

fn run_mdtest_attempt(path: &Path) -> Result<(), String> {
    // A calibration run measures every fixture unclipped, so the pinned
    // budgets below step aside with the defaults.
    let budgets_disabled = std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS").is_some();
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "bubble_sort3_loop_permutation.md")
    {
        // This is the former load-sensitive clock canary. Its measured
        // maxima are simple 146, smart 21,090, and control 42,169 work
        // units. Pin all three classes below 100,000 so machine load
        // cannot change the result.
        let limits = instrumentation::TacticWorkLimits {
            simple: BUBBLE_SORT3_WORK_LIMIT,
            smart: BUBBLE_SORT3_WORK_LIMIT,
            control: BUBBLE_SORT3_WORK_LIMIT,
        };
        return instrumentation::with_tactic_work_limits(limits, || run_mdtest(path));
    }
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "explicit_transport_failure_is_prompt.md")
    {
        return instrumentation::with_tactic_work_limits(
            instrumentation::TacticWorkLimits {
                simple: PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT,
                control: PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT,
                ..instrumentation::TacticWorkLimits::default()
            },
            || run_mdtest(path),
        );
    }
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "simp_false_list_position_is_prompt.md")
    {
        return instrumentation::with_tactic_work_limits(
            instrumentation::TacticWorkLimits {
                smart: 100_000,
                ..instrumentation::TacticWorkLimits::default()
            },
            || run_mdtest(path),
        );
    }
    run_mdtest(path)
}

fn run_mdtest(path: &Path) -> Result<(), String> {
    if path
        .extension()
        .is_some_and(|extension| extension == "click")
    {
        let source = fs::read_to_string(path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
        let project = read_click_project(path, &source)?;
        let inputs = read_c_inputs_for_project(path, &source, &project)?;
        return click::surface::verify_project_with_summary(&project, &inputs.program_inputs())
            .map(|_| ())
            .map_err(|error| error.report());
    }
    let mdtest = read_mdtest(path)?;
    let click_source = mdtest
        .click_source
        .as_deref()
        .ok_or_else(|| format!("`{}` is missing a ```click block", path.display()))?;
    let inputs = prepare_mdtest_inputs(&mdtest)?;
    let expectation = mdtest
        .expectation
        .as_ref()
        .ok_or_else(|| format!("`{}` is missing a ```expect block", path.display()))?;

    let project = read_mdtest_project_if_needed(path, click_source, &inputs)?;
    let verify = || -> Result<(), (String, String)> {
        match (&inputs, &project) {
            (CInput::Bundle(sources), Some(project)) => {
                verify_c0_project(project, &source_refs(sources)).map(|_| ())
            }
            (CInput::Bundle(sources), None) => {
                verify_c0_sources(click_source, &source_refs(sources)).map(|_| ())
            }
            (CInput::PreparedProgram(import), Some(project)) => {
                verify_program_prepared_project(project, import).map(|_| ())
            }
            (CInput::PreparedProgram(_), None) | (CInput::Prepared(_), _) => {
                unreachable!("every prepared mdtest input reads a Click project")
            }
        }
        .map_err(|error| (error.message().to_string(), error.report()))
    };

    let (result, samples) = tactic_work::measure(verify);
    if !samples.is_empty() {
        let line_offset = mdtest.click_start_line.saturating_sub(1);
        let relative = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .unwrap_or(path);
        tactic_work::write(
            "mdtests",
            &relative.display().to_string(),
            relative,
            &samples,
            |claim, source_index| {
                let position = match (&inputs, &project) {
                    (CInput::Bundle(sources), Some(project)) => project_tactic_source_position(
                        project,
                        &ProgramInputs::Bundle(source_refs(sources)),
                        claim,
                        source_index,
                    ),
                    (CInput::Bundle(sources), None) => c0_tactic_source_position(
                        click_source,
                        &source_refs(sources),
                        claim,
                        source_index,
                    ),
                    (CInput::PreparedProgram(import), Some(project)) => {
                        project_tactic_source_position(
                            project,
                            &ProgramInputs::program(import),
                            claim,
                            source_index,
                        )
                    }
                    _ => return None,
                };
                position
                    .ok()
                    .map(|position| (position.line + line_offset, position.column))
            },
        );
    }
    check_expectation(path, expectation, result)
}

fn check_expectation(
    path: &Path,
    expectation: &MdTestExpectation,
    result: Result<(), (String, String)>,
) -> Result<(), String> {
    match (expectation, result) {
        (MdTestExpectation::Pass, Ok(())) => Ok(()),
        (MdTestExpectation::Pass, Err((_, report))) => Err(format!(
            "`{}` expected pass, but failed: {report}",
            path.display()
        )),
        (MdTestExpectation::FailContains(expected), Ok(())) => Err(format!(
            "`{}` expected failure containing `{expected}`, but passed",
            path.display()
        )),
        (MdTestExpectation::FailContains(expected), Err((message, report))) => {
            if let Some(internal) = ["CMemory {", "CHeapMemory {", "pointer(pointer "]
                .into_iter()
                .find(|internal| report.contains(internal))
            {
                return Err(format!(
                    "`{}` leaked `{internal}` in its proof report: {report}",
                    path.display()
                ));
            }
            if message.contains(expected) {
                Ok(())
            } else {
                Err(format!(
                    "`{}` expected failure containing `{expected}`, got `{message}`",
                    path.display()
                ))
            }
        }
    }
}
