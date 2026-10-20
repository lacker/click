#!/usr/bin/env bash
# Temporary scoped baseline diagnostics; never included in a repair PR.
set -euo pipefail
export RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
failed=0
if [[ " $* " == *" --audit "* ]]; then
    cargo nextest run --lib --run-ignored all --no-fail-fast -E 'test(returned_struct_pointer_lemmas_survive_expansion_and_retained_verification) | test(rb_next_false_list_postconditions_fail_below_the_smart_budget)' || failed=1
    cargo nextest run --bin click --run-ignored all --no-fail-fast -E 'test(audits_an_undecided_wide_guard_after_a_recursive_call) | test(resource_proof_expansions_audit_every_site)' || failed=1
    cargo nextest run --test examples --run-ignored all --no-fail-fast -E 'test(rbtree_erase_general_explicit_closers_preserve_ownership) | test(rbtree_sized_context_rotation_retained_session_expansion_rechecks) | test(rbtree_sized_mirrored_context_rotation_retained_session_expansion_rechecks)' || failed=1
else
    cargo nextest run --test rust_import --test bitcoin_core_money_range --run-ignored all --no-fail-fast -E 'test(rust_split_at_rejects_unsupported_results_and_mutation) | test(rust_usize_arithmetic_casts_and_expansion_verify) | test(pinned_upstream_fee_frac_mul_reexports_and_verifies) | test(axiomatic_span_refused_precondition_names_model_accessors_after_execution)' || failed=1
fi
exit "$failed"
