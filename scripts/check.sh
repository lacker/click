#!/usr/bin/env bash
# TEMPORARY FORK VALIDATION ONLY. Not part of the pointer-assertion fix PR.
set -euo pipefail
export RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
if [[ " $* " == *" --audit "* ]]; then
    echo "Scoped pointer validation: one resource-witness expansion nightly"
    cargo nextest run --profile nightly --lib --run-ignored only -E 'test(expansion_names_a_resource_witness_through_the_checked_return_pointer)'
else
    echo "Scoped pointer validation: six existing rbtree rejection nightlies"
    cargo fmt --check
    find src/scaling_tests -name '*.rs' -print0 | xargs -0 rustfmt --edition 2024 --check
    cargo clippy --all-targets -- -D warnings
    cargo nextest run --profile nightly --test examples --run-ignored only -E 'test(rbtree_erase_color_general_flips_outer_requires_far_child_blackening) | test(rbtree_erase_color_general_flips_rotations_requires_first_grandchild_blackening) | test(rbtree_erase_color_general_flips_rotations_requires_first_grandchild_parent) | test(rbtree_erase_color_general_inner_left_requires_old_sibling_parent) | test(rbtree_erase_color_general_red_left_requires_sibling_recoloring) | test(rbtree_erase_color_general_red_left_requires_the_sibling_parent)'
fi
