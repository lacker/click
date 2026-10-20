#!/usr/bin/env bash
# TEMPORARY FORK VALIDATION ONLY. Not part of the signed-certificate fix PR.
set -euo pipefail
export RUST_MIN_STACK=8388608
export CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
if [[ " $* " == *" --audit "* ]]; then
    echo "Scoped signed validation: historical scalar-cast fixtures and original claims"
    cargo build --bin click
    MDTEST_FILTER=integer_scalar_casts_keep_historical_values cargo nextest run --test mdtests -E 'test(mdtests)'
    MDTEST_FILTER=historical_pointer_cast_keeps_current_expression_requirement cargo nextest run --test mdtests -E 'test(mdtests)'
    target/debug/click audit --claim fill_range.contract examples/concurrency-fork-join/fork_join.click
    target/debug/click audit --claim f.contract mdtests/signed_loop_certificate_keeps_its_native_type.md
else
    echo "Scoped signed validation: all normal scaling, signed arithmetic, and expansion tests"
    cargo fmt --check
    find src/scaling_tests -name '*.rs' -print0 | xargs -0 rustfmt --edition 2024 --check
    cargo nextest run --lib -E 'test(/scaling_tests/) | test(signed_arithmetic) | test(expansion_tests) | test(signed_loop_certificate_keeps_its_native_type)'
    cargo clippy --all-targets -- -D warnings
fi
