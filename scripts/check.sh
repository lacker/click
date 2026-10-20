#!/usr/bin/env bash
# Temporary isolated diagnostic only.
set -euo pipefail
export RUST_MIN_STACK=8388608
export CLICK_SIGNED_CERTIFICATE_DIAGNOSTIC=1
export CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
cargo build --bin click
if [[ " $* " == *" --audit "* ]]; then
    target/debug/click audit --claim fill_range.contract examples/concurrency-fork-join/fork_join.click
else
    target/debug/click audit --claim f.contract mdtests/signed_loop_certificate_keeps_its_native_type.md
fi
