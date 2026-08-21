#!/usr/bin/env bash
# The single source of truth for "is this tree green". CI runs exactly this
# script, so a local check and a CI check cannot drift apart.
#
# Judge pass/fail from this script's exit status, never from piped `cargo test`
# output. A shell pipeline reports its *last* command's status, so
# `cargo test | tail` exits 0 on a failing suite. `pipefail` below makes that
# mistake impossible inside this script.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Formatting is part of the gate: the same command judges locally and in CI,
# so drift cannot accumulate. Run `cargo fmt` to fix a failure.
cargo fmt --check

# Keep the rendered technical documentation and its source-backed public
# inventories in the same deterministic gate as the verifier.
cargo test --test documentation
scripts/mdbook-build.sh

if command -v cargo-nextest >/dev/null 2>&1; then
    # Applies the per-test time budgets in `.config/nextest.toml`: prover
    # regressions usually manifest as hangs, which must fail fast.
    #
    # Unit tests may use every core.
    cargo nextest run --lib --bins "$@"
    # The fixture harnesses verify serially to bound peak memory. Their proof
    # verdicts come from deterministic tactic-work budgets; nextest's outer
    # timeout is process-level hang containment, not a proof budget.
    cargo nextest run --test mdtests --test examples --test-threads 1 "$@"
else
    echo "cargo-nextest not found; falling back to cargo test without the" >&2
    echo "per-test time budget. Install it with:" >&2
    echo "    cargo install cargo-nextest --locked" >&2
    cargo test "$@"
fi
