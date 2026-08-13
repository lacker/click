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

if command -v cargo-nextest >/dev/null 2>&1; then
    # Applies the per-test time budgets in `.config/nextest.toml`: prover
    # regressions usually manifest as hangs, which must fail fast.
    #
    # Unit tests may use every core.
    cargo nextest run --lib --bins "$@"
    # The fixture gates enforce real-time tactic budgets, so they must not
    # compete for CPU with the unit tests or with each other: on a small
    # machine, contention rather than prover slowness would decide the result.
    # Each harness already verifies its own fixtures serially. Budgets are
    # unchanged — this only stops starvation from being measured as slowness.
    cargo nextest run --test mdtests --test examples --test-threads 1 "$@"
else
    echo "cargo-nextest not found; falling back to cargo test without the" >&2
    echo "per-test time budget. Install it with:" >&2
    echo "    cargo install cargo-nextest --locked" >&2
    cargo test "$@"
fi
