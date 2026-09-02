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
scripts/docs-lint.sh

# The gate needs nextest: `.config/nextest.toml` holds the per-test time
# budgets, and prover regressions usually manifest as hangs, which must be
# killed and named rather than waited on. Plain `cargo test` has no such
# containment, so the gate refuses to run without nextest instead of
# silently running unbounded.
if ! command -v cargo-nextest >/dev/null 2>&1; then
    echo "error: cargo-nextest not found; the gate needs its per-test time budgets" >&2
    echo "Install it once with:" >&2
    echo "    cargo install cargo-nextest --locked" >&2
    exit 1
fi

# Unit tests may use every core.
cargo nextest run --lib --bins "$@"
# The fixture harnesses verify serially to bound peak memory. Their proof
# verdicts come from deterministic tactic-work budgets; nextest's outer
# timeout is process-level hang containment, not a proof budget. Their
# output is not captured: each fixture prints a line when it starts and when
# it finishes, so a stall is visible as it happens and named.
cargo nextest run --test mdtests --test examples --test-threads 1 --no-capture "$@"
