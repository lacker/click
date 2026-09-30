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

# Documentation-only changes have a focused gate. Keep this opt-in so the
# ordinary invocation remains the complete green-tree verdict.
if [[ "${1:-}" == "--docs-only" ]]; then
    shift
    exec scripts/check-docs.sh "$@"
fi

fixture_targets=(
    --test mdtests
    --test examples
    --test compiler_import
    --test cpp_import
    --test bitcoin_core_money_range
)

if [[ "${1:-}" == "--ci-shard" ]]; then
    archive="${2:?usage: scripts/check.sh --ci-shard ARCHIVE PARTITION}"
    partition="${3:?usage: scripts/check.sh --ci-shard ARCHIVE PARTITION}"

    # A few expansion regressions recurse deeply enough to overflow the
    # default per-test thread stack on otherwise healthy runners.
    export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

    # C++ import tests refresh one artifact through the repository-owned
    # exporter, so make the same backend available in every archive runner.
    export CLICK_CPP_EXPORTER
    CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"

    cargo nextest run --archive-file "$archive" --partition "$partition" --test-threads 1 --no-capture
    exit 0
fi

ci_archive=""
nextest_args=("$@")
if [[ "${1:-}" == "--ci-prepare" ]]; then
    ci_archive="${2:?usage: scripts/check.sh --ci-prepare ARCHIVE}"
    nextest_args=()
fi

# A few expansion regressions recurse deeply enough to overflow the default
# per-test thread stack on otherwise healthy runners.
export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

# Formatting is part of the gate: the same command judges locally and in CI,
# so drift cannot accumulate. Run `cargo fmt` to fix a failure.
cargo fmt --check

# The first C++ frontend is a small repository-owned LibTooling executable.
# Build it before Rust tests so the gate fails clearly when the exact pinned
# LLVM development package is unavailable. Ordinary artifact loading does not
# execute this binary; only explicit import refresh and its focused tests do.
export CLICK_CPP_EXPORTER
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"

# Lints are part of the gate for the same reason formatting is: the tree is
# clippy-clean today, so any new diagnostic is a new one and belongs to the
# change that introduced it. Deliberate exceptions are `#[allow]`s carrying a
# reason, not warnings the gate has learned to ignore.
cargo clippy --all-targets -- -D warnings

# Keep the rendered technical documentation and its source-backed public
# inventories in the same deterministic gate as the verifier. The
# `documentation` test that checks those inventories runs with the unit tests
# below, so it shares their build instead of paying for a separate one.
scripts/mdbook-build.sh
scripts/docs-lint.sh

# The gate needs nextest: `.config/nextest.toml` holds the per-test time
# budgets, and prover regressions usually manifest as hangs, which must be
# killed and named rather than waited on. Plain `cargo test` has no such
# containment, so the gate refuses to run without nextest instead of
# silently running unbounded.
if ! command -v cargo-nextest >/dev/null 2>&1; then
    echo "error: cargo-nextest not found; the gate needs its per-test time budgets" >&2
    echo "Prepare this machine with:" >&2
    echo "    scripts/setup-environment.sh" >&2
    exit 1
fi

# The combined `click` binary includes each command source file as a module.
# Cargo also discovers those source files as standalone binaries under
# `src/bin/`, so `--bins` runs their identical test bodies a second time.
# Test the shipped entry point once; clippy above still checks every target.
cargo nextest run --lib --bin click --test documentation --test condition_transport_api "${nextest_args[@]}"
# The fixture harnesses run one at a time, and each verifies its fixtures on
# every core. Their proof verdicts come from deterministic tactic-work
# budgets; nextest's outer timeout is process-level hang containment, not a
# proof budget. Their output is not captured: each fixture prints a line when
# it starts and when it finishes, so a stall is visible as it happens and
# named.
if [[ -n "$ci_archive" ]]; then
    # CI builds each fixture target once, then runs deterministic partitions
    # of the archived binaries on independent standard runners.
    cargo nextest archive "${fixture_targets[@]}" --archive-file "$ci_archive"
else
    cargo nextest run "${fixture_targets[@]}" --test-threads 1 --no-capture "${nextest_args[@]}"
fi
