#!/usr/bin/env bash
# Records a wall-clock sampling profile of `click verify` on the given targets
# with samply, in an optimized build that keeps symbols, and opens it in the
# Firefox Profiler.
#
# This complements `click profile`, which attributes time and deterministic
# work to proof steps and kernel operations. Use samply when the question is
# where the verifier itself spends wall-clock time: which functions, not
# which tactics.
#
#     scripts/profile-samply.sh examples/binary-tree
#     scripts/profile-samply.sh mdtests/bubble_sort3_two_pass_sorted.md
#
# Pass `--save-only` first to write `target/profiling/click.samply.json`
# instead of opening the viewer. Install samply once with
# `cargo install samply --locked`.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

if ! command -v samply >/dev/null 2>&1; then
    echo "error: samply not found; install it once with: cargo install samply --locked" >&2
    exit 1
fi
if [[ $# -eq 0 ]]; then
    echo "usage: scripts/profile-samply.sh [--save-only] <verify target>..." >&2
    exit 1
fi

save_only=()
if [[ "$1" == "--save-only" ]]; then
    save_only=(--save-only --output target/profiling/click.samply.json)
    shift
fi

cargo build --profile profiling --bin click
exec samply record "${save_only[@]}" target/profiling/click verify "$@"
