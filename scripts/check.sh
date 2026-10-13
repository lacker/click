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

run_quality_checks() {
    cargo fmt --check
    scripts/test-setup-environment.sh
    cargo clippy --all-targets -- -D warnings
    scripts/mdbook-build.sh
    scripts/docs-lint.sh
}

# CI runs these checks alongside compilation, while the final required check
# still requires both this stage and every test shard to pass.
if [[ "${1:-}" == "--ci-quality" ]]; then
    run_quality_checks
    exit 0
fi

# The gate has a ten-minute budget, locally and in CI
# (`docs/internals/testing.md`). A test that takes more than a few seconds is
# `#[ignore = "nightly: ..."]`, an example that does is in `NIGHTLY` in
# `tests/examples.rs`, and `click audit` runs in the import tests only under
# `CLICK_NIGHTLY`. `--nightly` runs all of it with no budget.
#
# The two fixture harnesses are single tests that each verify a whole corpus
# on every core, so they run one at a time. Every other test binary holds
# ordinary tests and runs with the unit tests, in parallel.
fixture_targets=(--test mdtests --test examples)
unit_targets=(
    --lib --bin click --test documentation --test condition_transport_api
    --test compiler_import --test cpp_import --test rust_import
    --test bitcoin_core_money_range
)

if [[ "${1:-}" == "--ci-shard" ]]; then
    artifacts="${2:?usage: scripts/check.sh --ci-shard ARTIFACTS SUITE [SHARD/TOTAL]}"
    suite="${3:?usage: scripts/check.sh --ci-shard ARTIFACTS SUITE [SHARD/TOTAL]}"
    partition="${4:-1/1}"
    nextest_args=()
    needs_charon=""
    case "$suite" in
        unit)
            filter='not (binary(mdtests) | binary(examples) | binary(rust_import))'
            nextest_args=(--partition "hash:$partition")
            ;;
        rust)
            # The only tests that run Charon, and so the only shards that
            # download the pinned compiler runtime and the Charon binaries.
            filter='binary(rust_import)'
            nextest_args=(--partition "hash:$partition")
            needs_charon=1
            ;;
        mdtests)
            filter='binary(mdtests)'
            nextest_args=(--no-capture)
            export MDTEST_PARTITION="$partition"
            ;;
        examples)
            # The example-project harness takes every n-th example by
            # `EXAMPLE_PARTITION`; the binary's other tests run on the first
            # shard only.
            filter='binary(examples)'
            if [[ "$partition" != 1/* ]]; then
                filter='binary(examples) & test(=example_projects)'
            fi
            nextest_args=(--no-capture)
            export EXAMPLE_PARTITION="$partition"
            ;;
        nightly)
            # Everything the budgeted gate leaves out: ignored tests, the
            # nightly examples, audits in the import tests, and the live
            # Charon re-extraction.
            filter='all()'
            nextest_args=(--run-ignored all --no-fail-fast --profile nightly)
            export CLICK_NIGHTLY=1
            needs_charon=1
            ;;
        *) echo "error: CI suite must be unit, rust, mdtests, examples, or nightly" >&2; exit 2 ;;
    esac

    # A few expansion regressions recurse deeply enough to overflow the
    # default per-test thread stack on otherwise healthy runners.
    export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

    # All consumers reuse the exporter and Rust binaries from the build job.
    # Keep the exporter in a tar file because Actions artifacts do not retain
    # executable permissions on individual uploaded files.
    mkdir -p target/cpp-exporter
    tar -xf "$artifacts/exporter.tar" -C target/cpp-exporter
    export CLICK_CPP_EXPORTER
    CLICK_CPP_EXPORTER="$PWD/target/cpp-exporter/click-cpp-exporter"
    if [[ ! -x "$CLICK_CPP_EXPORTER" ]]; then
        echo "error: shared C++ exporter is missing at $CLICK_CPP_EXPORTER" >&2
        exit 1
    fi
    # Charon and its compiler runtime are a separate artifact under `rust/`,
    # about half of the whole build output, fetched only by the shards whose
    # tests start the Rust compiler.
    if [[ -n "$needs_charon" ]]; then
        mkdir -p target/charon/debug
        tar -xzf "$artifacts/rust/charon.tar.gz" -C target/charon/debug
        export CLICK_CHARON="$PWD/target/charon/debug/charon"
        if [[ ! -x "$CLICK_CHARON" ]]; then
            echo "error: shared Charon extractor is missing at $CLICK_CHARON" >&2
            exit 1
        fi
    fi

    # Extract at the checkout root so compile-time CARGO_BIN_EXE paths still
    # work on GitHub's identical build/test checkout paths. No Cargo build or
    # Rust toolchain is needed to run a nextest archive.
    cargo-nextest nextest run --archive-file "$artifacts/tests.tar.zst" \
        --extract-to "$PWD" --extract-overwrite \
        --filterset "$filter" "${nextest_args[@]}"
    exit 0
fi

# The live Charon re-extraction alone, for work on the Rust importer. It is
# part of `--nightly`, not of the budgeted gate.
if [[ "${1:-}" == "--charon-live" ]]; then
    export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"
    export CLICK_CHARON="${CLICK_CHARON:-$PWD/target/charon/debug/charon}"
    scripts/build-charon.sh
    cargo nextest run --test rust_import --filterset 'test(charon_)' \
        --run-ignored only --test-threads 2 --no-fail-fast --profile nightly
    exit 0
fi

# The whole-repository expansion audit: every smart tactic in the examples
# and mdtests must expand to a proof that verifies. It takes about twenty
# minutes on a release build, so it is a job of the nightly workflow and not
# part of the budgeted gate.
#
# examples/basic-cpp is left out for a different reason: its import lock and
# compilation database are generated per machine by the test harness and are
# not checked in, so a fresh checkout cannot load it. `tests/cpp_import.rs`
# audits the C++ path.
if [[ "${1:-}" == "--audit" ]]; then
    export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"
    # The C++ mdtests are audited through the pinned exporter.
    export CLICK_CPP_EXPORTER
    CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
    cargo build --release --bin click
    exec target/release/click audit --keep-going --time-limit 180m \
        --exclude examples/basic-cpp \
        .
fi

gate_started=$SECONDS
nightly=""
if [[ "${1:-}" == "--nightly" ]]; then
    shift
    nightly=1
    export CLICK_NIGHTLY=1
fi

ci_artifacts=""
nextest_args=("$@")
if [[ -n "$nightly" ]]; then
    nextest_args+=(--run-ignored all --profile nightly)
fi
if [[ "${1:-}" == "--ci-prepare" ]]; then
    ci_artifacts="${2:?usage: scripts/check.sh --ci-prepare ARTIFACTS}"
    nextest_args=()
fi

# A few expansion regressions recurse deeply enough to overflow the default
# per-test thread stack on otherwise healthy runners.
export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

if [[ -z "$ci_artifacts" ]]; then
    run_quality_checks
fi

# The C++ and Rust frontends need pinned toolchains that a C contributor may
# not have: LLVM/Clang 19.1.7 for the repository-owned C++ exporter, and
# Charon's pinned rustc for Rust import. When one is not installed, the gate
# skips the suites that need it, says so at the start and the end, and runs
# everything else. CI builds both and runs every suite; set
# CLICK_REQUIRE_FRONTENDS=1 to make a missing toolchain an error here too.
# An installed toolchain whose build fails is always an error.
if [[ -n "$ci_artifacts" ]]; then
    CLICK_REQUIRE_FRONTENDS=1
fi
skipped_frontends=()
unit_filter=()
frontend_missing() {
    local name="$1" reason="$2" suites="$3"
    if [[ -n "${CLICK_REQUIRE_FRONTENDS:-}" ]]; then
        echo "error: the $name toolchain is required (CLICK_REQUIRE_FRONTENDS is set):" >&2
        echo "$reason" >&2
        exit 1
    fi
    skipped_frontends+=("$name ($suites): $reason")
    echo "warning: skipping $suites; the $name toolchain is not installed:" >&2
    echo "$reason" >&2
}
# Removes each named `--test NAME` pair from `unit_targets`.
drop_test_targets() {
    local kept=() index=0 name dropped
    while [[ "$index" -lt "${#unit_targets[@]}" ]]; do
        if [[ "${unit_targets[$index]}" == --test ]]; then
            dropped=""
            for name in "$@"; do
                if [[ "${unit_targets[$((index + 1))]}" == "$name" ]]; then
                    dropped=1
                fi
            done
            if [[ -z "$dropped" ]]; then
                kept+=(--test "${unit_targets[$((index + 1))]}")
            fi
            index=$((index + 2))
        else
            kept+=("${unit_targets[$index]}")
            index=$((index + 1))
        fi
    done
    unit_targets=("${kept[@]}")
}

# The C++ exporter is built before the Rust tests so a broken pinned LLVM
# fails clearly. Ordinary artifact loading does not execute it; only explicit
# import refresh and its focused tests do.
if reason="$(scripts/build-cpp-exporter.sh --check 2>&1)"; then
    export CLICK_CPP_EXPORTER
    CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
else
    frontend_missing "C++" "$reason" \
        "tests/cpp_import.rs, tests/bitcoin_core_money_range.rs, C++ mdtests and examples"
    drop_test_targets cpp_import bitcoin_core_money_range
    # The `click` command tests that run a C++ mdtest through the exporter.
    unit_filter=(--filterset 'not (binary_id(clicklang::bin/click) & (
        test(=audit::tests::cpp_mdtest_audit_inventories_imported_semantics)
        | test(=expand::tests::cpp_mdtest_expansion_rechecks_the_imported_source)
        | test(=expand::tests::a_line_in_a_call_outcome_arm_selects_its_smart_tactic)
        | test(=profile::tests::cpp_mdtests_profile_the_compiler_imported_source)))')
    export CLICK_SKIP_CPP_FRONTEND=1
fi

if reason="$(scripts/build-charon.sh --check 2>&1)"; then
    export CLICK_CHARON
    CLICK_CHARON="$(scripts/build-charon.sh)"
else
    frontend_missing "Rust (Charon)" "$reason" "tests/rust_import.rs"
    drop_test_targets rust_import
fi

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

# The combined `click` binary includes each command source file in `src/bin/`
# as a module (`autobins = false` keeps Cargo from also building each as a
# standalone binary), so `--bin click` runs every command's tests once.
if [[ -n "$ci_artifacts" ]]; then
    mkdir -p "$ci_artifacts"
    cargo nextest archive "${unit_targets[@]}" "${fixture_targets[@]}" \
        --archive-file "$ci_artifacts/tests.tar.zst"
    tar -cf "$ci_artifacts/exporter.tar" \
        -C "$(dirname "$CLICK_CPP_EXPORTER")" "$(basename "$CLICK_CPP_EXPORTER")"
    mkdir -p "$ci_artifacts/rust"
    tar -czf "$ci_artifacts/rust/charon.tar.gz" \
        -C "$(dirname "$CLICK_CHARON")" "$(basename "$CLICK_CHARON")" charon-driver
    scripts/charon-runtime.sh pack "$ci_artifacts/rust/rust-runtime.tar.gz"
    exit 0
fi

cargo nextest run "${unit_targets[@]}" "${unit_filter[@]}" "${nextest_args[@]}"
# The fixture harnesses run one at a time, and each verifies its fixtures on
# every core. Their proof verdicts come from deterministic tactic-work
# budgets; nextest's outer timeout is process-level hang containment, not a
# proof budget. Their output is not captured: each fixture prints a line when
# it starts and when it finishes, so a stall is visible as it happens and
# named.
cargo nextest run "${fixture_targets[@]}" --test-threads 1 --no-capture "${nextest_args[@]}"

# Report the budget every run, so a gate that has crept past it is seen the
# day it does and not a week later.
elapsed=$((SECONDS - gate_started))
printf 'gate finished in %dm%02ds\n' $((elapsed / 60)) $((elapsed % 60))
if [[ "${#skipped_frontends[@]}" -gt 0 ]]; then
    echo "warning: this gate run was partial; CI runs the skipped suites:" >&2
    for skipped in "${skipped_frontends[@]}"; do
        echo "  skipped $skipped" >&2
    done
fi
if [[ -z "$nightly" && "$elapsed" -gt 600 ]]; then
    echo "warning: the gate took longer than its ten-minute budget; move slow tests to the nightly gate (docs/internals/testing.md)" >&2
fi
