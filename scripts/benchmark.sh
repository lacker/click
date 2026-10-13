#!/usr/bin/env bash
# Click's key performance benchmark: nonblank `.click` lines verified per CPU
# second over a small fixed set of examples.
#
#     scripts/benchmark.sh [--work] [--runs N]
#
# The members are chosen to cover the kinds of proof Click is used for, not
# to be every example: an ordinary benchmark must not drift each time an
# example is added. `STRESS` members are measured and printed beside the
# headline but kept out of it, so one slow outlier does not become the
# number. See docs/internals/testing.md ("The key benchmark").
#
# Each member is verified with the optimized `profiling` build, `--runs`
# times (default 3); its CPU time is the fastest run's user plus system
# time, which is far less noisy than wall time, and verification is
# single-threaded. Compilation is outside the measurement.
#
# `--work` also reports deterministic work units per line, measured through
# the example harness (`CLICK_TACTIC_WORK_REPORT`). Work is the same on any
# machine, so it is the number to compare across machines; it costs a debug
# harness run of each member.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

MEMBERS=(arena rbtree-insert owned-vector)
STRESS=(rbtree-erase)

work=0
runs=3
while [[ $# -gt 0 ]]; do
    case "$1" in
        --work) work=1 ;;
        --runs)
            shift
            runs="$1"
            ;;
        *)
            echo "usage: scripts/benchmark.sh [--work] [--runs N]" >&2
            exit 2
            ;;
    esac
    shift
done

export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

echo "building optimized verifier (compilation is not measured)"
cargo build --profile profiling --bin click
verifier="${CARGO_TARGET_DIR:-$PWD/target}/profiling/click"

report=""
if [[ $work -eq 1 ]]; then
    report="$(mktemp -d "${TMPDIR:-/tmp}/click-benchmark-work.XXXXXX")"
    for member in "${MEMBERS[@]}" "${STRESS[@]}"; do
        echo "measuring deterministic work: $member"
        mkdir -p "$report/$member"
        CLICK_EXAMPLE="$member" CLICK_TACTIC_WORK_REPORT="$report/$member" \
            cargo test --test examples -- --nocapture >"$report/$member.log" 2>&1 || {
            echo "error: the example harness failed on $member; see $report/$member.log" >&2
            exit 1
        }
    done
fi

python3 - "$verifier" "$runs" "$report" "${#MEMBERS[@]}" "${MEMBERS[@]}" "${STRESS[@]}" <<'PY'
import glob, os, subprocess, sys

verifier, runs, report, member_count = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
names = sys.argv[5:]
members, stress = names[:member_count], names[member_count:]


def lines(project):
    total = 0
    for path in glob.glob(os.path.join("examples", project, "**", "*.click"), recursive=True):
        with open(path, errors="replace") as handle:
            total += sum(1 for line in handle if line.strip())
    return total


def cpu_seconds(project):
    best = None
    for _ in range(runs):
        process = subprocess.Popen(
            [verifier, "verify", os.path.join("examples", project)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        _, status, usage = os.wait4(process.pid, 0)
        if os.waitstatus_to_exitcode(status) != 0:
            sys.exit(f"error: examples/{project} did not verify; run `click verify examples/{project}`")
        seconds = usage.ru_utime + usage.ru_stime
        best = seconds if best is None else min(best, seconds)
    return best


def work_units(project):
    if not report:
        return None
    total = 0
    for path in glob.glob(os.path.join(report, project, "*.tsv")):
        with open(path) as handle:
            for row in handle:
                fields = row.rstrip("\n").split("\t")
                if len(fields) == 10 and fields[2] == "run":
                    total += int(fields[3])
    return total or None


def measure(project):
    count = lines(project)
    seconds = cpu_seconds(project)
    return project, count, seconds, work_units(project)


def row(project, count, seconds, units):
    text = f"  {project:<16} {count:>7} lines  {seconds:>8.2f} s  {count / seconds:>7.0f} lines/s"
    if units is not None:
        text += f"  {units / count:>8.0f} units/line"
    return text


measured = [measure(project) for project in members]
print(f"key benchmark: {', '.join(members)} (CPU time, fastest of {runs} runs)")
for entry in measured:
    print(row(*entry))
total_lines = sum(entry[1] for entry in measured)
total_seconds = sum(entry[2] for entry in measured)
print(f"key benchmark: {total_lines / total_seconds:.0f} lines/s ({total_lines} lines in {total_seconds:.2f} s CPU)")
if all(entry[3] is not None for entry in measured):
    total_units = sum(entry[3] for entry in measured)
    print(f"key benchmark work: {total_units / total_lines:.0f} units/line ({total_units} units)")
if stress:
    print("stress members (not in the headline):")
    for project in stress:
        print(row(*measure(project)))
PY
