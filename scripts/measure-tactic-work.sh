#!/usr/bin/env bash
# Measures the deterministic work every tactic in the example and mdtest
# corpus charges, with budgets disabled so no cost is clipped, and prints the
# per-class statistics that `TacticWorkLimits::default` is calibrated from.
#
#     scripts/measure-tactic-work.sh [REPORT_DIR]
#
# The fixture harnesses record work in-process (`collect_tactic_work`) and
# write one tab-separated file per fixture into REPORT_DIR (default: a fresh
# directory under target/). This script only runs the harnesses and
# aggregates those files; it is a measurement, not the gate. With budgets
# disabled a fixture that expects a budget failure fails its expectation;
# the harness names it, and its tactics are still measured.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

report="${1:-target/tactic-work/$(date +%Y%m%dT%H%M%S)}"
rm -rf "$report"
mkdir -p "$report"
report="$(cd "$report" && pwd)"

export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"
if ! command -v cargo-nextest >/dev/null 2>&1; then
    echo "error: cargo-nextest not found; install it with: cargo install cargo-nextest --locked" >&2
    exit 1
fi

# The C++ example needs the repository-owned exporter, as in the gate.
export CLICK_CPP_EXPORTER
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"

status=0
CLICK_DISABLE_TACTIC_BUDGETS=1 CLICK_TACTIC_WORK_REPORT="$report" \
    cargo nextest run --test mdtests --test examples --test-threads 1 --no-capture --no-fail-fast \
    >"$report/harness.log" 2>&1 || status=$?
if [[ $status -ne 0 ]]; then
    echo "note: the harnesses exited $status with budgets disabled; failing fixtures:" >&2
    grep -E "^mdtest \`[^\`]*\` failed in|^example project \`[^\`]*\` sidecar" "$report/harness.log" >&2 || true
    echo "full harness output: $report/harness.log" >&2
fi

python3 - "$report" <<'PY'
import glob, math, os, sys

report = sys.argv[1]
rows = []
fixtures = {"examples": set(), "mdtests": set()}
for path in sorted(glob.glob(os.path.join(report, "*.tsv"))):
    with open(path) as handle:
        for line in handle:
            fields = line.rstrip("\n").split("\t")
            if len(fields) != 10:
                continue
            harness, fixture, cls, work, outcome, name, claim, stmt, src, loc = fields
            fixtures.setdefault(harness, set()).add(fixture)
            rows.append(dict(harness=harness, fixture=fixture, cls=cls, work=int(work),
                             outcome=outcome, name=name, claim=claim, stmt=stmt,
                             src=src, loc=loc))

def rank(sorted_values, q):
    # Nearest-rank percentile.
    index = max(0, math.ceil(q * len(sorted_values)) - 1)
    return sorted_values[index]

print(f"tactic work report: {report}")
print("corpus: " + ", ".join(
    f"{len(fixtures.get(h, ()))} {h} fixtures" for h in ("examples", "mdtests")))
for scope in ("examples", "mdtests", "all"):
    print(f"\n== {scope} ==")
    print(f"{'class':8} {'count':>7} {'p50':>9} {'p95':>9} {'p99':>9} {'second':>10} {'max':>10}")
    for cls in ("simple", "smart", "control"):
        values = sorted(r["work"] for r in rows
                        if r["cls"] == cls and (scope == "all" or r["harness"] == scope))
        if not values:
            print(f"{cls:8} {0:>7}")
            continue
        second = values[-2] if len(values) > 1 else 0
        print(f"{cls:8} {len(values):>7} {rank(values, .50):>9} {rank(values, .95):>9} "
              f"{rank(values, .99):>9} {second:>10} {values[-1]:>10}")

for cls in ("simple", "smart", "control"):
    top = sorted((r for r in rows if r["cls"] == cls), key=lambda r: -r["work"])[:10]
    print(f"\n== top {len(top)} {cls} tactics by work ==")
    for r in top:
        failed = " (failed)" if r["outcome"] == "failed" else ""
        print(f"{r['work']:>10}  {r['name']}{failed}  {r['loc']}  "
              f"[{r['claim']}, statement {r['stmt']}, source tactic {r['src']}]")
PY
exit 0
