#!/usr/bin/env bash
# Measures end-to-end verifier throughput over the working example projects.
#
# The verifier is built with Cargo's optimized `profiling` profile, then each
# project is verified serially. Example preparation, import preparation, and
# compilation are outside the timed interval. The reported rate is nonblank
# `.click` source lines per wall-clock second.
#
#     evals/speed-survey.sh
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Keep this aligned with `tests/examples.rs::QUARANTINED`. A benchmark should
# cover every example in the normal green gate without hiding an unexpected
# failure behind a best-effort skip.
quarantined_project="multifile-registry"

export RUST_MIN_STACK="${RUST_MIN_STACK:-8388608}"

mapfile -t projects < <(find examples -mindepth 1 -maxdepth 1 -type d -print | sort)
working_projects=()
for project in "${projects[@]}"; do
    project_name="${project##*/}"
    if [[ "$project_name" == "$quarantined_project" ]]; then
        continue
    fi
    working_projects+=("$project")
done

if [[ ${#working_projects[@]} -eq 0 ]]; then
    echo "error: no working example projects found" >&2
    exit 1
fi

click_lines="$({
    find "${working_projects[@]}" -type f -name '*.click' -print0
} | xargs -0 awk 'NF { lines++ } END { print lines + 0 }')"

echo "building optimized verifier (compilation is not timed)"
cargo build --profile profiling --bin click

verifier="$PWD/target/profiling/click"
if [[ ! -x "$verifier" ]]; then
    echo "error: optimized verifier was not built at $verifier" >&2
    exit 1
fi

export CLICK_CPP_EXPORTER
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"
while IFS= read -r -d '' prepare; do
    python3 "$prepare"
done < <(find "${working_projects[@]}" -type f -name 'prepare.py' -print0)
while IFS= read -r -d '' sidecar; do
    if [[ -f "$sidecar.import.json" ]]; then
        "$verifier" import lock "$sidecar"
    fi
done < <(find "${working_projects[@]}" -type f -name '*.click' -print0)

echo "verifying ${#working_projects[@]} example projects serially"
echo "nonblank .click lines: $click_lines"
start_ns="$(date +%s%N)"
for project in "${working_projects[@]}"; do
    "$verifier" verify "$project"
done
end_ns="$(date +%s%N)"

elapsed_ns=$((end_ns - start_ns))
if [[ $elapsed_ns -le 0 ]]; then
    echo "error: verifier elapsed time was not positive" >&2
    exit 1
fi

awk -v lines="$click_lines" -v elapsed_ns="$elapsed_ns" '
    BEGIN {
        seconds = elapsed_ns / 1000000000
        printf "elapsed: %.2fs\n", seconds
        printf "nonblank .click lines/sec: %.1f\n", lines / seconds
    }
'
