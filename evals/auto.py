#!/usr/bin/env python3
"""How much of the examples' hand-written `have` statements `auto` covers.

    evals/auto.py [--jobs N] [--per-file N] [--only SUBSTRING]
                  [--out results.jsonl] [--write-baseline]

The corpus is every `.click` sidecar of the projects listed in
`evals/auto/corpus.txt`. A site is a `have P ...;` statement whose `have` line
holds the whole proposition: a one-line `have` or one with a `by { ... }`
block. Each site is measured twice, in a scratch copy of the project:

- deletable: with the whole statement deleted, the proof unit that contained
  it still verifies. The proof's own automation (`auto` at the claims,
  `simp`, the steps after it) finds the fact, and no later step names it.
- by auto: with its justification replaced by `by auto;`, the proof unit
  still verifies. `auto` proves the fact where it is stated, whether or not
  later steps cite it.

`click verify FILE:LINE:COLUMN` checks only the proof unit that contains the
site. The verdict is the exit status. For a failure, the first line naming a
reason is kept as a label for reading, never as the verdict.

Each file contributes at most `--per-file` sites (default 20), chosen with a
fixed seed so the sample is the same on every run. Results are compared with
`evals/auto/baseline.json`; `--write-baseline` replaces it. A file whose
unmodified sidecar does not verify is reported and skipped.

Uses the optimized verifier at `$CARGO_TARGET_DIR/profiling/click` (built here
unless `CLICK` names another binary). Sites run in parallel; verdicts do not
depend on load, because every tactic budget is deterministic work, and the
time limit is only crash containment.
"""

import argparse
import concurrent.futures
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
EVAL_DIR = os.path.join(ROOT, "evals", "auto")
CORPUS = os.path.join(EVAL_DIR, "corpus.txt")
BASELINE = os.path.join(EVAL_DIR, "baseline.json")
SITE_TIME_LIMIT = "5m"
# The unmodified sidecar is verified whole, and the largest take minutes.
FILE_TIME_LIMIT = "30m"
HAVE = re.compile(r"^(\s*)have (.+?)( by \{| by [a-z_]+(\(.*\))?;\s*$|;\s*$)")
# Each measure and the field holding its failure label.
MEASURES = [("deletable", "reason"), ("by_auto", "auto_reason")]
REASONS = [
    ("budget", "exhausted"),
    ("timeout", "time limit"),
    ("syntax", "syntax error"),
]


def verifier():
    if os.environ.get("CLICK"):
        return os.environ["CLICK"]
    target = os.environ.get("CARGO_TARGET_DIR", os.path.join(ROOT, "target"))
    subprocess.run(
        ["cargo", "build", "--profile", "profiling", "--bin", "click"], cwd=ROOT, check=True
    )
    return os.path.join(target, "profiling", "click")


def corpus_projects():
    projects = []
    with open(CORPUS) as corpus:
        for line in corpus:
            line = line.split("#", 1)[0].strip()
            if line:
                projects.append(line)
    return projects


def proof_end(text, open_brace):
    """The index just past the `}` matching `text[open_brace]`, skipping
    `#` comments."""
    depth = 0
    index = open_brace
    while index < len(text):
        character = text[index]
        if character == "#":
            newline = text.find("\n", index)
            index = len(text) if newline < 0 else newline
            continue
        if character == "{":
            depth += 1
        elif character == "}":
            depth -= 1
            if depth == 0:
                return index + 1
        index += 1
    return None


def sites(path):
    """Each `have` statement whose proposition is on the `have` line and has
    no braces of its own, as (line, column, proposition, start, end), where
    `text[start:end]` is the whole statement with its line ending."""
    with open(path) as source:
        text = source.read()
    found = []
    offset = 0
    for number, line in enumerate(text.split("\n"), start=1):
        match = HAVE.match(line)
        proposition = match.group(2) if match else ""
        if match and "{" not in proposition and "}" not in proposition:
            if match.group(3) == " by {":
                end = proof_end(text, offset + match.end() - 1)
            else:
                end = offset + len(line)
            if end is not None:
                newline = text.find("\n", end)
                end = len(text) if newline < 0 else newline + 1
                found.append((number, len(match.group(1)) + 1, proposition, offset, end))
        offset += len(line) + 1
    return text, found


def site_key(relative, proposition, occurrence):
    """A key that survives edits elsewhere in the file: the file, the written
    proposition, and which occurrence of it this is."""
    return f"{relative}::{proposition}::{occurrence}"


def label(output):
    for line in output.splitlines():
        lowered = line.lower()
        for reason, needle in REASONS:
            if needle in lowered:
                return reason
    return "failed"


def run_unit(click, path, line, column):
    start = time.monotonic()
    completed = subprocess.run(
        [click, "verify", "--time-limit", SITE_TIME_LIMIT, f"{path}:{line}:{column}"],
        capture_output=True,
        text=True,
    )
    elapsed = time.monotonic() - start
    return completed.returncode, completed.stdout + completed.stderr, elapsed


def verdict(click, path, edited, line):
    """Writes `edited` to `path` and verifies the proof unit holding `line`,
    counted from 1 and given as the line just above the edited statement,
    which is still inside its proof unit after the edit."""
    with open(path, "w") as source:
        source.write(edited)
    above = edited.split("\n")[line - 1]
    column = len(above) - len(above.lstrip()) + 1
    status, output, elapsed = run_unit(click, path, line, column)
    return status == 0, None if status == 0 else label(output), elapsed


def evaluate_file(click, project, relative, chosen):
    """Verifies `relative` unmodified, then with each chosen site deleted
    and with each proved by `auto`, in a private copy of the examples."""
    results = []
    with tempfile.TemporaryDirectory(prefix="click-auto-eval-") as scratch:
        # Copy every example, not only this project: a sidecar may import
        # another project's declarations by a relative path.
        shutil.copytree(os.path.join(ROOT, "examples"), os.path.join(scratch, "examples"))
        path = os.path.join(scratch, relative)
        text, _ = sites(path)
        completed = subprocess.run(
            [click, "verify", "--time-limit", FILE_TIME_LIMIT, path],
            capture_output=True,
            text=True,
        )
        if completed.returncode != 0:
            return [{"file": relative, "skipped": "unmodified sidecar does not verify"}]
        for key, (line, column, proposition, by, end) in chosen:
            # After a deletion the statement's own line may be the unit's
            # last brace, so both edits target the line above it.
            deletable, reason, deleted_seconds = verdict(
                click, path, text[:by] + text[end:], line - 1
            )
            indent = " " * (column - 1)
            by_auto, auto_reason, auto_seconds = verdict(
                click,
                path,
                text[:by] + f"{indent}have {proposition} by auto;\n" + text[end:],
                line - 1,
            )
            results.append(
                {
                    "key": key,
                    "file": relative,
                    "line": line,
                    "proposition": proposition,
                    "deletable": deletable,
                    "reason": reason,
                    "by_auto": by_auto,
                    "auto_reason": auto_reason,
                    "seconds": round(deleted_seconds + auto_seconds, 2),
                }
            )
        with open(path, "w") as source:
            source.write(text)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    parser.add_argument("--per-file", type=int, default=20)
    parser.add_argument("--only", help="evaluate only files whose path contains this")
    parser.add_argument("--out", help="write one JSON line per site here")
    parser.add_argument("--write-baseline", action="store_true")
    arguments = parser.parse_args()

    click = verifier()
    work = []
    for project in corpus_projects():
        for directory, _, files in os.walk(os.path.join(ROOT, project)):
            for name in sorted(files):
                if not name.endswith(".click"):
                    continue
                relative = os.path.relpath(os.path.join(directory, name), ROOT)
                if arguments.only and arguments.only not in relative:
                    continue
                _, found = sites(os.path.join(ROOT, relative))
                seen = {}
                keyed = []
                for site in found:
                    occurrence = seen.get(site[2], 0)
                    seen[site[2]] = occurrence + 1
                    keyed.append((site_key(relative, site[2], occurrence), site))
                chosen = random.Random(relative).sample(
                    keyed, min(arguments.per_file, len(keyed))
                )
                chosen.sort(key=lambda item: item[1][0])
                if chosen:
                    work.append((project, relative, chosen))

    started = time.monotonic()
    results = []
    with concurrent.futures.ThreadPoolExecutor(arguments.jobs) as pool:
        futures = [
            pool.submit(evaluate_file, click, project, relative, chosen)
            for project, relative, chosen in work
        ]
        for future in concurrent.futures.as_completed(futures):
            results.extend(future.result())
    elapsed = time.monotonic() - started

    skipped = [result for result in results if "skipped" in result]
    measured = sorted(
        (result for result in results if "skipped" not in result), key=lambda r: r["key"]
    )
    times = sorted(result["seconds"] for result in measured)
    files = len({result["file"] for result in measured})
    print(f"auto eval: {files} files, {len(measured)} sites, {elapsed / 60:.0f}m")
    for measure, reason_field in MEASURES:
        held = [result for result in measured if result[measure]]
        reasons = {}
        for result in measured:
            if not result[measure]:
                reasons[result[reason_field]] = reasons.get(result[reason_field], 0) + 1
        share = 100 * len(held) / len(measured) if measured else 0
        print(f"{measure:<10} {len(held):5} / {len(measured)}  {share:.1f}%")
        for reason, count in sorted(reasons.items(), key=lambda item: -item[1]):
            print(f"  {reason:<12} {count}")
    if measured:
        print(
            f"seconds per site  median {times[len(times) // 2]:.1f}, "
            f"p95 {times[min(len(times) - 1, len(times) * 95 // 100)]:.1f}"
        )
    for result in skipped:
        print(f"skipped  {result['file']}: {result['skipped']}")

    current = {
        result["key"]: {measure: result[measure] for measure, _ in MEASURES}
        for result in measured
    }
    if os.path.exists(BASELINE):
        with open(BASELINE) as source:
            baseline = json.load(source)
        new = sorted(key for key in current if key not in baseline)
        print(f"vs baseline  {len(new)} new sites")
        for measure, _ in MEASURES:
            was = {
                key: entry.get(measure) for key, entry in baseline.items()
            }
            gained = sorted(
                key for key, entry in current.items() if entry[measure] and was.get(key) is False
            )
            lost = sorted(
                key for key, entry in current.items() if not entry[measure] and was.get(key) is True
            )
            print(f"  {measure:<10} +{len(gained)} gained, -{len(lost)} lost")
            for key in lost:
                print(f"    lost   {key}")
            for key in gained:
                print(f"    gained {key}")
    if arguments.write_baseline:
        with open(BASELINE, "w") as target:
            json.dump(current, target, indent=1, sort_keys=True)
            target.write("\n")
        print(f"wrote {os.path.relpath(BASELINE, ROOT)}")
    if arguments.out:
        with open(arguments.out, "w") as target:
            for result in measured:
                target.write(json.dumps(result) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
