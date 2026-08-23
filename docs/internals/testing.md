# Testing Click

Click uses ordinary Rust tests plus markdown integration tests.

The [verification efficiency contract](verification-efficiency.md) is part of
correctness testing. In particular, an all-simple project must scale with the
selected source and explicit proof rather than with repeatedly copied or
scanned ambient state. Wall-clock profiling locates current pain; deterministic
multi-size regressions protect the scaling law.

Use [Triaging Proof Failures](../concepts/proof-failure-triage.md) to classify a failed
proof before deciding whether it belongs in a regression test, an issue, or
ordinary proof development. This page describes how to test and contain the
tooling failures identified by that process.

## Tooling failures block feature work

Treat the verifier and its proof tools as the foundation for every language
feature and example. If verification becomes unexpectedly slow without a local
bounded failure, a smart success cannot expand into verifiable source,
`click-expand` fails or emits an unverifiable rewrite, the performance tools disagree, or a normal
diagnostic dumps enormous internal state, stop feature work. Reduce and fix the
tooling defect first. If it cannot be fixed in the same chunk, record a focused
issue with a regression plan and return the branch to a green checkpoint before
continuing.

Do not compensate by increasing a time limit, accepting eventual success,
rewriting the example into unnatural C, or adding irrelevant proof facts. Those
actions hide a foundation problem and make the next feature harder to debug.
The repository-level version of this rule is in `AGENTS.md`; issue-writing
requirements are in `issues/README.md`.

A smart tactic that promptly reports that it did not find a proof is not one of
these tooling failures. Smart search is heuristic and incomplete. Continue
with a smaller search or explicit relevant simple tactics. Reduce the engine
only if search misses its budget, produces an unusable diagnostic, reports
success without verifiable expansion, behaves unstably, or exposes a missing
simple proof operation.

Ordinary verifier errors are capped at 16 KiB of UTF-8 text. Fact and resource
lists show at most twelve entries and report how many were omitted. Engine
debugging that genuinely needs complete internal terms can opt in with
`CLICK_FULL_DIAGNOSTICS=1`; do not enable it in normal tests or user workflows.

Run the full suite with:

```sh
cargo test
```

Run the markdown proof fixtures with:

```sh
cargo test --test mdtests
```

Run the larger example-project verifier with:

```sh
cargo test --test examples
```

## Time-Bounded runs

Prover regressions usually manifest as hangs rather than failures, so the
suite has a hard per-test time budget enforced by cargo-nextest. Install it
once with `cargo install cargo-nextest --locked` (or `brew install
cargo-nextest`), then run:

```sh
cargo nextest run
```

`.config/nextest.toml` reports any test slower than 10 seconds as slow and
kills any test still running after 60 seconds. Treat a test that trips either
threshold as a bug: split it, or fix the prover slowdown it is exposing. The
mdtest and example-project harnesses are aggregate tests covering many directly
verified fixtures, so their outer test-process allowance is not a per-project
verification budget.

Plain `cargo test` does not apply nextest's outer Rust-test deadline. The
fixture harnesses deliberately have no wall-clock proof limit: deterministic
tactic-work budgets decide their verdicts. Under nextest, the aggregate mdtest
and example test processes retain a 20-minute outer timeout as crash/hang
containment. A nextest timeout is therefore a tooling failure, visibly distinct
from the verifier's deterministic-budget diagnostic, and is not evidence that
a particular proof is invalid or too expensive. On 2026-08-20 the complete
mdtest and example harnesses took 58.2 and 17.6 seconds respectively, so the
20-minute containment boundary has more than 20x headroom over the slower
aggregate gate.

Production tactics have two independent bounds, and the deterministic work
budget is the primary one: it counts cooperative prover checkpoints, so the
same source spends the same units on any machine under any load. The
real-time limits are a backstop for stretches of work the checkpoints do not
count: five seconds for simple tactics, two seconds for smart tactics, and
six seconds for control tactics. Simple correctness must not hinge on
wall-clock speed — near-threshold time enforcement made one audit pass or
fail with machine load — while smart search keeps a short cutoff because its
latency is itself the product. Exhaustion says which kind of bound fired.
Completed tactic events report both real CPU time and deterministic work, so
`click profile` can continue measuring actual user latency without making
that measurement a correctness oracle.

The default correctness budgets are 500,000 checkpoints for simple tactics
and 2,000,000 for smart and control tactics. The simple budget is calibrated
from the complete green corpus on the whole-claim-gate base (2026-08-12,
measured with budgets disabled so no cost is clipped): the example projects'
1,278 simple tactics measure p95 = 1,027 units, p99 = 6,292, max = 16,583;
the 383 mdtests' 6,137 simple tactics measure p99 = 766 with a single
148,094-unit outlier (copy3's `close_invariants`; the next largest is
20,796); and the issue-tracked hot steps sit at 35,368 and 46,242. The
budget gives the corpus maximum 3.4x margin and everything else at least
10x, and a simple tactic that grows past roughly three times today's worst
known cost fails deterministically on any machine. Recalibration must
measure both the examples and the mdtests.
Changing a work budget requires corpus measurements and a documented reason;
it is not a way to make one difficult proof pass.

### Scaling regressions

An optimization that changes a hot-path representation or algorithm should
include a generated deterministic-work regression at four or more input sizes.
Test independent dimensions rather than one realistic example: functions,
straight-line statements, facts, surface spellings, resources, theorems, and
claims. Exclude fixed parsing/startup work where practical and assert the
growth ratio, not an elapsed-time threshold.

The intended bound for simple verification is output-sensitive `N log N` or
better. A benchmark that merely stays below the production deadline can still
hide quadratic growth and is not sufficient. Conversely, explicitly emitted
paths, quantified instances, premises, and definition members count as input
or output and may be charged accordingly.

Rust library tests and both fixture gates enforce deterministic tactic-work
budgets but do not inherit production time limits. Tests specifically about
real-time interruption install explicit time limits. Fixture traversal remains
serial and fail-fast, while nextest owns the narrow process-level timeout for
an uncooperative hang. The former load-sensitive bubble-sort canary is pinned
at 100,000 deterministic units per tactic class; its measured maxima on
2026-08-20 were 146 simple, 21,090 smart, and 42,169 control units. The gates
do not rerun a successful proof to decide whether a noisy timing observation was
"confirmed": host throughput cannot change the semantic result in the first
place.

Real-time tactic accounting still uses exclusive per-thread CPU time on Unix,
so descheduling is not charged to a tactic. On platforms without a thread CPU
clock it falls back to exclusive wall-clock time. Whole-project deadlines are
always wall-clock limits. `CLICK_DISABLE_TACTIC_BUDGETS=1` remains a narrow A/B
diagnostic escape hatch; it must not be used for the ordinary correctness
gate.

The direct CLI is itself the bounding mechanism: `click verify --time-limit`
cooperatively interrupts execution, proposition derivation, memory resolution,
and resource search. Do not wrap Click in an external timeout command; a proof
search that outlives the CLI limit is a Click tooling bug.

## Quarantine

Known-broken and pathologically slow tests are quarantined so the default
suite is a meaningful green gate: any red is new signal, and nothing should
land red. Quarantine is always explicit and temporary — every entry names its
reason, and the goal is to shrink the list to zero, not to let it grow.

- Lib tests are quarantined with `#[ignore = "quarantined: ..."]` in the test
  source. Run them with `cargo test -- --ignored` or
  `cargo nextest run --run-ignored=only`.
- Mdtests are quarantined in the `QUARANTINED` list at the top of
  `tests/mdtests.rs`. Run one with `MDTEST_FILTER=<name>`, or all of them
  with `CLICK_RUN_QUARANTINED=1`.
- Example projects are quarantined in the `QUARANTINED` list at the top of
  `tests/examples.rs`. Run one with `CLICK_EXAMPLE=<name>`, or all of them
  with `CLICK_RUN_QUARANTINED=1`.

Before adding an entry, prefer fixing or reverting the offending change —
`git bisect` against a scratch worktree is cheap now that single tests are
fast to run. When a fix lands, remove the entry in the same change.

## Mdtests

Mdtests live in `mdtests/`. Each file can contain prose, one or more C blocks,
one Click block, and one expected result:

````text
```c filename=example.c
int32 example() {
    return 0;
}
```text

<!-- verified-example: mdtests/simple_tactics.md -->
```click
verifying "example.c";

int32 example() {
    ensures result == 0 by auto;
}
```text

```expect
pass
```text
````

Negative tests use an expected diagnostic substring:

```text
fail: expected diagnostic substring
```

Use mdtests for focused language, lowering, proof, and diagnostic behavior.

## Example project tests

Example projects live under `examples/`. The integration test in
`tests/examples.rs` verifies `.click` sidecars against C files in each immediate
project directory.

Use example projects for larger library-shaped fixtures. Keep them small enough
that a reader can understand the proof boundary.

### Verifying one file or project directly

`click verify` is the plain verification command the expansion workflow ends
with. It takes either a sidecar or a directory:

```sh
click verify examples/input-cursor/input_cursor.click
click verify examples/input-cursor
click verify examples
```

A bare sidecar path verifies the whole file. A `:LINE:COLUMN` suffix verifies
only the proof unit containing that one-based source location and the C
functions it calls — the same location scheme `click profile`, `click expand`,
and `click audit` use, and the targeted entry point the audit's cold
reverification runs. A directory verifies every sidecar in it: the directory
itself when it holds sidecars, otherwise each immediate subdirectory that does.
Every sidecar or selected proof unit has an independent 30-second limit. Use
`--time-limit DURATION` to override it. A timeout exits unsuccessfully and
names both the target and the active phase or tactic; one slow project cannot
consume the following projects' budgets.

That makes the expansion loop runnable end to end:

```sh
click verify path/to/file.click
click expand --in-place path/to/file.click:LINE:COLUMN
click verify path/to/file.click
```

When profiling attributes aggregate cost to a claim containing many individually
small smart tactics, expand the complete claim in one checked operation:

```sh
click expand --claim function.contract --in-place path/to/file.click
```

The first verification is a prerequisite, not merely a useful check:
expansion optimizes an already-correct selected proof unit. A failure later in
that proof blocks expansion of an earlier tactic. Repair the proof with
ordinary tactics first rather than moving between partially verified sources.
`click expand` then verifies the complete rewritten proof unit before it writes
anything. `--in-place` atomically replaces the source only on success;
`--output PATH` writes a checked sibling artifact without shell redirection.
Failures in unrelated proof units do not block this targeted workflow.

### Profiling slow proof steps

Start with `click verify`. If it reports a prompt correctness failure, repair
the proof before profiling it. Use `click profile` for optimization only after
verification succeeds. The exception is a target that times out or is
unexpectedly slow: profile it diagnostically to locate the incomplete work,
then restore successful verification before expanding anything.

Use `click profile` to find slow proof steps without letting one project run
indefinitely:

```sh
click profile examples
click profile mdtests/bubble_sort3_two_pass_sorted.md
click profile mdtests
```

Pass one sidecar, one example-project directory, the complete `examples`
directory, one markdown test, or a directory of them. Direct sidecar profiling
is useful for the sibling `.expanded.click` artifact printed by the expansion
workflow. An mdtest is profiled from its embedded
` ```c ` and ` ```click ` blocks using the same extraction the mdtests gate
uses, and reported locations point into the markdown file. Quarantine does not
apply — a quarantined mdtest is exactly the one worth profiling. The two modes
are told apart by shape: example projects win whenever a Click sidecar is found
under the directory, so their `README.md` files are not mistaken for mdtests.

The defaults report smart tactics at 2 seconds, simple tactics at
500 milliseconds, control-flow containers at 6 seconds, and stop each project
after 30 seconds. Override them with `--smart-threshold`,
`--simple-threshold`, `--control-threshold`, and `--time-limit`;
`--threshold` is shorthand for setting all three class thresholds equally.

The verifier emits each tactic's class as a structured event. The report uses
that class to prescribe the next action:

- Successful `SMART` hotspots in fully verified targets are expansion
  candidates. The report prints pasteable commands that write a sibling
  artifact, verify it, and reprofile that exact artifact with the same limits.
  A successful step observed before a later correctness failure or timeout is
  diagnostic only and produces no expansion command. Failed smart search has
  no successful proof; normally decompose the proof. An interrupted search is a
  tooling bug only when it ignores or badly overshoots its enforced bound.
- `SIMPLE` steps are deterministic checked operations. Do not expand them;
  reduce and fix the verifier bottleneck first.
- `CONTROL` steps are proof containers. Inspect their nested smart and simple
  timings rather than optimizing the container row by itself.

`have` is structurally a proof container, but the complete selectable source
occurrence inherits SMART from a supported smart body and SIMPLE from a
nonempty all-simple body. Other `have` forms remain CONTROL. Timing, inventory,
and expansion use that same source-site classification.

If a project reaches its limit, the report classifies every active step and
applies the same advice. This prevents slow compatibility checking from being
mistaken for smart search merely because it is nested inside a smart tactic.

The category sections list only steps that crossed a tail threshold. `TIME
ACCOUNTING` reconciles direct verification wall time across frontend,
environment, exclusive tactic classes, kernel certification, measured
`VERIFIER CORE` orchestration, and parent-observed `PROCESS/DRIVER` overhead.
`UNATTRIBUTED` is only the remaining inconsistent or unknown portion.

`WORK AND THROUGHPUT` counts completed simple leaves by kind, C transitions,
smart attempts and outcomes, functions, claims, and certification paths. It
reports aggregate rates and tactic averages/maxima. `DIAGNOSES` combines those
rates with the tail guards to distinguish SMART HOTSPOT, SIMPLE ENGINE BUG,
HEALTHY VOLUME, CERTIFICATION BOTTLENECK, SETUP BOTTLENECK, and UNEXPLAINED.
The displayed baselines are conservative development bounds, not a universal
hardware SLA.

A step whose timing names a tactic index the surface proof does not have keeps
its timing and loses only its location; those are listed under `STEPS WITHOUT A
SOURCE LOCATION`. Loop phases the verifier plans for itself index generated
tactics, so this is expected there.

The bounded report is intentionally a frontier rather than an exhaustive
profile beyond timed-out work. Fix simple bottlenecks before expanding one
smart location, then run the same command again. For raw function and tactic
timing, set `CLICK_TIMINGS=1`; add `CLICK_TIMING_STARTS=1` when an externally
interrupted run should identify its active statement. Raw tactic events include
`class simple`, `class smart`, or `class control`.

### Dependency-aware incremental verification

After a clean full verification, Click records a small atomic success marker
inside Git metadata for that exact commit, sidecar, and Click executable. It
records a marker only when the sidecar and its declared C sources match `HEAD`;
interrupted or dirty verification cannot attest a baseline.

Use the attested commit as a semantic comparison point:

```sh
click verify --changed-since HEAD~1 --explain examples/my-project
click verify --changed-since HEAD~1 examples/my-project
```

`--explain` is a dry run. The report lists selected functions, unchanged
functions whose baseline result is reused, and bounded reasons. Click compares
parsed C bodies, imported layouts, Click contracts, and proofs, so comments and
formatting do not invalidate results. A changed function selects its transitive
callers; the native verifier checks that set and its callees in one transaction.
Changes to shared predicates, pure functions, resources, or theorems select the
whole sidecar.

A different verifier executable (which includes its parser, kernel, proof
engine, builtins, and embedded standard library), a missing or corrupt marker,
an absent baseline source, and cache-schema drift all fall back to ordinary full
verification. The marker contains no theorem or proof object: it only attests
that the reference full gate passed. Full `click verify` remains the reference
release check.

### Expansion is not a repair operation

Expansion is deliberately not a repair operation for a broken proof. The
selected proof unit and the contracts it depends on must verify before `click
expand` will emit a rewrite. In particular, a failure later in the same proof
blocks expansion of an earlier tactic. First restore correctness with ordinary
proof steps; then profile and expand the green proof. Broken proof units must
not be moved between partially checked intermediate states under an expansion
label.

### Auditing smart-tactic expansion

Use `click audit` for a slow, exhaustive check of the source-expansion
boundary:

```sh
click audit examples
click audit mdtests
click audit .
```

The repository-root form is the complete manual expansion-boundary
gate: it covers examples and every passing mdtest in one resumable run.
Negative mdtests are excluded because their intended result is proof failure,
so they cannot supply successful expansions. The ordinary `cargo test` and
nextest gates keep fast unit, timing-parser, expansion, and markdown smoke
coverage; they do not run the exhaustive audit.

The audit first parses every proof container and builds a deterministic
inventory of smart source sites without executing any proof, printing its
size. Locations in mdtests use markdown coordinates, like `click profile` and
`click expand`:

```text
INVENTORY
  26 unique smart source sites
```

It then walks those unique `file:line:column` locations in path and source
order. A bounded verifier worker is started lazily when the cursor reaches a
sidecar or mdtest, so resuming in a later file does not initialize earlier
files. The resulting certified function environment stays alive while the
audit handles that file. Each site gets these checks:

1. **expand** — run expansion directly for that location,
   require the emitted proof container to differ from the on-disk original,
   and require it to round-trip through the ordinary Surface Click parser
   (there is no separate generated or Kernel Click grammar);
2. **verify** — verify the rewritten proof in the retained session. That
   entry point additionally requires the location to resolve to the same proof
   unit as the baseline and the Click source to be identical outside that unit;
   it then reverifies just that proof unit while reusing certified dependencies;
3. **cold original/rewritten** — on the first site of each claim, directly
   verify the original and expanded versions of the same targeted proof unit
   without the retained session. Later sites explicitly report
   `cold comparison not run`;
4. **reexpand** — check that the rewrite is an expansion fixed point. The check
   is claim-based, because the rewrite moves and replaces tactics so the site
   cannot be re-found by its original position: the audited smart tactic must be
   gone from its claim's smart inventory and the emitted expansion must not
   have introduced a new smart tactic, so the claim's smart-site multiset
   strictly shrinks. A path-aligned certificate may remove multiple symmetric
   occurrences at once.

A passing audit prints one bounded row per claim by default:

```text
CLAIM [2/25] examples/owned-vector/vector.click  vector_copy.ensures_0 (1 sites) ... ok (1 sites)
```

Repeat `--claim LABEL` to select exact named proof units. Unknown labels are an
error; labels present in multiple sidecars are rejected as ambiguous unless the
audit target is narrowed to one sidecar. `--verbose` prints all per-site phase
timings:

```text
[1/26] examples/input-cursor/input_cursor.click:8:9  incremented_zero_is_one.ensures_0 (simp) ... ok (expand 22ms, verify 29ms, cold original 37ms, cold rewritten 35ms, reexpand 23ms)
```

### Compatibility replay stack budget

Independent checking of explicit and expanded proofs currently uses the
recursive internal-proof interpreter. The complete mdtest gate, complete
non-quarantined example gate, and the `sort3` expansion canary each reached a
maximum of nine live interpreter calls in the 2026-08-20 debugger census. A
small wrapper rejects depth beyond 12 before entering the large interpreter
frame, producing an actionable proof error rather than allowing a process
stack overflow.

`ProofReplayContext` keeps its large `TacticReplayState` behind a `Box`; this
reduced the ordinary debug interpreter frame from 123,264 to 62,688 bytes.
`selected_pure_case_split_simp_expands_by_removal` runs on an explicit 1.75 MiB
thread stack, below libtest's 2 MiB default, and pins that representation
budget. The replay needs between 1216 and 1280 KiB on rustc 1.92 / macOS and
overflowed a 1.25 MiB budget on CI's Linux stable toolchain, so the budget
carries about 40% headroom over the measured need; recalibrate on the CI
platform before tightening it. The outlined proof-rule and replay adapters
keep rule-local enum and proposition payloads out of their dispatchers'
frames; they are stable stack budget boundaries, not substitutes for the
depth guard. Changes to those boundaries must keep the small-stack canary
green. The larger architectural
question of replacing the parallel mutable replay model is tracked separately
in `issues/replay-smell.md`.

### Rate-aware performance comparison

Raw site totals are informational because all verification phases naturally
grow with proof-unit size. Audit compares expanded cold verification with its
same-run original baseline. The expanded proof must be both more than twice as
slow and more than `--performance-slack` slower (default 500 ms), then repeat
that regression in a second serial comparison, to fail. The failure prints
commands that materialize and profile the exact expanded artifact.

The whole run is also bounded by `--time-limit` (default 10 minutes). Every
blocking phase is capped by the time remaining in that deadline, including
session initialization and cold verification. Reaching it stops at the current
inclusive cursor, prints one resume command, and exits unsuccessfully without
counting deadline exhaustion as a Click check failure.

### Time limits and resuming

| Option | Default | Bounds |
| --- | --- | --- |
| `--session-time-limit` | 5m | original-sidecar session initialization |
| `--expansion-time-limit` | 2m | one expansion, and the re-expansion check |
| `--verification-time-limit` | 5m | retained and cold proof-unit verification |
| `--performance-slack` | 500ms | minimum same-run regression in addition to the 2x ratio |
| `--time-limit` | 10m | the whole run's wall clock |

`--claim` and `--verbose` are selection/presentation controls and are retained
in resume commands; they do not weaken any selected site's checks.

Use `--changed-since REVISION` to audit only smart-tactic claims affected by a
Git change. It uses the same parsed C/Click comparison and reverse-call
dependency selection as incremental verification. A changed function selects
its claims and callers' claims; shared predicates, resources, pure functions,
or theorems select the whole sidecar. A missing or unparsable baseline also
selects the whole sidecar. When auditing Click's own checkout, changes to its
parser, kernel, verifier, standard library, CLI, or build inputs select the
complete audit. `--claim` intersects with this semantic selection, and both
options are retained in resume commands.

`--discovery-time-limit` remains as a compatibility alias for
`--session-time-limit`; `--slow-site-limit` is a compatibility alias for
`--performance-slack`.

By default the audit stops at the first session, expansion, verification,
fixed-point, or confirmed performance failure and prints a copy-pasteable
continuation command carrying every current limit:

```sh
click audit --session-time-limit 5m --expansion-time-limit 2m \
  --verification-time-limit 5m --performance-slack 500ms --time-limit 10m \
  --start-at path/to/file.click:LINE:COLUMN examples
```

`--start-at` is inclusive, so fixing a failure and running the suggested
command retests that same site before continuing. The cursor also skips
session initialization for preceding files. `--keep-going` requests the older
failure-collecting behavior. Use `--max-sites` only for a deliberately partial
diagnostic run; it prints the next cursor when the bound is reached. A release
or expansion-boundary audit should omit it and finish one complete pass.

Every site starts from the unchanged baseline source, so an earlier rewrite
cannot hide or cause a later failure. With `--keep-going`, a failed session is
rebuilt from a fresh complete verification before the audit continues. The command exits
unsuccessfully if session initialization, expansion, parsing, source isolation,
proof-unit verification, the fixed-point check, the confirmed relative
performance contract, or the run limit fails.

Proof scripts have no runtime semantics. Re-verifying the same isolated claim
is the semantic audit condition; requiring the automation and generated
explicit proof to visit byte-identical internal branch/path states would reject
valid expansions and is intentionally not an audit invariant.

## Unit tests

Rust unit tests are appropriate when the behavior is lower-level than a sidecar
can express clearly, such as parser details, kernel term simplification, or
specific reasoning helpers.

## Test selection

When adding a feature, prefer this order:

1. Add or update an mdtest that demonstrates the user-visible behavior.
2. Add unit tests for lower-level parser or kernel behavior if needed.
3. Add or update an example project only when the feature changes the shape of
   realistic verification.
4. Update the relevant docs.

Mdtests are the main executable documentation for Click's proof surface.
