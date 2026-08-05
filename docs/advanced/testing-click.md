# Testing Click

Click uses ordinary Rust tests plus markdown integration tests.

## Tooling failures block feature work

Treat the verifier and its proof tools as the foundation for every language
feature and example. If verification becomes unexpectedly slow without a local
bounded failure, a searched certificate does not replay, `click-expand` fails
or emits an unverifiable rewrite, the performance tools disagree, or a normal
diagnostic dumps enormous internal state, stop feature work. Reduce and fix the
tooling defect first. If it cannot be fixed in the same chunk, record a focused
issue with a regression plan and return the branch to a green checkpoint before
continuing.

Do not compensate by increasing a time limit, accepting eventual success,
rewriting the example into unnatural C, or adding irrelevant proof facts. Those
actions hide a foundation problem and make the next feature harder to debug.
The repository-level version of this rule is in `AGENTS.md`; issue-writing
requirements are in `issues/README.md`.

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

## Time-Bounded Runs

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
mdtest and example-project harnesses are exempted up to 20 minutes because
each is a single test function covering many directly verified fixtures.

Plain `cargo test` does not apply nextest's outer Rust-test deadline. The
fixture harnesses still report per-fixture limits from the shared event stream:
each mdtest gets 30 seconds by default (`MDTEST_TIME_LIMIT`), and each example
project gets 10 minutes (`CLICK_EXAMPLE_TIME_LIMIT`). Override those variables
while reducing a slow fixture; neither disables tactic budgets.

Tactic deadlines use exclusive per-thread CPU time on Unix, so scheduler
contention from parallel Rust tests or independent project workers is not
charged to a tactic. Whole-project deadlines remain wall-clock limits. On
platforms without a thread CPU clock, tactic enforcement falls back to
exclusive wall-clock time; parallel proof execution should remain disabled on
those platforms.

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
```

```click
verifying "example.c";

int32 example() {
    ensures result == 0 by auto;
}
```

```expect
pass
```
````

Negative tests use an expected diagnostic substring:

```text
fail: expected diagnostic substring
```

Use mdtests for focused language, lowering, proof, and diagnostic behavior.

## Example Project Tests

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
click expand --in-place path/to/file.click:LINE:COLUMN
click verify path/to/file.click
```

`click expand` verifies the selected rewritten proof unit before it writes
anything. `--in-place` atomically replaces the source only on success;
`--output PATH` writes a checked sibling artifact without shell redirection.

### Profiling slow proof steps

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
500 milliseconds, control-flow containers at 2 seconds, and stop each project
after 30 seconds. Override them with `--smart-threshold`,
`--simple-threshold`, `--control-threshold`, and `--time-limit`;
`--threshold` is shorthand for setting all three class thresholds equally.

The verifier emits each tactic's class as a structured event. The report uses
that class to prescribe the next action:

- Successful `SMART` hotspots are expansion candidates. The report prints
  pasteable commands that write a sibling artifact, verify it, and reprofile
  that exact artifact with the same limits. Failed or interrupted smart search
  has no certificate and is reported as a Click bug to reduce.
- `SIMPLE` steps are deterministic certificate replay. Do not expand them;
  reduce and fix the verifier bottleneck first.
- `CONTROL` steps are proof containers. Inspect their nested smart and simple
  timings rather than optimizing the container row by itself.

`have` is structurally a proof container, but the complete selectable source
occurrence inherits SMART from a supported smart body and SIMPLE from a
nonempty all-simple body. Other `have` forms remain CONTROL. Timing, inventory,
and expansion use that same source-site classification.

If a project reaches its limit, the report classifies every active step and
applies the same advice. This prevents a slow internal certificate replay from
being mistaken for smart search merely because it is nested inside a smart
tactic.

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

### Auditing smart-tactic expansion

Use `click audit` for a slow, exhaustive check of the source-expansion
boundary:

```sh
click audit examples
click audit mdtests
click audit .
```

The repository-root form is the complete manual release/certificate-boundary
gate: it covers examples and every passing mdtest in one resumable run.
Negative mdtests are excluded because their intended result is proof failure,
so they cannot supply accepted certificates. The ordinary `cargo test` and
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

A passing site prints all phase timings:

```text
[1/26] examples/input-cursor/input_cursor.click:8:9  incremented_zero_is_one.ensures_0 (simp) ... ok (expand 22ms, verify 29ms, cold original 37ms, cold rewritten 35ms, reexpand 23ms)
```

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
or certificate-boundary audit should omit it and finish one complete pass.

Every site starts from the unchanged baseline source, so an earlier rewrite
cannot hide or cause a later failure. With `--keep-going`, a failed session is
rebuilt from a fresh complete verification before the audit continues. The command exits
unsuccessfully if session initialization, expansion, parsing, source isolation,
proof-unit verification, the fixed-point check, the confirmed relative
performance contract, or the run limit fails.

Proof scripts have no runtime semantics. Re-verifying the same isolated claim
is the semantic audit condition; requiring the automation and explicit
certificate to visit byte-identical internal branch/path states would reject
valid expansions and is intentionally not an audit invariant.

## Unit Tests

Rust unit tests are appropriate when the behavior is lower-level than a sidecar
can express clearly, such as parser details, kernel term simplification, or
specific reasoning helpers.

## Test Selection

When adding a feature, prefer this order:

1. Add or update an mdtest that demonstrates the user-visible behavior.
2. Add unit tests for lower-level parser or kernel behavior if needed.
3. Add or update an example project only when the feature changes the shape of
   realistic verification.
4. Update the relevant docs.

Mdtests are the main executable documentation for Click's proof surface.
