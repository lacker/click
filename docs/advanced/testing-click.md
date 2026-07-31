# Testing Click

Click uses ordinary Rust tests plus markdown integration tests.

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
each is a single test function that already bounds its own child processes.

Plain `cargo test` still works and applies no time limits; use it as the
escape hatch while fixing a slow test.

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
`tests/examples.rs` verifies `.click` sidecars against C files in each direct
child directory.

Use example projects for larger library-shaped fixtures. Keep them small enough
that a reader can understand the proof boundary.

### Verifying one sidecar directly

`click-verify` runs the same verification outside the test harnesses:

```sh
cargo run --quiet --bin click-verify -- examples/input-cursor/input_cursor.click
```

Appending a one-based `:LINE:COLUMN` suffix verifies only the proof unit
containing that source location and the C functions it calls, which is the
targeted entry point the audit's cold reverification uses.

### Profiling slow proof steps

Use `click-profile` to find slow proof steps without letting one project run
indefinitely:

```sh
cargo run --quiet --bin click-profile -- examples
```

Pass either one example-project directory or the complete `examples`
directory. The defaults report smart tactics at 2 seconds, simple tactics at
500 milliseconds, control-flow containers at 2 seconds, and stop each project
after 30 seconds. Override them with `--smart-threshold`,
`--simple-threshold`, `--control-threshold`, and `--time-limit`;
`--threshold` is shorthand for setting all three class thresholds equally.

The verifier emits each tactic's class into the timing stream. The report uses
that class to prescribe the next action:

- `SMART` steps are expansion candidates. The report prints a pasteable
  `click-expand` command for each one.
- `SIMPLE` steps are deterministic certificate replay. Do not expand them;
  reduce and fix the verifier bottleneck first.
- `CONTROL` steps are proof containers. Inspect their nested smart and simple
  timings rather than optimizing the container row by itself.

If a project reaches its limit, the report classifies every active step and
applies the same advice. This prevents a slow internal certificate replay from
being mistaken for smart search merely because it is nested inside a smart
tactic.

The bounded report is intentionally a frontier rather than an exhaustive
profile beyond timed-out work. Fix simple bottlenecks before expanding one
smart location, then run the same command again. For raw function and tactic
timing, set `CLICK_TIMINGS=1`; add `CLICK_TIMING_STARTS=1` when an externally
interrupted run should identify its active statement. Raw tactic events include
`class simple`, `class smart`, or `class control`.

### Auditing smart-tactic expansion

Use `click-audit` for a slow, exhaustive check of the source-expansion
boundary:

```sh
cargo run --quiet --bin click-audit -- examples
```

The audit first parses every sidecar and builds a deterministic inventory of
smart source sites without executing any proof, printing its size:

```text
INVENTORY
  26 unique smart source sites
```

It then walks those unique `file:line:column` locations in path and source
order. A bounded verifier worker is started lazily when the cursor reaches a
sidecar, so resuming in a later file does not initialize earlier files. The
resulting certified function environment stays alive while the audit handles
that file. Each site gets four timed checks:

1. **expand** — run expansion for that location in a bounded child process,
   require the emitted sidecar to differ from the on-disk original, and require
   it to round-trip through the ordinary Surface Click parser (there is no
   separate generated or Kernel Click grammar);
2. **verify** — verify the rewritten sidecar in the retained session. That
   entry point additionally requires the location to resolve to the same proof
   unit as the baseline and the rewritten file to be identical to the baseline
   outside that proof unit; it then drops the selected function's rule from the
   certified baseline environment and reverifies just that proof unit, reusing
   its already-certified dependencies;
3. **reverify** — reverify the same audited *proof unit* in a fresh process
   through the normal targeted entry point. This runs once per claim, not once
   per site: the retained session already established that the rewrite changed
   nothing outside the proof unit, so a whole-file pass here would redo every
   other unit for every site. Later sites of a claim already covered report
   `reverify 0ms`;
4. **reexpand** — check that the rewrite is an expansion fixed point. The check
   is claim-based, because the rewrite moves and replaces tactics so the site
   cannot be re-found by its original position: the audited smart tactic must be
   gone from its claim's smart inventory and the emitted expansion must not
   have introduced a new smart tactic, so the claim's smart-site count drops by
   exactly one.

A passing site prints its four timings:

```text
[1/26] examples/input-cursor/input_cursor.click:8:9  incremented_zero_is_one.ensures_0 (simp) ... ok (expand 22ms, verify 29ms, reverify 37ms, reexpand 23ms)
```

### Slowness is a finding

A site whose four checks together exceed `--slow-site-limit` (default 10
seconds) is reported `SLOW` and **counts as a failure**, even though every
check passed. Profile such a site with `click-profile` rather than raising the
limit.

The whole run is also bounded by `--time-limit` (default 10 minutes). Reaching
it stops the audit, prints the resume cursor, and exits unsuccessfully, so an
audit can never quietly run for an hour.

### Time limits and resuming

| Option | Default | Bounds |
| --- | --- | --- |
| `--session-time-limit` | 5m | original-sidecar session initialization |
| `--expansion-time-limit` | 2m | one expansion, and the re-expansion check |
| `--verification-time-limit` | 5m | retained-session verification, and the cold reverification |
| `--slow-site-limit` | 10s | one site's four checks together |
| `--time-limit` | 10m | the whole run's wall clock |

`--discovery-time-limit` remains as a compatibility alias for
`--session-time-limit`.

By default the audit stops at the first session, expansion, verification, or
slow-site failure and prints a copy-pasteable continuation command carrying
every current limit:

```sh
click-audit --session-time-limit 5m --expansion-time-limit 2m \
  --verification-time-limit 5m --slow-site-limit 10s --time-limit 10m \
  --start-at path/to/file.click:LINE:COLUMN examples
```

`--start-at` is inclusive, so fixing a failure and running the suggested
command retests that same site before continuing. The cursor also skips
session initialization for preceding files. `--keep-going` requests the older
failure-collecting behavior. Use `--max-sites` only for a deliberately partial
diagnostic run; it prints the next cursor when the bound is reached. A release
or certificate-boundary audit should omit it and finish one complete pass.

Every timeout child or worker is killed and reaped. Every site starts from the
unchanged baseline source, so an earlier rewrite cannot hide or cause a later
failure. With `--keep-going`, a timed-out worker is rebuilt from a fresh
complete verification before the audit continues. The command exits
unsuccessfully if session initialization, expansion, parsing, source isolation,
proof-unit verification, the fixed-point check, or the slow-site limit fails,
or if the run limit is reached.

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
