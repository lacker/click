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
smart source sites without executing any proof. It then walks those unique
`file:line:column` locations in path and source order. A bounded verifier
worker is started lazily when the cursor reaches a sidecar, so resuming in a
later file does not initialize earlier files. The resulting certified function
environment stays alive while the audit handles that file:

1. run expansion in a bounded child process;
2. require a changed sidecar that round-trips through the ordinary Surface
   Click parser (there is no separate generated or Kernel Click grammar);
3. require the rewritten AST to differ only in the selected theorem or
   function proof;
4. remove the selected function's rule from the certified baseline
   environment; and
5. reverify that proof unit while reusing its already-certified dependencies.

Session initialization, expansion, and rewritten verification default to
limits of five minutes, two minutes, and five minutes respectively. Override
them with `--session-time-limit`, `--expansion-time-limit`, and
`--verification-time-limit`. The former `--discovery-time-limit` spelling
remains as a compatibility alias for `--session-time-limit`.

By default the audit stops at the first session, expansion, or verification
failure and prints a copy-pasteable continuation command:

```sh
click-audit --start-at path/to/file.click:LINE:COLUMN examples
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
unsuccessfully if original verification, expansion, parsing, source-isolation,
or selected-proof verification fails.

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
