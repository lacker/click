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

For each example project, the audit first verifies the original source and
uses the verifier's timing stream to inventory every smart source site. It
then handles each unique `file:line:column` independently:

1. run expansion in a bounded child process;
2. require a changed, syntactically readable sidecar;
3. copy the original project to a fresh temporary directory;
4. install that one expanded sidecar; and
5. fully verify the rewritten project in another bounded child process.

Discovery, expansion, and rewritten verification default to limits of five
minutes, two minutes, and five minutes respectively. Override them with
`--discovery-time-limit`, `--expansion-time-limit`, and
`--verification-time-limit`. Use `--max-sites` only for a deliberately partial
diagnostic run; a release or certificate-boundary audit should omit it.

Every timeout child is killed and reaped. Sites are tested against independent
project copies, so an earlier rewrite cannot hide or cause a later failure.
The command exits unsuccessfully if original verification, expansion, parsing,
or rewritten verification fails.

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
