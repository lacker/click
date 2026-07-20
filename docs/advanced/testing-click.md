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

Use `click-profile` to find proof steps slower than a threshold without letting
one project run indefinitely:

```sh
cargo run --quiet --bin click-profile -- \
  --threshold 1s --time-limit 25s examples
```

Pass either one example-project directory or the complete `examples`
directory. The time limit applies separately to each project. Completed slow
steps are sorted by duration. If a project reaches its limit, the report names
the active function, tactic, and zero-based source-statement index, so the next
profiling run can advance after that local bottleneck is fixed.

The bounded report is intentionally a frontier rather than an exhaustive
profile beyond timed-out work. Fix or expand the first slow statements and run
the same command again. For raw function and tactic timing, set
`CLICK_TIMINGS=1`; add `CLICK_TIMING_STARTS=1` when an externally interrupted
run should identify its active statement.

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
