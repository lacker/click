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
