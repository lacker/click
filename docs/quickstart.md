# Quickstart

This page is for agents that need to make progress immediately.

## Run The Project

From the repository root:

```sh
cargo check
cargo test
```

The full test suite includes Rust unit tests and markdown integration tests. The
markdown tests are the best examples of end-to-end Click behavior:

```sh
cargo test --test mdtests
```

## Mdtest Format

Each `mdtests/*.md` file can contain prose, one or more C source blocks, one
Click block, and one expected-result block:

````text
```c filename=example.c
int32 example(int32* p) {
    return 0;
}
```

```click
verifying "example.c";

int32 example(int32* p) {
    ensures result == 0 by auto;
}
```

```expect
pass
```
````

Negative tests use:

```text
fail: expected diagnostic substring
```

The harness is `tests/mdtests.rs`. It runs every markdown file in `mdtests/`,
so keep examples deterministic and reasonably small.

## Minimal Proof Example

```c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1 by auto;
}
```

The `requires` clause is needed because signed overflow is undefined behavior.
Click proves C0 code only when the requirements rule out undefined behavior and
the postcondition follows on every execution path.

## Common Workflow

1. Find a nearby mdtest.
2. Copy the smallest relevant pattern.
3. Add the new behavior or failing case.
4. Run `cargo test --test mdtests`.
5. Implement parser/lowering/prover changes.
6. Run `cargo test`.
7. Update the relevant `docs/*.md` file.

## Where To Look In Source

- `src/lang/c/syntax.rs`: C0 parser and lowering.
- `src/lang/click.rs`: `.click` parser, validation, lowering, tactics, mdtest
  proof orchestration.
- `src/megakernel.rs`: C semantic terms, propositions, assumptions, symbolic
  execution, and theorem-producing axioms.
- `stdlib/prelude.click`: ordinary Click standard-library definitions.
