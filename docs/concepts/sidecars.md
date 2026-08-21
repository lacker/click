# Files and sidecars

Click specs live beside C0 source files. The C file contains executable code.
The `.click` file names the C file and gives contracts for functions in it.

A tiny project might look like this:

```text
increment.c
increment.click
```

The C file contains the implementation:

<!-- verified-example: mdtests/scalar.md -->
```c
int32 increment(int32 x) {
    return x + 1;
}
```

The Click sidecar names the C file and specifies the function:

<!-- verified-example: mdtests/scalar.md -->
```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;
    ensures result == x + 1 by auto;
}
```

The function signature in the `.click` file must match the C function. The body
of the Click function is not executable C; it is the contract and proof surface
for the C function.

## The `verifying` clause

Each sidecar starts with one or more source declarations:

<!-- verified-example: mdtests/scalar.md -->
```click
verifying "file.c";
```

This tells Click which C source files are part of the verification unit. Larger
sidecars can name multiple C files when a proof depends on helper functions.

## Contracts are per function

Each function block in a sidecar describes one C function:

<!-- verified-example: mdtests/scalar.md -->
```click
int32 function_name(int32 x) {
    requires x >= 0;
    ensures result >= 0 by auto;
}
```

The `requires` clauses describe what callers must provide. The `ensures`
clauses describe what the function promises when those requirements hold.

## Where examples live

There are two kinds of example material in this repository:

- `mdtests/`: small, self-contained markdown tests. These are best for focused
  proof patterns and regression tests.
- `examples/`: larger example projects with ordinary `.c` files and `.click`
  sidecars. These are best for library-shaped verification examples.

For learning Click, follow the introductory concept pages and then read the
small mdtests listed in the examples catalog. For seeing how proofs are organized at a
larger scale, read the project fixtures under `examples/`.
