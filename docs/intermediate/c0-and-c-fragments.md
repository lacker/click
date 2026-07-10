# C0 And C Fragments

Click verifies C0, the repository's current C subset.

C0 is not intended to be a new production language. It is the precise target
Click can reason about today while it grows toward more realistic C.

## C0 Source

C0 source is the implementation language. It currently includes scalar integer
code, pointer code, arrays, loops, function calls, byte buffers, and a pilot
slice of struct support.

For the full list, see the C0 subset reference.

## C Fragments In Click

Click specs can contain C-like expressions:

```click
ensures result == x + 1 by auto;
ensures p[k] == old(p[k]) by auto;
requires loadable(p[0..n]);
```

These are called **C fragments**. They use C-like local syntax and typing, but
they appear inside Surface Click.

The distinction matters:

- `x + 1` follows C0 integer rules, including signed-overflow obligations.
- `p[k]` follows C0 pointer and memory rules.
- `and`, `or`, `not`, `forall`, and `exists` are Click proposition syntax, not
  C operators.

## Three Layers

Click has three layers:

- **C0**: the C-like code being verified.
- **Surface Click**: the user-written sidecar language.
- **Kernel Click**: the explicit internal proof representation.

Most users write Surface Click and C fragments. Contributors sometimes need the
Kernel Click model, especially when changing lowering, loop invariants, pure
functions, or `old(...)`.

The core representation reference explains that lower layer in detail.

## Why This Exists

The goal is to let specifications stay close to C while still having precise
logic underneath.

For example:

```click
ensures p[0] == old(p[0]) by auto;
```

is easy to read as a C programmer, but internally Click must elaborate both
memory reads into explicit memory snapshots. That translation is what lets the
kernel reason about old and current memory without treating C state as ambient.
