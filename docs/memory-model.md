# Memory Model

The memory model is central to Click. Many proof failures are aliasing or frame
failures, not arithmetic failures.

## Blocks And Pointers

Kernel memory is a map of named byte-sized blocks plus known cells. A
pointer is a semantic object:

```text
Pointer { block, offset }
```

The pointer block carries provenance. Pointer offsets are separate terms, not
raw integers. C0 pointer arithmetic is scaled by the pointee type: `int32*`
adds four bytes per element, while `uint8*` adds one byte per element.

## Argument Memory And Aliasing

Function pointer parameters are modeled as symbolic offsets into one shared
external argument-memory block. Distinct pointer parameter names do not imply
non-aliasing.

If a proof relies on non-overlap, state it:

```click
requires disjoint(dst[0..n], src[0..n]);
```

This is intentionally C-like. C functions can be called with aliased pointers
unless their contract rules that out.

## Valid Ranges

Use `valid_range` to prove memory safety:

```click
requires valid_range(p, 12);
requires valid_range(p[0..3]);
requires valid_range(p[0..n]);
requires valid_range((p + 1)[0..n - 1]);
```

Segment forms are half-open `int32` element ranges. For `int32 p[]`,
`valid_range(p[0..n])` means cells `p[0]` through `p[n - 1]` are available for
four-byte `int32` access. For `uint8 p[]`, the same spelling covers `n`
one-byte elements.

Symbolic memory access usually needs:

- a valid range
- lower and upper index bounds
- loop invariants if the bounds are established by a loop

## Old Memory

`old(expression)` evaluates in the function-entry state:

```click
ensures p[0] == old(p[0]) by auto;
```

For quantified old-memory postconditions:

```click
ensures forall (int32 k) {
    0 <= k and k < n implies p[k] == old(p[k])
} by auto;
```

Pointer-writing loops do not implicitly preserve old memory. Use explicit loop
invariants, loop effect summaries, or disjointness facts.

When an array parameter is passed to a pure Click function or predicate,
`old(p)` means the entry-state array ref, not just the old pointer value:

```click
ensures permutation(p, old(p), 0, 2) by {
    symbolic_execute();
    unfold(permutation);
    simp();
    close();
}
```

The current `p` argument carries post-state memory. The `old(p)` argument
carries function-entry memory. Both carry the same C pointer value unless the
pointer variable itself changed.

## Effects And Frames

Function-level effects:

```click
immutable by frame;
mutable p[0..n] by frame;
mutable dst[0..n], counter[0..1] by frame;
```

`immutable` means no externally visible memory is changed. Stack-local writes
are allowed. `mutable` means all externally visible writes are inside the listed
segments. It is an upper bound, not a promise that each cell changed.

Loop-level effects describe dynamic writes inside a loop. Step effects describe
one loop body iteration and may use iteration locals.

## Local Stack Memory

Local scalar address-of and local arrays allocate stack memory blocks named like
`local:x`. Local stack bookkeeping is not externally visible for function-level
effect checks.

Example:

```c
int32 local_array_roundtrip() {
    int32 a[3];
    a[0] = 7;
    return a[0];
}
```

The local array block is ordinary memory for load/store semantics, but it does
not count as an external mutation.

## Click Array Refs

A pure Click function or predicate parameter written as an array or pointer:

```click
predicate permutation(int32 a[], int32 b[], int32 lo, int32 hi)
```

receives pure array refs for `a` and `b`. Each ref carries:

- a `CMemory` snapshot
- a C pointer
- an element type, currently `int32` or `uint8`

Indexing `a[k]` inside the predicate loads from `a`'s carried memory, not from
some global ambient predicate memory. The element type decides pointer scaling
and whether the load yields an `int32` or `uint8` value. This lets
`permutation(p, old(p), lo, hi)` compare post-state `p` to entry-state `p`
without copying a snapshot array.

See [click-core.md](click-core.md) for the full C-pointer versus Click-array-ref
model.
