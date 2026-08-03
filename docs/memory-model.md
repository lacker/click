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

C0's integer constant `0` converts to a single canonical null pointer in
pointer-valued return, initialization, assignment, argument, and comparison
contexts. This narrow conversion does not identify pointers with integers:
nonzero integers still cannot be used as pointers.

## Argument Memory And Aliasing

Function pointer parameters are modeled as symbolic offsets into one shared
external argument-memory block. The identity of that external block is not
assumed distinct from null, so an unconstrained pointer parameter retains both
its null and non-null executions. Distinct pointer parameter names do not imply
non-aliasing.

If a proof relies on non-overlap, state it:

```click
requires separate(memory(dst[0..n]), memory(src[0..n]));
```

This is intentionally C-like. C functions can be called with aliased pointers
unless their contract rules that out.

## Loadable Ranges

Use `loadable` to prove memory safety:

```click
requires loadable(p[0..3]);
requires loadable(p[0..n]);
requires loadable((p + 1)[0..n - 1]);
```

Segment forms are half-open `int32` element ranges. For `int32 p[]`,
`loadable(p[0..n])` means cells `p[0]` through `p[n - 1]` are available for
four-byte `int32` access. For `uint8 p[]`, the same spelling covers `n`
one-byte elements.

Symbolic memory access usually needs:

- a covering viewed or owned memory resource, or a separate loadable range
- lower and upper index bounds
- loop invariants if the bounds are established by a loop

Viewed and owned memory resources imply loadability for the covered range. A separate
`loadable(...)` clause is useful when a proof needs loadability without access
permission, or when it needs a larger structural range than the immediate
permission covers.

Use `loadable(p[lo..hi])` for the same kind of loadability fact when Click
expects a proposition, for example in a composite resource `fact`. `loadable`
does not grant read or write authority; it only supplies the pure fact needed
to justify loads from that range when the index bounds are known.

In an explicit proof, use proposition-level `at(...)` to refer to loadability
at a recorded program point:

```click
have at(statement(0).entry, loadable(p[0..n])) by {
    assumption();
}
```

This snapshots the whole loadability proposition. In particular, its pointer,
range bounds, and memory state are all interpreted at `statement(0).entry`.
Writing `loadable(at(statement(0).entry, p)[0..n])` is not equivalent: that
would snapshot the pointer expression but still ask whether it is loadable in
the current memory.

## Old Memory

`old(expression)` evaluates in the function-entry state:

```click
ensures p[0] == old(p[0]) by auto;
```

For quantified old-memory postconditions:

```click
ensures forall (k: int32) {
    0 <= k and k < n implies p[k] == old(p[k])
} by auto;
```

Pointer-writing loops do not implicitly preserve old memory. Use explicit loop
invariants, loop effect summaries, or separation facts.

When an array parameter is passed to a pure Click function or predicate,
`old(p)` means the entry-state array ref, not just the old pointer value:

```click
ensures permutation(p, old(p), 0, 2) by {
    execute();
    unfold(permutation);
    simp();
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

Automatic storage is not initialized by declaration. A scalar declaration such
as `int32 x;`, a pointer declaration such as `int32* p;`, and the cells of a
local array have no readable value until the program writes them. Reading one
first is modeled as undefined behavior; taking its address or assigning to it
is allowed.

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
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32)
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
