# Memory model

The memory model is central to Click. Many proof failures are aliasing or frame
failures, not arithmetic failures.

## Blocks and pointers

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

## Heap blocks and lifetimes

The supported `malloc` forms have a null outcome and a successful outcome.
Success creates a fresh block identity at offset zero, with either the exact
LP64 size of `struct T` or a verified runtime `int32`-array extent such as
`count * 4`. Heap identities are not reused within a proof. Fresh bytes are
live but uninitialized, so ownership permits stores but does not make an
unstored cell readable.

Click tracks two different facts on the successful branch:

- owned memory for the complete object permits reads and writes;
- `allocation(p, bytes)` is the exclusive authority and obligation to end that
  allocation's lifetime; `bytes` may be a supported symbolic runtime extent.

`free(p)` requires both facts for the complete allocation and consumes them.
`free(NULL)` changes nothing. An interior, stack, opaque, or retired pointer is
not a valid free target. A successful free retires the whole block identity;
all aliases and derived addresses then reject loads and stores, and a second
free is diagnosed separately. Verified function exits also check that live
allocation authority was returned through the contract or actually freed.

The allocation/null refinement and allocation/free transitions are recorded
as memory-snapshot edges. Registering the pending result has an explicit
memory-preserving edge, allowing existing loads and permissions to cross the
unresolved state. Failed allocation removes that metadata and returns to the
pre-allocation memory identity without producing allocation authority.
Successful allocation starts from the pending snapshot but introduces only
its fresh, uninitialized block. A successful `free` also emits a checked heap
lifetime-retirement effect connecting its before and after snapshots, exact
base, and possibly symbolic byte extent. This is deliberately distinct from a
mutable byte range: retirement changes which allocation identities are live,
while a mutable range bounds ordinary stores. Exact contract replay and
modular call verification therefore use the same lifetime model as direct
execution without pretending deallocation is a byte write.

Writes to a block freshly allocated by the current function are internal while
that block is being initialized: they do not mutate memory that was externally
visible at function entry. The function must still return the new access and
lifetime authority in its contract or free it. Registering allocation authority
for already-owned storage immediately before a direct `free` is likewise
bookkeeping, while the actual retirement remains an explicit lifetime effect.

## Argument memory and aliasing

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

## Loadable ranges

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

A checked universal fact that reads every `int32` cell under the exact guard
`0 <= k and k < n` also certifies `loadable(p[0..n])` for that same memory and
base. This lets a modular copy or initialization postcondition re-establish the
initialized prefix without an extra ad-hoc permission proposition. A narrower
guard, another base, or another memory snapshot does not establish the range.

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

## Old memory

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

Freeing an allocation retires it only in the current and later states. A load
inside `old(...)` remains a historical entry-state value when the entry
permissions and bounds justified that load; the corresponding current-state
load is still rejected as use-after-free.

## Effects and frames

Function-level effects:

```click
immutable by frame;
mutable p[0..n] by frame;
mutable dst[0..n], counter[0..1] by frame;
```

`immutable` means no memory visible at function entry is changed. Stack-local
writes and initialization of a function-fresh allocation are allowed.
`mutable` means all externally visible writes are inside the listed segments.
It is an upper bound, not a promise that each cell changed. Allocation and
retirement must still satisfy their separate lifetime/resource obligations.

Loop-level effects describe dynamic writes inside a loop. Step effects describe
one loop body iteration and may use iteration locals.

## Local stack memory

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

## Click array refs

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

See [click-core.md](surface-and-kernel.md) for the full C-pointer versus Click-array-ref
model.
