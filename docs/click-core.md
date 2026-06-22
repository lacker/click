# Click Core Model

This page explains how C expressions and Click expressions meet. It is the
mental model agents should use when changing lowering code.

## Three Layers

Click has three layers:

1. C execution layer: mutable C0 state, C values, C pointers, statements, and
   memory updates.
2. Click surface layer: `.click` syntax that can mention C-looking expressions
   such as `p[k]`, `old(p[k])`, `count(p, 0, n, x)`, and
   `permutation(p, old(p), 0, n)`.
3. Click core layer: pure specification values and propositions sent to the
   megakernel.

The surface layer is convenience syntax. It elaborates C-looking expressions
into pure values over explicit memory states.

## Surface Versus Core

Surface Click is context-sensitive. A term such as `p[k]` or `old(p)` is not
itself the final proof object; it still depends on where the term appears.

Core Click is pure and explicit. It may still mention C semantic data, but only
as values:

```text
load(memory_snapshot, pointer + k)
RangeFold(start, end, initial, ...)
ForAll(var, body)
```

The important rule is that C state is never ambient in core Click. Surface Click
is elaborated against a chosen state, and that state becomes an explicit
`CMemory`, `Pointer`, or `CValue` inside the term.

## C Pointers Versus Click Array Refs

A C pointer says where:

```text
Pointer { block, offset }
```

A Click array ref says where and in which memory snapshot:

```text
ClickArrayRef { memory, pointer }
```

It is a pure specification value. It is not a C runtime object, it is not
stored in C memory, and C code cannot mutate it. If C code writes through a
pointer, that produces a new `CMemory` value. Existing array refs still refer to
the memory snapshot they were built from.

## Surface Elaboration

In a postcondition, a bare array parameter used as an array argument means the
post-state array:

```click
p
```

elaborates like:

```text
ClickArrayRef { memory: post_memory, pointer: p }
```

An old array argument means the entry-state array at the same pointer value:

```click
old(p)
```

elaborates like:

```text
ClickArrayRef { memory: pre_memory, pointer: p }
```

Inside a pure Click function or predicate, indexing an array-ref parameter:

```click
p[k]
```

means:

```text
load(p.memory, p.pointer + k)
```

So:

```click
permutation(p, old(p), 0, 2)
```

means:

```text
permutation(
  ClickArrayRef { memory: post_memory, pointer: p },
  ClickArrayRef { memory: pre_memory, pointer: p },
  0,
  2
)
```

This is why `permutation` can live in `stdlib/prelude.click`: it is an ordinary
Click predicate over pure array refs, not a kernel-level permutation concept.

## Loop Invariants

Loop invariants use the same surface-to-core idea, but they are state-parametric.
The lowered invariant is evaluated at:

1. the pre-loop entry state
2. the symbolic loop-head state
3. the post-body preservation state

A current array argument in a loop invariant means the array in whichever loop
state is being checked:

```text
ClickArrayRef { memory: loop_state.memory, pointer: p }
```

An old array argument still means the function-entry memory:

```text
ClickArrayRef { memory: function_entry_memory, pointer: p }
```

This is represented in the megakernel with `CSpecExpression` and
`CSpecProposition`: spec/core forms that can embed current-state C expressions
but can also represent pure `if`, `let`, `.fold`, and explicit fixed-memory
loads. This is why an invariant can unfold `permutation` and then evaluate the
`.fold` inside stdlib `count` without pretending that the fold is executable C.

## Source Spelling Today

There is no public `ref<int32>` syntax yet. For now, parameters written as
`int32 p[]` or `int32* p` in pure Click `function` and `predicate` definitions
are treated as Click array-ref parameters.

This is intentionally source-compatible with existing C-like signatures:

```click
function count(int32 p[], int32 lo, int32 hi, int32 x) -> int32 { ... }

predicate sorted(int32* p, int32 n) { ... }
```

In C function signatures, the same spelling still means an ordinary C pointer.
The array-ref interpretation only applies while lowering pure Click functions
and predicates.

## Implementation Notes

In `src/lang/click.rs`, `ClickArrayRef` is private lowering state. Opaque
kernel predicate arguments encode an array ref as two terms:

```text
Term::CMemory(memory), Term::CValue(CValue::Pointer(pointer))
```

When a predicate is unfolded, Click reconstructs the array-ref environment from
those terms before lowering the predicate body. This keeps the megakernel free
of domain names like `permutation` while still making memory state explicit
enough for `old(p)` to work as an array argument.

The old one-hidden-memory predicate shape is still accepted for legacy opaque
facts and C predicate lowering. New Click predicate calls with known signatures
use expanded array-ref arguments.
