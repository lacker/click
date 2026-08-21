# Click core model

This page explains how Surface Click, C fragments, and Kernel Click meet. It
is the mental model agents should use when changing lowering code.

## Three layers

Click has three layers:

1. **Kernel Click**: pure, explicit specification values and propositions sent
   to the kernel. It is a Rust data model, not a textual language users can
   place in a `.click` file.
2. **Surface Click**: user-written `.click` syntax such as `requires`,
   `ensures`, `invariant`, `old`, pure functions, predicates, quantifiers,
   and folds.
3. **C fragments**: pieces of C0 syntax inside Surface Click, such as `p[k]`,
   `x + 1`, or `result == n`.

Surface Click is convenience syntax. It may contain C fragments, but Surface
Click owns their meaning and elaborates everything into Kernel Click over
explicit memory states.

Expansion travels in the other direction only through retained surface
provenance and a canonical Surface Click renderer. It must never pretty-print
the kernel data model directly. Consequently, output from expansion and
diagnostics is part of the public Surface Click language and must parse again
with the ordinary parser.

## Surface versus core

Surface Click is context-sensitive. A term such as `p[k]` or `old(p)` is not
itself the final proof object; it still depends on where the term appears.

Kernel Click is pure and explicit. It may still mention C semantic data, but
only as values:

```text
load(memory_snapshot, pointer + k)
RangeFold(start, end, initial, ...)
ForAll(var, body)
```

The important rule is that C state is never ambient in Kernel Click. Surface
Click is elaborated against a chosen state, and that state becomes an explicit
`CMemory`, `Pointer`, or `CValue` inside the term.

In `src/lang/click.rs`, invariant elaboration is driven by
`SpecElaborationContext`. That context carries:

- scalar bindings already elaborated to `SpecExpression`
- array-ref bindings as explicit `{ memory, pointer }` pairs in Kernel Click
  elaboration and typed `ClickArrayRef` values in surface contract evaluation
- the memory that current C-fragment reads should use

`old(expr)` is not a separate expression language. In loop invariants it
re-elaborates `expr` under a derived context whose current memory is the
function-entry memory and whose ordinary variables are rebound to entry values.
This is what lets `old(count(p, 0, n, x))` lower through the ordinary stdlib
`count` definition and keep its `.fold` as Kernel Click.

## C pointers versus Click array refs

A C pointer says where:

```text
Pointer { block, offset }
```

A Click array ref says where and in which memory snapshot:

```text
ClickArrayRef { memory, pointer, element_type }
```

It is a pure specification value. It is not a C runtime object, it is not
stored in C memory, and C code cannot mutate it. If C code writes through a
pointer, that produces a new `CMemory` value. Existing array refs still refer to
the memory snapshot they were built from.

The `element_type` is currently `int32` or `uint8`. It decides both pointer
scaling and the type of value produced by indexing the array ref.

## Surface elaboration

In a postcondition, a bare array parameter used as an array argument means the
post-state array:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
p
```

elaborates like:

```text
ClickArrayRef { memory: post_memory, pointer: p, element_type: int32 }
```

For a `uint8 p[]` parameter, the same shape uses `element_type: uint8`.

An old array argument means the entry-state array at the same pointer value:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
old(p)
```

elaborates like:

```text
ClickArrayRef { memory: pre_memory, pointer: p, element_type: int32 }
```

Inside a pure Click function or predicate, indexing an array-ref parameter:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
p[k]
```

means:

```text
load(p.memory, p.pointer + k * sizeof(p.element_type))
```

So:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
permutation(p, old(p), 0, 2)
```

means:

```text
permutation(
  ClickArrayRef { memory: post_memory, pointer: p, element_type: int32 },
  ClickArrayRef { memory: pre_memory, pointer: p, element_type: int32 },
  0,
  2
)
```

This is why `permutation` can live in `stdlib/prelude.click`: it is an ordinary
Click predicate over pure array refs, not a kernel-level permutation concept.

## Loop invariants

Loop invariants use the same surface-to-core idea, but they are state-parametric.
The lowered invariant is evaluated at:

1. the pre-loop entry state
2. the symbolic loop-head state
3. the post-body preservation state

A current array argument in a loop invariant means the array in whichever loop
state is being checked:

```text
ClickArrayRef { memory: loop_state.memory, pointer: p, element_type }
```

An old array argument still means the function-entry memory:

```text
ClickArrayRef { memory: function_entry_memory, pointer: p, element_type }
```

More generally, `old(expr)` inside an invariant switches elaboration of `expr`
to the function-entry context. Current memory reads inside that expression
become fixed-memory reads, so pure helpers such as `count` do not need a
separate old-state evaluator.

This is represented in the kernel with `SpecExpression` and
`SpecProposition`: Kernel Click forms that can include current-state C
fragments, pure `if`, `let`, `.fold`, and explicit fixed-memory loads. This is
why an invariant can unfold `permutation` and then evaluate the `.fold` inside
stdlib `count` without pretending that the fold is executable C.

## Source spelling

There is no public `ref<int32>` syntax yet. For now, parameters written as
`int32 p[]`, `int32* p`, `uint8 p[]`, or `uint8* p` in pure Click `function`
and `predicate` definitions are treated as Click array-ref parameters.

This is intentionally source-compatible with existing C-like signatures:

<!-- verified-example: mdtests/pure_click_functions.md -->
```click
function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 { ... }

predicate sorted(p: int32*, n: int32) { ... }
```

The parameter spelling fixes the array-ref element type. A pure Click function
or predicate declared with `uint8 p[]` indexes one byte at a time and returns
`uint8` values from `p[k]`.

Ordinary postcondition and predicate/function evaluation use typed
`ClickArrayRef` values. Loop-invariant spec lowering uses typed
`SpecArrayRef { memory, pointer, element_type }` values plus typed
`SpecExpression::MemoryLoad` and byte-width `SpecExpression::PointerOffset`
nodes, so byte-aware pure helpers can appear in invariants and inside
`old(...)`.

In C function signatures, the same spelling still means an ordinary C pointer.
The array-ref interpretation only applies while lowering pure Click functions
and predicates.

## Implementation notes

In `src/lang/click.rs`, `ClickArrayRef` is private lowering state. Opaque
kernel predicate arguments encode an array ref as two terms:

```text
Term::CMemory(memory), Term::CValue(CValue::Pointer(pointer))
```

When a predicate is unfolded, Click reconstructs the array-ref environment from
those terms before lowering the predicate body. This keeps the kernel free
of domain names like `permutation` while still making memory state explicit
enough for `old(p)` to work as an array argument.

All predicate calls use expanded array-ref arguments. Each array-ref parameter
contributes its memory snapshot and pointer as separate kernel terms.
