# Current Limitations

This page lists boundaries that agents should not silently assume away.

## C0 Is Small

Click does not parse general C. See [c0-subset.md](c0-subset.md). Missing
features include structs, unsigned integers beyond the narrow `uint8` byte
type, casts, globals, heap allocation, `for` loops, `switch`, and many
operators.

## Type Support Is Still Narrow

The verifier supports `int32` and a byte-like `uint8` type, including `uint8*`,
`uint8[]`, ASCII character literals, byte loads/stores, byte equality, and
typed Click array refs. This is not a full C integer model: there are no casts,
promotions, signedness conversions, or general unsigned arithmetic yet.

Ordered comparisons are supported for `int32`. `uint8` currently has equality,
inequality, truthiness, memory access, and return-value support.

## Aliasing Is Default

Distinct pointer parameters may alias. Add `disjoint(...)` whenever a proof
depends on non-overlap.

## Requirements Cannot Freely Read Memory

Direct memory reads in `requires` propositions are limited. Use a named
predicate for memory-reading preconditions, and unfold it in proof scripts when
the body is needed.

## Predicates Are Opaque

Predicate calls are not unfolded automatically. Exact predicate facts can be
reused, but proving a predicate body or using its consequences generally needs:

```click
unfold(predicate_name);
```

## `old(...)` Is Still A Surface Construct

`old(...)` is surface syntax for elaborating an expression in the function-entry
context. As an array argument to a pure Click function or predicate, `old(p)`
becomes an entry-state array ref, so `permutation(p, old(p), lo, hi)` has the
expected old-vs-current meaning.

Loop-invariant lowering now applies that same model to old-state pure
functions, so `old(count(p, lo, hi, x))` can elaborate through stdlib `count`
and preserve its `.fold` in Kernel Click. The elaborator still rejects attempts
to capture non-fixed local spec bindings inside `old(...)`.

There is still no public `ref<T>` syntax. Array refs are an internal pure Click
lowering concept for parameters written as `int32 p[]`, `int32* p`,
`uint8 p[]`, or `uint8* p`.

## Existentials Need Explicit Facts

`exists (int32 k) { ... }` is supported, and symbolic `(lo..hi).any(...)`
lowers to a bounded existential. `auto` can reuse matching existential facts,
but it does not synthesize witnesses yet. Concrete `.any` ranges still unroll
to finite disjunctions.

## Folds Are Partly Supported

Pure `.fold` supports concrete unrolling and symbolic `RangeFold` terms. The
kernel knows useful fold facts for current stdlib `count` proofs, but it is not
a general induction engine for arbitrary folds.

Loop invariants now elaborate through spec lowering, so unfolded pure Click
functions can contain `if`, `let`, and `.fold` values over explicit current and
entry memory snapshots. This supports direct invariants such as
`permutation(p, old(p), lo, hi)` when the proof unfolds the relevant predicate.

## Loop Invariants Need Explicit Facts

Pointer-writing loops do not implicitly preserve memory. Use invariants,
`mutable` effects, and `disjoint` requirements. Symbolic loops need invariants
for arithmetic bounds, memory safety, and postconditions.

## `simp` Is Not A Solver

`simp` performs deterministic local normalization and selected proof rules. It
does not search broadly, infer missing invariants, synthesize frame conditions,
or invent arithmetic lemmas.

## Diagnostics Are Developer-Oriented

Failure messages expose internal propositions, path facts, and memory terms.
They are useful for agents but not yet polished for end users.
