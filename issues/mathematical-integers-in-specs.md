# Offer unbounded integers on the specification side

Found by the 2026-09-01 kernel audit at cb034b21.

Every integer-valued specification term is a `Bitvector32Term`
(`src/kernel/primitives.rs:82-116`),
so contracts and invariants are stated modulo 2^32. A claim such as "result
equals the sum of the array" is only "equals the sum modulo 2^32", and an
invariant like `total == (0..i).fold(0, |acc, k| acc + a[k])` silently wraps.
Functional-correctness statements about real C arithmetic need a
mathematical integer sort with explicit conversions to and from machine
integers, so that overflow is a proof obligation rather than a change of
meaning.

## Violated invariant

A specification should be able to state exact arithmetic facts, with the
relationship between machine values and their mathematical counterparts made
explicit and checkable.

## Intended regression

Mdtest over `int32 sum(int32 a[], int32 n) { int32 total; int32 i; total = 0;
i = 0; while (i < n) { total = total + a[i]; i = i + 1; } return total; }`.
Provisional surface, to be pinned when the sort lands: `requires n <= 1000;`,
the bound `forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and
a[k] <= 1000 }` available at entry (through a callee's ensures until
[memory-reads-in-requires.md](memory-reads-in-requires.md) lands),
`ensures to_int(result) == (0..n).fold(0, |acc, k| acc + to_int(a[k]))` with
the fold typed over the new `int` sort, and the loop invariant
`to_int(total) == (0..i).fold(0, |acc, k| acc + to_int(a[k]))`. A negative
mdtest that drops the element bound must fail on the overflow obligation at
`total + a[i]`, not on the invariant.

## Acceptance criteria

- The kernel term language gains an unbounded integer sort with the usual
  operators and order, and conversion terms `to_int(bv)` / `from_int(z)`
  with definedness conditions.
- `RangeFold` and the finite-forall machinery work over the new sort.
- Surface Click can declare quantified variables and `let` bindings of the
  new sort.
- `scripts/check.sh` passes.

Related: [integer-types.md](integer-types.md).
