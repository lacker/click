# Instantiate universals with symbolic bounds and index facts under folds

Found by the 2026-09-01 kernel audit at cb034b21.

- `finite_forall_ranges` (`src/kernel/reasoning/order_reasoning.rs:80-140`)
  produces a range only when each binder gets both a lower and an upper
  bound from constant order facts, with width at most 32, and
  `FINITE_FORALL_INSTANTIATION_LIMIT` is 128 (`order_reasoning.rs:36`). A
  universal guarded by a symbolic bound (`forall k. 0 <= k < n implies P(k)`)
  cannot be finitely instantiated and must be applied through explicit
  `instantiate` steps at each needed point.
- `alpha_bitvector_key` returns `None` for any term containing
  `Bitvector32Term::RangeFold` (`src/kernel/proof/fact_keys.rs:530`, consumed
  through `quantified_equivalence_index_key` at `:669` and
  `matching_quantified_facts` in `facts.rs:424-439`), so universal facts whose
  bodies mention a fold are never indexed and never matched by
  `matching_quantified_fact`. Array-sum invariants stated with a range fold
  cannot be reused through the fact index.

## Violated invariant

Deterministic reasoning should be able to use a universally quantified fact
at any point that is provably inside its guard, and should be able to find
an available universal fact regardless of the term forms in its body.

## Intended regression

Kernel unit tests: `P(j)` derived from `forall k. 0 <= k and k < n implies
P(k)` and `0 <= j < n` with symbolic `n`, without explicit instantiation;
`matching_quantified_fact` finding `forall i. 0 <= i < n implies s(i) ==
(0..i).fold(...)` under alpha-renaming. An mdtest: `int32 get(int32 a[],
int32 n, int32 j) { return a[j]; }` with `views a[0..n]; requires 0 <= j and
j < n;`, the universal `forall (k: int32) { 0 <= k and k < n implies 0 <=
a[k] }` available at entry (through a callee's ensures until
[memory-reads-in-requires.md](memory-reads-in-requires.md) lands), and
`ensures result >= 0 by simp;` with no explicit `instantiate`; today it fails
at the ensure and after the fix it verifies.

## Acceptance criteria

- A guarded-instantiation rule instantiates a universal at a term when the
  guard is provable for that term, with the derivation retained.
- The alpha key handles `RangeFold` by canonicalizing its binders.
- The tests above pass; `scripts/check.sh` passes.

Related: the finite-forall vacuity fix (landed 2026-09-01) made
`finite_forall_ranges` in `src/kernel/reasoning/order_reasoning.rs` accept
only bodies whose leaves are all guarded implications and instantiate the
hull of their guards; the guarded-instantiation rule above must keep that
condition.
