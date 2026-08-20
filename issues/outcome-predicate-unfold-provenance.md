# Preserve predicate-unfold provenance through outcome goals

## Violated invariant

A checked `UnfoldPredicate` step must remain the authority for every body fact
it introduced while the same outcome `Proof` advances through drain resyncs and
nested `have` scopes. Today the temporary `with_drained_outcome` adapter
rebuilds `ProofFacts` from a plain vector and loses the narrow index identifying
universals introduced by predicate unfolds. A later `simp` therefore cannot
select the body fact without either falling back or scanning unrelated ambient
universals.

The nested goal has a second representation mismatch: when an already-active
unfold lets `have predicate(...)` prove the predicate through its structural
body, the kernel and Surface views must agree on that body so `intro` retains
binder names, while the enclosing `Have` still publishes the opaque predicate
the user stated.

## Current reproductions

The fresh 2026-08-19 timing census identifies these passing fixtures as this
class:

- `mdtests/loop_stdlib_permutation_invariant.md`
- `mdtests/sort3_permutation.md`
- `mdtests/bubble_sort3_loop_permutation.md`

An uncommitted probe preserves only unfold-owned universal provenance that is
still present after resync and pairs an active predicate `have` body with its
unfolded Surface form. Those three fixtures then stop emitting both outcome
fallback spans. This is evidence for the slice, not a completed fix: the probe
must be isolated from later bound-transport experiments and pass the repository
gate.

## Intended regression

- A focused proof-object unit test applies a predicate unfold, resynchronizes a
  changed ordered fact vector, and proves that surviving unfold-owned
  universals remain in the special index while removed and unrelated ambient
  universals do not enter it.
- A nested predicate `have` regression introduces the unfolded body's binder,
  closes through ordinary simple steps, retains one opaque `Have`, expands, and
  independently reverifies.
- A multi-size curve grows unrelated facts while the resync and lookup remain
  proportional to the explicit unfold delta plus logarithmic index work.

## Acceptance criteria

- All three reproductions verify without `outcome simp compatibility
  construction` or `outcome simp legacy exit planning`.
- Resync preserves provenance only for surviving facts already owned by checked
  unfold steps; it never infers provenance by scanning or classifying the
  ambient fact vector.
- The retained certificate expands and independently verifies.
- `scripts/check.sh` passes.

