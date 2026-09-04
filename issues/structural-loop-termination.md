# Prove loop termination from recursive structure descent

Found by the 2026-09-04 MVR audit. Click's optional loop termination rule uses
`int32` expressions. Linux rbtree traversal and rebalancing loops instead move
down child links or up parent links without maintaining a numeric counter.
The finite recursive tree or ancestor-context resource already contains the
natural well-founded witness, but only recursive function calls can currently
name such a witness with `decreases resource`.

Partial correctness is not enough for MVR: the rbtree source explicitly
depends on traversal and rebalancing completing, and its lockless-reader notes
call out absence of temporary child-pointer cycles as a termination property.
Concurrent-reader termination remains outside this sequential issue.

## Violated invariant

An unchanged finite-structure loop should be able to prove termination from a
kernel-checked strict descent through a guarded recursive resource, without a
proof-only C counter or an execution budget.

## Intended regression

Use unchanged C loops for:

1. descending through left children to the minimum node;
2. ascending through parent links represented by a recursive tree-context
   resource; and
3. an rbtree-style loop that sometimes performs a local rotation and then
   continues at a strict ancestor.

Negative cases that stay on the same node, move to an unrelated node, or
recreate a previously consumed context layer must fail.

## Acceptance criteria

- A loop may declare a guarded directly recursive composite resource as a
  structural decreases measure.
- Every continuing back edge identifies a direct contained child witness in
  the exact resource definition, and the kernel checks the ancestry evidence.
- The rule composes with loop invariants and resource transformations needed
  to unfold, rotate, refold, and continue with the surviving strict child.
- No hidden counter, bounded unrolling, heap-size assumption, or C rewrite
  stands in for well-foundedness.
- Descending and ascending traversal, rebalancing, and negative regressions
  pass with `scripts/check.sh`.

Related: [recursion.md](recursion.md) and
[recursive-structure-models.md](recursive-structure-models.md).
