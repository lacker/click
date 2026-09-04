# Add abstract summaries for recursive memory structures

Found by the 2026-09-04 MVR audit. A directly recursive composite resource can
own an arbitrary finite binary tree, but ownership alone does not state the
tree's abstract contents or in-order sequence. Linear ownership can prevent
resource duplication or loss, but a contract that merely consumes one
well-formed tree and produces another still cannot state the API theorem that
the exact node sequence is unchanged. Linux rbtree does not store keys itself,
so its generic correctness property is preservation of node identity and
in-order order while links and colors change.

## Violated invariant

Contracts for a mutable recursive structure must be able to relate its finite
abstract model before and after mutation. The model must be derived from the
owned structure, not supplied as an unconstrained ghost assertion.

## Intended regression

Define an abstract model for a binary tree whose in-order sequence contains
node identities. Verify unchanged left- and right-rotation functions with
contracts showing that:

- the output contains exactly the input nodes;
- the in-order sequence is unchanged;
- parent/child links are consistent; and
- no node is duplicated or omitted.

Negative rotations that drop a subtree, reuse one child twice, or swap the
in-order position of two nodes must fail even if the output can still be
folded as some binary tree.

## Acceptance criteria

- The specification language has a finite abstract collection or algebraic
  model suitable for sequences of pointer identities, with explicit empty,
  singleton, concatenation, equality, and membership reasoning.
- A guarded recursive composite can expose a model determined compositionally
  from its node and direct children.
- Models retain pointer identity without turning pointers into arithmetic
  integers or granting pointee ownership.
- Function contracts can relate entry and exit models across a changed root.
- Reasoning and certificates are output-sensitive in the explicitly exposed
  model terms; no tactic unfolds an unknown whole tree automatically.
- The rotation regressions, an insert/erase model-preservation regression, and
  `scripts/check.sh` pass.

Related: [mathematical-integers-in-specs.md](mathematical-integers-in-specs.md)
and [resource-algebra-extensions.md](resource-algebra-extensions.md).
