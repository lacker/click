# Modeled Binary Tree

This synthetic project fixes the ordinary C implementation that will drive
Click's recursive-structure-model design. The C is the implementation boundary:
future proof work must add contracts, resources, models, and tactics without
changing it into a verifier-specific form.

The tree is deliberately unbalanced and has no parent pointers or cached
metadata. `tree_node_init` connects caller-supplied nodes. `tree_leftmost` and
`tree_rightmost` use iterative structural descent. `tree_contains` performs a
recursive depth-first search. The two rotation functions rewire a root, pivot,
and middle subtree in the same shape used by balancing algorithms.

The intended abstract resource associates each root with the in-order sequence
of its node identities. It should support proofs that:

- leftmost and rightmost return the first and last sequence elements;
- depth-first search returns true exactly when the target identity is a member;
- left and right rotation preserve the exact sequence and node set; and
- traversal terminates for every finite owned tree.

## Pure model

`modeled_binary_tree.click` defines an example-local `Tree<T>` with `Empty`
and `Node(left, value, right)` constructors. Values occur at every node, and
either child may be empty. `T` is arbitrary; the model does not assume an
ordering or a particular C representation.

- `tree_size` counts nodes using the standard library's `Nat` and `nat_add`.
- `tree_mirror` exchanges left and right recursively.
- `tree_mirror_twice` proves that mirroring twice restores the original tree.
- `tree_mirror_preserves_size` proves that mirroring preserves node count.

Both theorems use structural induction with hypotheses for both children.
The size proof also uses the standard library's commutativity theorem for
natural-number addition. Recursive definitions decrease on immediate subtrees;
unknown trees and function applications remain symbolic in proofs.

Run `cargo run --bin click -- verify examples/modeled-binary-tree` from the
repository root. The example is also checked by `scripts/check.sh`.

## Remaining C connection

These are proofs about finite algebraic trees, not yet about C pointers or
memory ownership. Mirroring is a pure proof exercise, not a new C operation.
The sidecar imports the unchanged C but still declares no C function proof.
In particular, it does not yet establish C traversal termination, acyclicity,
or rotation correctness. The next step is a recursive resource relating heap
nodes to the pure model, including node identities for the in-order list.

The missing heap-derived sequence model is tracked by
[`recursive-structure-models.md`](../../issues/recursive-structure-models.md),
and structural termination of the iterative walks is tracked by
[`structural-loop-termination.md`](../../issues/structural-loop-termination.md).
