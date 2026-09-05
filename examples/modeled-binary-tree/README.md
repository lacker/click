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

`modeled_binary_tree.click` currently imports the C but intentionally declares
no function proof. The missing heap-derived sequence model is tracked by
[`recursive-structure-models.md`](../../issues/recursive-structure-models.md),
and structural termination of the iterative walks is tracked by
[`structural-loop-termination.md`](../../issues/structural-loop-termination.md).
