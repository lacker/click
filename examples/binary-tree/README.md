# Binary Tree

This project verifies an arbitrary finite binary tree over caller-supplied
nodes. Its guarded recursive resource is empty at null and otherwise owns the
root node's three fields plus two still-folded child trees.

`tree_empty` constructs the empty tree from C's null pointer constant.
`tree_make_root` combines a detached node and two child trees. `tree_root`
reads through one unfolded level, and `tree_swap_children` exchanges the two
recursive subtrees while preserving the tree resource. `tree_leaf_pipeline`
composes the complete API with two independently returned empty children; this
checks that repeated empty recursive resources behave as the identity rather
than conflicting ownership.

The example is intentionally about branching resource composition. It does
not cover allocation, deallocation, traversal, balancing, parent pointers,
shared subtrees, or cycles.

The project also includes a verified `tree_is_leaf` algorithm, which observes
both child links without consuming the tree. A one-level sum and a left
rotation were also implemented in C. They remain small motivating cases for
the symbolic-addition, nested-resource certification, and nested mutable-path
gaps recorded in `issues/`; they are deliberately not listed as verified.
