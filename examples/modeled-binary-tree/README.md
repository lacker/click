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

## Verified C initializer

The sidecar also defines `HeapTree`, an example-local model recording each
node's address, payload, and left/right submodels. Its `tree_at(p)` resource
relates that model to the actual heap:

- `Empty` requires `p == 0` and owns no memory.
- `Node(identity, value, left_model, right_model)` requires a nonnull `p`
  equal to `identity`, owns the three struct fields, and relates the stored
  payload to `value`.
- The children own `tree_at(p->left)` and `tree_at(p->right)`, with the
  corresponding submodels. Their memory ownership is disjoint from each
  other and the parent. Model addresses alone grant no ownership.

The unchanged `tree_node_init` is verified for arbitrary owned child models.
It takes separately owned writable parent fields and two modeled children,
performs the original three stores, and constructs a parent resource with
`HeapTree::Node(node, value, old(l.model), old(r.model))`. Folding explicitly
selects and consumes both children; no parent open handle is required.

The focused [resource_tree_node_init mdtest](../../mdtests/resource_tree_node_init.md)
also checks reading a payload through this resource and constructing an empty
tree. Expansion/rechecking and rejection tests cover wrong payloads or node
identities, swapped/missing links, unreadable child arguments, duplicate child
selection, and overlapping or reused ownership.

## Remaining C proofs

The generic `Tree<T>` theorems above remain pure model exercises; mirroring
is not a C operation. Only `tree_node_init` has a C function proof in this
example. Traversal termination, membership, rotations, and the heap-derived
in-order sequence are not yet verified. The next algorithm proof can use
`HeapTree`'s identities as well as values when describing a rotation.

The missing heap-derived sequence model is tracked by
[`recursive-structure-models.md`](../../issues/recursive-structure-models.md),
and structural termination of the iterative walks is tracked by
[`structural-loop-termination.md`](../../issues/structural-loop-termination.md).
