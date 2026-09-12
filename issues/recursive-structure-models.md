# Add abstract summaries for recursive memory structures

P1: required for MVR. A directly recursive composite resource can
own an arbitrary finite binary tree, but ownership alone does not state the
tree's abstract contents or in-order sequence. Linear ownership can prevent
resource duplication or loss, but a contract that merely consumes one
well-formed tree and produces another still cannot state the API theorem that
the exact node sequence is unchanged. Linux rbtree does not store keys itself,
so its generic correctness property is preservation of node identity and
in-order order while links and colors change.

The core ADT and list foundation is implemented. Recursive `HeapTree`
fields now connect parent models to child models across ownership and mutation;
the derived in-order list also has a checked left-rotation preservation theorem.
The remaining work is extending these guarantees to required rbtree algorithms.
General ADT completeness is P2 under
[algebraic-data-types.md](algebraic-data-types.md), not a prerequisite to closing
this issue. This issue owns model-related MVR obligations and the narrow
integration slices their proofs actually require, such as model transport
through a required call or constructor cases during traversal.

The fixed synthetic C scaffold for this work lives in
[`examples/modeled-binary-tree`](../examples/modeled-binary-tree/README.md).
Its sidecar verifies the unchanged initializer and left rotation against an
exact `HeapTree` model carrying node addresses, payloads, and both subtrees.
Left rotation preserves both affected nodes and all three arbitrary subtrees.
Its C contract also preserves the exact derived in-order node-identity list.
Right rotation and insert/erase regressions remain. Synthetic examples are
development regressions, not a requirement to verify an extra tree library
before launch; the target is the pinned unchanged Linux implementation.

Found at the function-contracts close-out (2026-09-11): a model-gated
composite cannot expose its links at contract-lowering time. With
`resource tree_at(p) { field model: Shape; match model { ... owns p->left;
owns p->right; ... } }`, a contract `consumes t: tree_at(node); owns
node->right->augmented;` fails surface lowering with `missing pure fact:
loadable(base=node[2], bytes=8)`: which links `tree_at` owns depends on the
`model` arm, and no proof step has selected the `Shape::Node` arm when the
contract is lowered. The memory-only `shape` resource, whose body is an
`if`-guarded block, has no such gate and the same contract lowers. So
`mdtests/augment_rotate_model_callback.md` keeps its helper contracted over
the root's link cells and the two subtree instances instead of one folded
`tree_at(node)`. The missing piece is deciding a matched arm from a
requirement such as `requires t.model != Shape::Empty` at contract lowering,
or otherwise exposing a matched composite's cells there. Regression: that
fixture's `rotate_left` contracted as `consumes t: tree_at(node); produces r:
tree_at(result); owns node->augmented; owns node->right->augmented;`.

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

- Preserve the implemented ownership-backed resource fields and compositional
  parent/child models; no generalized witness syntax is required by itself.
- Models retain pointer identity without turning pointers into arithmetic
  integers or granting pointee ownership.
- Function contracts can relate entry and exit models across a changed root.
- Reasoning and certificates are output-sensitive in the explicitly exposed
  model terms; no tactic unfolds an unknown whole tree automatically.
- Required rbtree contracts establish exact rotation order preservation,
  insertion of the designated node, erasure of the designated node, and the
  specified identity substitution on replacement. Insertion and erasure must
  describe the correct sequence change, not equality with the input sequence.
- Models express parent/child consistency, acyclicity, red-black color and
  black-height invariants, and correct traversal results. Required algorithms
  establish their respective guarantees. Loop termination is coordinated with
  [structural-loop-termination.md](structural-loop-termination.md).
- Small positive and negative rotation and insert/erase regressions (synthetic
  or on the pinned source), required MVR model proofs, and
  `scripts/check.sh` pass.

Integer specification coverage is landed and documented in
[the mathematical-integer internals](../docs/internals/mathematical-integers.md);
this MVR model work has no pending dependency on the retired Integer P1
issue. Related: [algebraic-data-types.md](algebraic-data-types.md) and
[resource-algebra-extensions.md](resource-algebra-extensions.md).
