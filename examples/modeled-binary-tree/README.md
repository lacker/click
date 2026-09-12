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

## Verified C left rotation

The unchanged `tree_rotate_left` consumes a tree whose root and right child
are nonempty, and produces the returned tree with model
`heap_rotate_left(old(t.model))`. This exact structural transformation retains
both node addresses and payloads and all three arbitrary subtrees.

Two entry proof matches name the root and pivot fields and close the empty
cases from the preconditions. Unfolding exposes independent child resources;
after the original C loads and stores, explicit folds reconstruct the lower
node and returned pivot. No named open handles are used. The proof checks
memory ownership as well as the model transformation.

`heap_inorder` derives a `List<struct tree_node*>` from the owned model, visiting
left subtree, node, then right subtree. The pure theorem
`heap_rotate_left_preserves_inorder` proves that rotation preserves this exact
list, using the standard library's append-associativity theorem. The C contract
also guarantees `heap_inorder(rotated.model) == heap_inorder(old(t.model))`:
node identities, their order, and their multiplicities are unchanged.

## Verified C right rotation

`heap_rotate_right` mirrors `heap_rotate_left`, and `heap_left` is the
accessor its contract needs to state that the root's left child is nonempty.
The unchanged `tree_rotate_right` consumes a tree whose root and left child
are nonempty and produces the returned tree with model
`heap_rotate_right(old(t.model))`.

The proof mirrors the left one: two entry matches name the root and pivot,
unfolding exposes the far-left and middle subtrees as independent resources,
and after the original four C statements explicit folds reconstruct the lower
node and the returned pivot. `heap_rotate_right_preserves_inorder`, proved
through its per-node helper from the standard library's append-associativity
theorem, gives the contract's second guarantee
`heap_inorder(rotated.model) == heap_inorder(old(t.model))`.

## Membership

`heap_member` is the recursive `int32`-valued membership test over the model:
it returns 1 when the target is the node's own address, otherwise searches the
left subtree and then the right one, in the order the C search uses. The
standard library already has list membership as `list_contains`, so no new
list function is needed.

`heap_member_is_inorder_membership` proves
`heap_member(tree, target) == list_contains(heap_inorder(tree), target)` by
structural induction, using the library's `list_contains_append` and
`list_contains_cons`. Membership in the model is therefore exactly membership
in the derived in-order sequence, which is what the rotation theorems preserve.

`heap_member_nonzero_is_one` proves
`heap_member(tree, target) != 0 implies heap_member(tree, target) == 1`, also
by structural induction. The C search only learns that a recursive call
returned nonzero, while `heap_member` tests its left subtree with
`heap_member(left, target) == 1`, so the membership proof needs that range
fact to connect the two.

## Verified C depth-first search

The unchanged recursive `tree_contains` is verified against
`owns t: tree_at(root);` with `ensures t.model == old(t.model);` and the
unguarded `ensures result == heap_member(old(t.model), target);`.
The proof matches the entry model, unfolds the root in the nonempty case,
spells the two C `if` statements with `branch`, hands each recursive call the
matching child instance through the call binder map, and refolds the root
from the returned children on every path. Recursion therefore descends through
a matched, modeled resource without losing or duplicating any subtree.

The membership guarantee is where the model's identity payload earns its
place. `heap_member` tests `node == target` against the payload, while the C
tests the address `root == target`; `tree_at` states `fact p == identity`, and
the proof turns that into `node == target` with

```click
have node == target by {
    rewrite(node == root);
    normalize() using { root == target; }
}
```

A pointer payload is an ordinary pointer in a proposition, so this compares a
`struct tree_node*` payload with a C pointer directly, with no conversion and
no ownership of its own. `mdtests/model_identity_pointer_payload.md` is the
minimal form of the same bridge, carried all the way to an unconditional
`ensures result == cell_member(old(c.model), q);`.

Both recursive calls appear only inside a condition or a return expression, so
their results are never stored in a named C object. The proof names each one
with the binder the call step already has:

```click
let found_left = step(tree_contains(root->left, target), { t: l });
```

`tree_contains` declares no `produces` binder, so this `let` binds
`found_left` to the call's scalar result instead of to a produced instance.
The name is then usable on either side of the `branch` that spells the C `if`:
the then arm combines `found_left != 0` with the callee's
`found_left == heap_member(left_model, target)`, and the else arm combines
`found_left == 0` with the same guarantee. The final
`return tree_contains(root->right, target);` is named the same way, and
`result` is that value.

Structural termination is verified too. `decreases t;` names the contract's
own `owns t: tree_at(root)` binder, and the `HeapTree::Node` arm's `left` and
`right` children are the direct contained children each recursive call must
pass, so the measure is the modeled resource rather than a pointer or a
counter.

## Verified C iterative walks

`tree_leftmost` and `tree_rightmost` are unchanged, and their contracts are the
zipper of decision D3: the walk consumes the whole tree and produces a context
and a focused subtree at the node it stopped on.

```click
struct tree_node* tree_leftmost(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    produces ctx: ctx_at(result);
    produces sub: tree_at(result);
    ensures plug(ctx.model, sub.model) == old(t.model);
    ensures heap_left(sub.model) == HeapTree::Empty;
}
```

`Context` is `Top | Left(parent, value, sibling, up) | Right(...)`, and
`ctx_at(child)` is the resource that holds everything the tree has except the
focused subtree: the parent's three cells, the untaken sibling as a
`tree_at`, and the frame above as another `ctx_at`. This C has no parent
pointers, so the frame is keyed by the focused child and carries the parent in
its payload; the rbtree frames of D3 take the parent as a second argument
because those loops already maintain it as a C local. `plug(ctx, sub)` rebuilds
the whole model from a context and the focused subtree, so
`plug(ctx.model, sub.model) == old(t.model)` says the walk lost nothing.

The loop declares both binders, and its measure is the focused subtree:

```click
loop {
    owns ctx: ctx_at(root);
    owns t: tree_at(root);
    decreases t;
    invariant t.model != HeapTree::Empty;
    invariant plug(ctx.model, t.model) == old(t.model);
}
```

One iteration matches the binder's model, unfolds it, folds the left child's
frame from the parent's cells, the right subtree and the old context, and
steps `root = root->left`. `close_invariants()` then rebinds `ctx` to the new
frame and `t` to the left subtree by proved argument equality, and the
structural measure sees a direct contained child of what the head held.

Two arm-selection decisions carry the walk. `requires t.model !=
HeapTree::Empty` selects the `HeapTree::Node` arm at contract lowering, and
that arm supplies its own `fact p != 0`, so `if (root == 0)` is decided by
`step()` with no `branch`. The same decision runs backwards inside the loop:
the guard `root->left != 0` contradicts the `HeapTree::Empty` arm's `fact
p == 0`, so the child the unfold produces has model `!= HeapTree::Empty`,
which is the next iteration's invariant. After the loop the guard is false, the
same rule refutes the `HeapTree::Node` arm instead, and because `Empty` carries
no fields the equation `left_model == HeapTree::Empty` is published outright;
that is the postcondition `heap_left(sub.model) == HeapTree::Empty`.

Two focused negatives cover the frame:
[loop_decreases_rejects_unrelated_node](../../mdtests/loop_decreases_rejects_unrelated_node.md)
moves the cursor to a node of another tree the contract owns, and
[loop_context_frame_refold_rejected](../../mdtests/loop_context_frame_refold_rejected.md)
folds a second frame from children the first frame already consumed.

## Transporting a context's sequence

A fixup replaces the focused subtree, so a proof about the whole tree needs
that the surrounding context carries an in-order equality down to the root:

```click
theorem plug_inorder_transport(ctx: Context, a: HeapTree, b: HeapTree) {
    requires heap_inorder(a) == heap_inorder(b);
    ensures heap_inorder(plug(ctx, a)) == heap_inorder(plug(ctx, b)) by {
        induct(ctx) as ih { ... }
    }
}
```

Each frame arm plugs its own node between the context and the subtree, so the
residual goal is this theorem for `up` at the two *larger* subtrees
`Node(parent, value, a, sibling)` and `Node(parent, value, b, sibling)`, not at
`a` and `b`. The hypothesis is therefore instantiated at the complete parameter
list, `ih(up, Node(...), Node(...))`, and its requirement at those arguments is
established by the `have` just above the application. A hypothesis fixed at the
theorem's own `a` and `b` has no applicable instance here.

## Negative rotation regressions

Three focused mdtests keep the model honest against rotations that are wrong
in a specific way, each with the same resource, contract, and proof script as
the passing [rotation_model_preserved](../../mdtests/rotation_model_preserved.md):

- [rotation_model_rejects_dropped_subtree](../../mdtests/rotation_model_rejects_dropped_subtree.md)
  never relinks the middle subtree;
- [rotation_model_rejects_reused_child](../../mdtests/rotation_model_rejects_reused_child.md)
  links the old root into both of the pivot's slots; and
- [rotation_model_rejects_swapped_order](../../mdtests/rotation_model_rejects_swapped_order.md)
  builds a perfectly well-formed tree that holds the same nodes in a different
  in-order sequence.

The first two fail at the fold, because linear ownership cannot produce the
proposed parent from the links the C actually stored. The third folds without
complaint and fails at the `have` that would state the rotated model, which is
the case ownership alone cannot catch.

## Remaining C proofs

The generic `Tree<T>` theorems above remain pure model exercises; mirroring
is not a C operation. Every C function in this project now has a contract:
`tree_contains` terminates by its structural measure, and the iterative walks
terminate by theirs.

Further recursive-model algorithms are tracked by
[`recursive-structure-models.md`](../../issues/recursive-structure-models.md),
and structural termination of the ascending and rotate-then-ascend loop shapes
is tracked by
[`structural-loop-termination.md`](../../issues/structural-loop-termination.md).
