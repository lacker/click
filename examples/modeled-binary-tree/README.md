# Modeled Binary Tree

This project verifies an ordinary unbalanced binary tree against an exact
abstract model. The C is the implementation boundary: it has no parent
pointers, no cached metadata, and no verifier-specific shape, and every proof
here is a contract, resource, model, lemma, or tactic added beside it.

Every function in `modeled_binary_tree.c` is verified:

- `tree_node_init` connects three caller-supplied fields and two modeled
  children into one node;
- `tree_rotate_left` and `tree_rotate_right` rewire a root, pivot, and middle
  subtree, preserving the exact in-order node sequence;
- `tree_contains` is a recursive depth-first search, proved equal to model
  membership and proved to terminate by its structural measure; and
- `tree_leftmost` and `tree_rightmost` are iterative structural descents,
  proved to lose nothing through a context resource and to stop on a node
  with no child on the walked side.

Run `cargo run --bin click -- verify examples/modeled-binary-tree` from the
repository root. `cargo run --bin click -- audit examples/modeled-binary-tree`
expands every smart tactic and rechecks the result: 37 of 37 sites. The example
is also checked by `scripts/check.sh`.

## The model

`HeapTree` is the exact model of one owned tree:

```click
spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}
```

A node carries its own address, its payload, and both submodels. The address is
identity, not authority: a model grants no ownership and is never converted to
an integer.

`tree_at(p)` is the resource that relates the model to the heap. Its body
matches the model, so which cells it owns depends on which constructor it
carries:

- `Empty` requires `p == 0` and owns no memory.
- `Node(identity, value, left_model, right_model)` owns the three struct
  fields, states `p != 0`, `p == identity`, and `p->value == value`, and owns
  `left: tree_at(p->left)` and `right: tree_at(p->right)` with the
  corresponding submodels.

Ownership of the two children is disjoint from each other and from the parent,
so a tree is a linear object: no proof here can duplicate, drop, or alias a
subtree.

## The context resource and `plug`

A walk stops in the middle of a tree, so its contract needs a name for
everything the tree has *except* the focused subtree. That is the zipper:

```click
spec enum Context {
    Top,
    Left(struct tree_node*, int, HeapTree, Context),
    Right(struct tree_node*, int, HeapTree, Context),
}
```

`ctx_at(child)` is the matching resource. `Top` owns nothing. A `Left` frame
owns the parent's three cells, the untaken sibling as `tree_at(parent->right)`,
and the frame above as `ctx_at(parent)`, and states `parent->left == child`.
`Right` mirrors it. The frame is keyed by the focused child and carries the
parent in its payload, because no C local here names the focus's parent and a
pure function cannot return a pointer to supply one. The rbtree frame is keyed
the same way for the same reason; its second argument, `ctx_at(child, root)`,
is the root struct, so that the `Top` frame can own `root->rb_node`.

The frame's cells hang off a constructor binding rather than off the resource's
own parameter: `Context::Left`'s first field is declared `struct tree_node*`, so
`parent` is a struct base for the whole arm. A frame owns a `tree_at` sibling,
which is a child of another declared family; `ctx_at` contains `tree_at` and
`tree_at` never contains `ctx_at`, so the cycle rejection is untouched.

`plug(ctx, sub)` rebuilds the whole model from a frame stack and the focused
subtree, descending on the context. `plug(ctx.model, sub.model) == old(t.model)`
is then the statement that a walk lost nothing: not that the result is *a*
well-formed tree, but that it is the same tree, with the same nodes in the same
order.

## Verified C initializer

The unchanged `tree_node_init` takes separately owned writable parent fields
and two modeled children, performs the original three stores, and constructs a
parent resource with `HeapTree::Node(node, value, old(l.model), old(r.model))`.
Folding explicitly selects and consumes both children; no parent open handle is
required.

The focused [resource_tree_node_init mdtest](../../mdtests/resource_tree_node_init.md)
also checks reading a payload through this resource and constructing an empty
tree. Expansion, rechecking, and rejection tests cover wrong payloads or node
identities, swapped or missing links, unreadable child arguments, duplicate
child selection, and overlapping or reused ownership.

## Verified C rotations

`tree_rotate_left` consumes a tree whose root and right child are nonempty and
produces the returned tree with model `heap_rotate_left(old(t.model))`. This
exact structural transformation retains both node addresses and payloads and
all three arbitrary subtrees. `tree_rotate_right` mirrors it, with `heap_left`
as the accessor its contract needs to say that the root's left child is
nonempty.

Both proofs have the same shape. Two entry proof matches name the root and
pivot fields and close the empty cases from the preconditions. Unfolding
exposes the independent child resources; after the original C loads and stores,
explicit folds reconstruct the lower node and the returned pivot. No named open
handles are used, and the proof checks memory ownership as well as the model
transformation.

`heap_inorder` derives a `List<struct tree_node*>` from the model, visiting left
subtree, node, then right subtree. `heap_rotate_left_preserves_inorder` and
`heap_rotate_right_preserves_inorder` prove that rotation preserves that exact
list, each through a per-node helper and the standard library's
append-associativity theorem. Each contract therefore also guarantees
`heap_inorder(rotated.model) == heap_inorder(old(t.model))`: node identities,
their order, and their multiplicities are unchanged.

## Verified C depth-first search

The unchanged recursive `tree_contains` is verified against
`owns t: tree_at(root);` with `ensures t.model == old(t.model);` and the
unguarded `ensures result == heap_member(old(t.model), target);`.
The proof matches the entry model, unfolds the root in the nonempty case,
spells the two C `if` statements with `branch`, hands each recursive call the
matching child instance through the call binder map, and refolds the root from
the returned children on every path. Recursion therefore descends through a
matched, modeled resource without losing or duplicating any subtree.

The membership guarantee is where the model's identity payload earns its place.
`heap_member` tests `node == target` against the payload, while the C tests the
address `root == target`; `tree_at` states `fact p == identity`, and the proof
turns that into `node == target` with

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

`tree_contains` declares no `produces` binder, so this `let` binds `found_left`
to the call's scalar result instead of to a produced instance. The name is then
usable on either side of the `branch` that spells the C `if`: the then arm
combines `found_left != 0` with the callee's
`found_left == heap_member(left_model, target)`, and the else arm combines
`found_left == 0` with the same guarantee. The final
`return tree_contains(root->right, target);` is named the same way, and `result`
is that value.

Structural termination is verified too. `decreases t;` names the contract's own
`owns t: tree_at(root)` binder, and the `HeapTree::Node` arm's `left` and
`right` children are the direct contained children each recursive call must
pass, so the measure is the modeled resource rather than a pointer or a counter.

## Verified C iterative walks

`tree_leftmost` and `tree_rightmost` are unchanged, and their contracts are the
zipper: the walk consumes the whole tree and produces a context and a focused
subtree at the node it stopped on.

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

A loop binder behaves like a callee contract for one instance: the head
consumes the enclosing owned instance whose family and arguments match and
gives it fresh fields, so the model the body sees is exactly what the
invariants say. The arguments are read where they are used, so
`owns t: tree_at(root);` names the subtree at whatever `root` holds.

One iteration is one proof:

1. `match t.model` inside `preserve` supplies the constructor the head's fresh
   model does not have. The `HeapTree::Empty` arm closes by `contradiction` on
   the invariant.
2. `unfold(t) as { left: l, right: rt }` takes the node apart into its three
   cells and the two child instances.
3. `fold(ctx_at(root->left), { model: Context::Left(root, value, right_model,
   ctx.model) }, { sibling: rt, up: ctx })` builds the new frame from the
   parent's cells, the untaken sibling, and the old frame. Both children are
   consumed by that fold, which is what makes the frame stack linear.
4. `step()` runs `root = root->left`.
5. `close_invariants()` rebinds `ctx` to the new frame and `t` to the left
   child by proved argument equality, and the structural measure sees a direct
   contained child of the instance the head held.

A `have` before each fold moves the `plug` equation forward: `plug` of the new
frame at the left submodel unfolds to `plug` of the old frame at the whole
node, which the invariant already equates with `old(t.model)`. A second `have`
restates it at the C local, since the fold names the frame's parent by the
cursor `root` while the arm named it `identity`.

Two arm-selection decisions carry the walk. `requires t.model !=
HeapTree::Empty` selects the `HeapTree::Node` arm at contract lowering, and
that arm supplies its own `fact p != 0`, so `if (root == 0)` is decided by
`step()` with no `branch`. The same decision runs backwards inside the loop:
the guard `root->left != 0` contradicts the `HeapTree::Empty` arm's
`fact p == 0`, so the child the unfold produces has model
`!= HeapTree::Empty`, which is the next iteration's invariant. After the loop
the guard is false, the same rule refutes the `HeapTree::Node` arm instead,
and because `Empty` carries no fields the equation `left_model ==
HeapTree::Empty` is published outright; that is the postcondition
`heap_left(sub.model) == HeapTree::Empty`.

Two focused negatives cover the frame:
[loop_decreases_rejects_unrelated_node](../../mdtests/loop_decreases_rejects_unrelated_node.md)
moves the cursor to a node of another tree the contract owns, so the back edge
has no `tree_at` at the new cursor at all, and
[loop_context_frame_refold_rejected](../../mdtests/loop_context_frame_refold_rejected.md)
folds a second frame from children the first frame already consumed.

## Pure theorems

The model half of the project stands on its own and is what the C contracts
cite.

- `heap_inorder` is the in-order identity list; `heap_left` and `heap_right`
  are the accessors the rotation contracts need.
- `heap_rotate_left` and `heap_rotate_right` are the model transformations, and
  `heap_rotate_left_preserves_inorder` and `heap_rotate_right_preserves_inorder`
  prove that each preserves `heap_inorder`, through a per-node helper and the
  standard library's `list_append_associative`.
- `heap_member` is the recursive `int32`-valued membership test, searching the
  node, then the left subtree, then the right one, in the order the C search
  uses. `heap_member_is_inorder_membership` proves
  `heap_member(tree, target) == list_contains(heap_inorder(tree), target)` by
  structural induction from `list_contains_append` and `list_contains_cons`, so
  membership in the model is exactly membership in the sequence the rotations
  preserve. `heap_member_nonzero_is_one` proves that a nonzero result is `1`,
  which is the range fact the C proof needs: the search only learns that a
  recursive call returned nonzero, while `heap_member` tests its left subtree
  with `heap_member(left, target) == 1`.
- `plug_top_frame`, `plug_left_frame`, and `plug_right_frame` each state one
  step of `plug`: taking one frame off the stack rebuilds one node. The walk
  proofs take that step inline with `unfold(plug(...))`; the theorems name it
  for a proof that cannot unfold in place.
- `plug_inorder_transport` is the theorem a fixup needs: if two subtrees have
  the same in-order sequence, so do the whole trees they sit in.

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
  `Node(parent, value, a, sibling)` and `Node(parent, value, b, sibling)`, not
  at `a` and `b`. The hypothesis is therefore instantiated at the complete
  parameter list, `ih(up, Node(...), Node(...))`, and its requirement at those
  arguments is established by the `have` just above the application. A
  hypothesis fixed at the theorem's own `a` and `b` has no applicable instance
  here.

The example-local generic `Tree<T>`, with `tree_size`, `tree_mirror`,
`tree_mirror_twice`, and `tree_mirror_preserves_size`, is a separate pure
exercise in structural induction over an arbitrary payload type. Mirroring is
not a C operation here; the theorems exist to keep the generic ADT path
covered, and they use the standard library's `Nat`, `nat_add`, and
`nat_add_commutative`.

## Negative rotation regressions

Three focused mdtests keep the model honest against rotations that are wrong in
a specific way, each with the same resource, contract, and proof script as the
passing [rotation_model_preserved](../../mdtests/rotation_model_preserved.md):

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

## Remaining

No function in `modeled_binary_tree.c` is left unverified, and no contract here
is partial. Three deliberate limits are worth naming:

- The walks state their stopping position structurally, as
  `heap_left(sub.model) == HeapTree::Empty` plus `plug(ctx.model, sub.model) ==
  old(t.model)`, rather than as a claim about `heap_inorder`. The sequence form
  follows from those two, and it is what the Linux traversals want; it is
  stated and verified on the rbtree model in
  [`mdtests/rb_first_last.md`](../../mdtests/rb_first_last.md), whose `rb_first`
  ends with `rb_list_starts_with(rb_inorder(old(t.model)), result) == 1`.
- This C has only a descending loop, so the descending structural measure is
  the only one it exercises. The ascending shape is
  [`mdtests/loop_ascending_walk_to_root.md`](../../mdtests/loop_ascending_walk_to_root.md)
  and its rbtree form is
  [`mdtests/rb_ascending_walk_to_root.md`](../../mdtests/rb_ascending_walk_to_root.md);
  the third shape
  [`issues/structural-loop-termination.md`](../../issues/structural-loop-termination.md)
  asks for, a loop that rotates locally and then continues at a strict
  ancestor, has no fixture yet.
- The tree is unbalanced and has no colors, so nothing here claims a balance or
  height invariant. That is the rbtree's job.

This example is the scaffold: it fixes the shapes — the matched modeled
resource, the context frame, `plug`, the loop binders, the structural
measure — on C small enough to read in one sitting. The red-black work
continues on verbatim Linux bodies in the `rb_*` mdtests, with
[`mdtests/rb_at_link_helpers.md`](../../mdtests/rb_at_link_helpers.md),
[`mdtests/rb_ctx_change_child.md`](../../mdtests/rb_ctx_change_child.md),
[`mdtests/rb_first_last.md`](../../mdtests/rb_first_last.md),
[`mdtests/rb_replace_node.md`](../../mdtests/rb_replace_node.md), and
[`mdtests/rb_ascending_walk_to_root.md`](../../mdtests/rb_ascending_walk_to_root.md)
as the current front, and its pure library is
[`examples/rbtree-model`](../rbtree-model/README.md). The plan for the rest is
[`issues/recursive-structure-models.md`](../../issues/recursive-structure-models.md).
