# Red-Black Tree Model

This project is the pure Click library for the Linux rbtree proofs planned in
[`recursive-structure-models.md`](../../issues/recursive-structure-models.md)
(decisions D1, D3, and D10). It contains no C and no resource:
`rbtree_model.click` has no `verifying` line, and `click verify` accepts a
sidecar that declares only specification values. The later packages attach
`rb_at(p)` and `ctx_at(child, root)` to these definitions, so every claim a C
contract will make about colors, black height, parent links, or the in-order
node sequence is proved here once.

Run `cargo run --bin click -- verify examples/rbtree-model` from the repository
root. The example is also checked by `scripts/check.sh`.

Linux rbtree stores no keys, so the model carries node identity rather than
ordering. `struct rb_node*` is a payload type only: the model grants no
ownership and never converts a pointer to an integer.

```click
spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, struct rb_node*, Color, RbTree, Context),
}
```

`RbTree::Node` is `(identity, parent, color, left, right)` and
`Context::Left`/`Context::Right` are
`(identity, grandparent, color, sibling_model, up_model)`: exactly the shapes
C1b's fixtures use (`mdtests/rb_first_last.md`,
`mdtests/rb_at_link_helpers.md`). The model is keyed by node with the parent in
the payload because `rb_first(root)` and `rb_next(node)` have no C local naming
the focused node's parent, so a `rb_at(p, parent)` resource could not be named
in their contracts (gap 35).

Because the parent is part of the model, every model function that moves a node
also states what happens to the parent payloads, the way the C rotation writes
the parent words. `rb_reparent(tree, new_parent)` replaces the root's parent
payload and is the only place a parent payload changes.
`rb_reparent_preserves_inorder`, `rb_reparent_preserves_is_rb`,
`rb_reparent_preserves_black_height`, and
`rb_reparent_preserves_rb_root_black` say that no other summary sees it, so the
ported proofs carry the re-parenting through without new inductions.

## In-order sequence and membership

`rb_inorder` derives the `List<struct rb_node*>` of node identities in left,
node, right order, exactly as `heap_inorder` does in
[`examples/modeled-binary-tree`](../modeled-binary-tree/README.md).
`rb_member` is the recursive membership test on the model, and
`rb_member_is_inorder_membership` proves it equals
`list_contains(rb_inorder(tree), target)`. `rb_left`, `rb_right`, and
`rb_color` are the accessors a C contract needs to state that a child is
nonempty or a node is red.

## Rotations and recoloring

`rb_rotate_left` and `rb_rotate_right` are the standard structural rotations at
the root. Each rotated node keeps its own color, exactly as the C rotation
does; recoloring is a separate step. A rotation now also re-parents the three
nodes whose parent word the C rotation writes: the pivot takes the root's old
parent payload, the demoted root takes the pivot, and the middle subtree's root
is re-parented to the demoted root with `rb_reparent`. The root's old parent is
read from its own payload, so no extra argument is needed.
`rb_rotate_left_preserves_inorder` and `rb_rotate_right_preserves_inorder`
prove that both preserve the in-order list exactly, through per-node helpers,
`rb_reparent_preserves_inorder`, and the standard library's append
associativity.

`rb_recolor(tree, color)` replaces the root's color, and `rb_recolor_left` and
`rb_recolor_right` recolor one child's root. `rb_rotate_left_at_left` and
`rb_rotate_right_at_right` rotate one child. Each has an in-order preservation
theorem, so the composed fixup steps below inherit sequence preservation
without a new induction.

## Parent consistency

`rb_parent_consistent(t, p)` is 1 when every node of `t` carries its own
parent as its parent payload and `t`'s root carries `p`. `Empty` is consistent
for any `p`, which is what a null child needs.

```click
function rb_parent_consistent(t: RbTree, p: struct rb_node*) -> int32
    decreases t
{
    match t {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if rb_parent_consistent(left, node) == 1 {
                if rb_parent_consistent(right, node) == 1 {
                    if rb_node_is(parent, p) == 1 { 1 } else { 0 }
                } else { 0 }
            } else { 0 },
    }
}
```

`rb_parent_is(tree, p)` is C1b's shallow spelling, unchanged, and
`rb_parent_is_node_is` bridges it to `rb_node_is(parent, p)`, the scalar
pointer test the recursive predicate uses. Two other spellings of the same
body do not work. A raw `if parent == p` as the **outermost** test leaves the
unfolded body one opaque bitvector operation, so
`normalize() using { parent == p; ... }` cannot select a branch; and a bare
`rb_node_is(parent, p)` as the arm's **value** rather than as a condition
leaves a destructor's goal an opaque operation that the premise does not
match. Every test is therefore an `if <int32 test> == 1` with constant
branches, which is the shape `is_rb` already uses.

- `rb_node_is_equal` and `rb_node_is_same` bridge a raw pointer equality and
  the scalar test in both directions, which is how a C proof turns a link fact
  such as `parent->rb_left == child` into `rb_node_is(_, _) == 1`;
  `rb_node_is_reflexive` is the case a fold at a freshly written parent word
  needs.
- `rb_parent_consistent_node` builds the predicate at a node from
  `rb_node_is(parent, p) == 1` and the two children's consistency;
  `rb_parent_consistent_node_left`, `_node_right`, and `_node_parent` take it
  apart again; `rb_parent_consistent_empty` is the base case.
- `rb_reparent_parent_consistent_at(tree, p, new_parent, q)` re-parents a
  consistent tree to `new_parent` and states the result at any `q` the frame
  proves equal to `new_parent`; `rb_reparent_parent_consistent` is its
  reflexive special case.
- `rb_rotate_left_parent_consistent` and `rb_rotate_right_parent_consistent`
  (with their per-node forms `rb_rotate_*_node_parent_consistent`) and
  `rb_recolor_parent_consistent` are the preservation theorems at a root whose
  parent is `p`.
- `rb_leaf(node, parent)` is a fresh red childless node;
  `rb_leaf_parent_consistent`, `rb_insert_leaf_left_parent_consistent`, and
  `rb_insert_leaf_right_parent_consistent` say that linking a fresh leaf into
  an empty child slot preserves consistency, which is `rb_link_node`'s model
  step.
- `rb_remove_min_parent_consistent` (through the per-node
  `rb_remove_min_node_parent_consistent`) and
  `rb_erase_two_child_splice_parent_consistent` are the splice lemmas'
  consistency halves.

## Red-black invariants

Predicates are written as `int32`-valued pure functions returning 1 or 0,
because a Click `predicate` has no `decreases` clause and cannot recurse.

- `black_height(tree)` counts the black nodes on the leftmost path as a `Nat`.
  `Empty` has black height `Nat::Zero`.
- `rb_root_black(tree)` is 1 for `Empty` and for a black root, 0 for a red
  root; empty subtrees count as black, which is what the red-child condition
  needs.
- `is_rb(Node(_, _, c, l, r))` is 1 when `is_rb(l)`, `is_rb(r)`,
  `black_height(l) == black_height(r)`, and, if `c` is `Red`, both children
  have black or empty roots. A black root is deliberately **not** required:
  Linux's `rb_insert_color` blackens the root only at the end.
- `is_rb_root(tree)` is `is_rb(tree)` plus a black root. This is the whole-tree
  invariant an entry point establishes.

None of these reads a parent payload, so the four
`rb_reparent_preserves_*` theorems are what lets a re-parented subtree keep
its color and height summaries.

`is_rb_black_node` and `is_rb_red_node` build `is_rb` at a node from its parts;
`is_rb_node_left`, `is_rb_node_right`, `is_rb_node_black_heights`, and
`is_rb_red_node_children_are_black` take it apart again. `black_height_*_node`
and `rb_root_black_*_node` compute the two summaries at a node of known color.

### Fixup invariants

Both fixup predicates follow the standard CLRS/Okasaki treatment, weakened at
exactly one point, which is the cursor.

`almost_rb_insert(Node(_, _, c, l, r))` requires `is_rb(l)`, `is_rb(r)`, and
`black_height(l) == black_height(r)`, and drops only the red-child condition at
the root. This is Okasaki's "infrared" tree: both subtrees are proper
red-black trees of equal black height, and the root may be red with a red
child, which is the single red-red violation `rb_insert_color` carries upward.
`almost_rb_insert(Empty)` is 1.

`almost_rb_erase(tree, required)` is 1 when `is_rb(tree)` holds and
`Nat::Succ(black_height(tree)) == required`: the cursor subtree is itself a
proper red-black tree, but it carries one fewer black node than its context
needs. `required` is the black height the sibling supplies, so this is the
CLRS "doubly black" cursor expressed without a second color. A deficit
predicate on the subtree alone cannot mention the sibling, so the required
height is an explicit parameter.

`is_rb_is_almost_rb_insert` shows the weakening is a weakening.
`almost_rb_insert_black_root_is_rb` closes the invariant back up when the
cursor is black, and `rb_blacken_root_restores_rb` is the terminal step of
`rb_insert_color`: blackening the root of an almost-red-black tree yields
`is_rb_root == 1`. `almost_rb_erase_node`, `almost_rb_erase_is_rb`, and
`almost_rb_erase_black_deficit` are the matching construction and
decomposition lemmas for the erase cursor.

## Insert fixup steps

Each standard case is a pure function on the local three-level subtree rooted
at the grandparent, spelled as a composition of the rotation and recolor
primitives rather than as a new pattern match:

| Case | Model function |
| --- | --- |
| uncle red | `rb_insert_fix_recolor` |
| uncle black, inner, left | `rb_insert_fix_inner_left` |
| uncle black, inner, right | `rb_insert_fix_inner_right` |
| uncle black, outer, left | `rb_insert_fix_outer_left` |
| uncle black, outer, right | `rb_insert_fix_outer_right` |

Because they are compositions, each one's in-order preservation theorem holds
for **every** tree, not only for the case shape, and follows from the
primitives' theorems: `rb_insert_fix_recolor_preserves_inorder` and its four
siblings. The rebalancing never changes the node sequence.

The invariant theorems are stated on the explicit case shape, with each node's
parent payload spelled as the node above it and the grandparent's own parent
named `above`, and with the parts' `is_rb`, `rb_root_black`, and
`black_height` hypotheses spelled out; those are exactly what
`almost_rb_insert` at the parent unfolds to. The rotating cases move one
subtree across the rotation, so the case result names it as
`rb_reparent(_, _)` and the proof carries its summaries through the
`rb_reparent_preserves_*` theorems.

- `rb_insert_fix_recolor_propagates`: recoloring a black grandparent's two red
  children black and the grandparent red leaves `almost_rb_insert` holding at
  the grandparent, which is the violation moving one level up. One theorem
  covers both mirrors, because the transformation does not depend on which
  child holds the red-red pair. Recoloring moves no node, so no payload
  changes.
- `rb_insert_fix_outer_left_restores` and
  `rb_insert_fix_outer_right_restores`: the outer case rotates and swaps the
  parent's and grandparent's colors, and the result satisfies `is_rb`.
- `rb_insert_fix_inner_left_becomes_outer` and its right mirror: the inner
  case rotates the parent and produces exactly the outer shape, with the
  cursor's inner child re-parented onto the old parent.
- `rb_insert_fix_inner_left_restores` and its right mirror: the inner rotation
  followed by the outer step satisfies `is_rb`.

Both mirrors are written out. Per decision D9 there is no proof reuse across
them.

## Erase: splice lemmas

`rb_remove_min(tree)` removes the leftmost node; `rb_min_list(tree)` is the
leftmost identity as a one-element list, `Nil` for `Empty`. When the leftmost
node is the root, its right subtree takes its place *and its parent*, so
`rb_remove_min` re-parents that subtree exactly as `rb_erase` writes the
spliced child's parent word. A pure function may not return a bare pointer
type, so the successor's identity is named through a list rather than returned
directly: a proof that needs it carries the hypothesis
`rb_min_list(right) == Cons(successor, Nil)`, which a C proof establishes from
its descent.

- `rb_min_list_splits_inorder`: `rb_inorder(tree)` is
  `list_append(rb_min_list(tree), rb_inorder(rb_remove_min(tree)))` for every
  tree, proved by structural induction through the per-node
  `rb_min_list_splits_node`.
- `rb_remove_min_drops_head` and `rb_remove_min_is_inorder_tail`: with the
  successor named, the entry list is `Cons(minimum, ...)` and
  `rb_inorder(rb_remove_min(tree)) == list_tail(rb_inorder(tree))`.
- `rb_inorder_node_splits`: the entry sequence of a node is
  `A ++ [node] ++ B`, where `A` and `B` are its subtrees' sequences.
- `rb_erase_no_left_child` and `rb_erase_no_right_child`: erasing a node with
  at most one child replaces `A ++ [node] ++ B` by the surviving child's
  sequence, which is `A ++ B` with one of the two empty.
- `rb_erase_two_child_splice`: splicing the in-order successor into the erased
  node's position, with the erased node's parent and both children re-parented
  onto the successor, yields `list_append(rb_inorder(left), rb_inorder(right))`,
  which is the entry sequence `A ++ [erased] ++ B` with exactly the erased
  identity dropped at its position.

Removal is stated as this pair of append equations rather than as
`list_remove_first(rb_inorder(t), node)`. A `list_remove_first` would need a
conditional that returns a list, and a Click `if` expression may not produce an
algebraic value: `function f(...) -> List<T> { if c { xs } else { ys } }` is
rejected with "returns List<...>, but its body is not algebraic". The append
form is also stronger, because it fixes the removed element's position instead
of relying on the identity's absence from the prefix.

## Context and `plug`

`plug(ctx, sub)` rebuilds the whole model from a context and the focused
subtree, mirroring the scaffold's `plug` in
[`examples/modeled-binary-tree`](../modeled-binary-tree/README.md) on the
five-payload node. `plug_inorder_transport` is the scaffold theorem on
`RbTree`: two subtrees with the same in-order list plug into whole trees with
the same in-order list, proved by induction on the context with A16's
generalized `ih`, which instantiates the focused subtrees at each frame.

`ctx_consistent(ctx, sub, root_parent)` is parent consistency for the frames
around `sub`: `Top` asks that `sub` is consistent for `root_parent`, and a
`Left` or `Right` frame asks that `sub` and the sibling are consistent for the
frame's own node and that the rest of the context is consistent around the node
the frame builds. `plug_parent_consistent_transport` is then

```click
requires ctx_consistent(ctx, sub, root_parent) == 1;
ensures rb_parent_consistent(plug(ctx, sub), root_parent) == 1;
```

The predicate carries the focused subtree instead of naming the focus's parent
as a separate argument. Both spellings state the same thing, but the
parent-as-argument form needs to move `rb_parent_consistent(sub, focus_parent)`
to `rb_parent_consistent(sub, identity)` across a proved pointer equality, and
no simple tactic derives that step: with `a == b` and `b == c` as premises,
`normalize() using { a == b; b == c; }` on the goal `a == c` reports "goal did
not normalize to true using the listed conditions" over the kernel goal
`v100000*4 = v100002*4`, `rewrite` refuses a bare pointer variable with
"`rewrite` equality does not occur in the current goal", and only the smart
`simp()` closes it. Carrying the subtree avoids the step entirely, and it is
also the shape a C loop invariant wants, since the loop already holds both the
frame and the focused subtree while no C local names the focus's parent.

`ctx_consistent_top`, `ctx_consistent_left_focus`, `_left_sibling`,
`_left_up`, and their right mirrors take the predicate apart one frame at a
time; `ctx_consistent_top_frame`, `ctx_consistent_left_frame`, and
`ctx_consistent_right_frame` build a frame back up, which is the step a descent
loop takes when it pushes a frame.

## Standard library

The example adds `list_tail` locally rather than to `stdlib/prelude.click`; it
is used only here. Everything else comes from the prelude: `List`, `Nat`,
`list_append`, `list_contains`, `list_append_associative`,
`list_contains_append`, and `list_contains_cons`.
