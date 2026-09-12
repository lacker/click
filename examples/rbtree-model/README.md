# Red-Black Tree Model

This project is the pure Click library for the Linux rbtree proofs planned in
[`recursive-structure-models.md`](../../issues/recursive-structure-models.md)
(decisions D1 and D10). It contains no C and no resource: `rbtree_model.click`
has no `verifying` line, and `click verify` accepts a sidecar that declares
only specification values. The later packages attach `rb_at(p, parent)` and the
context resource to these definitions, so every claim a C contract will make
about colors, black height, or the in-order node sequence is proved here once.

Run `cargo run --bin click -- verify examples/rbtree-model` from the repository
root. The example is also checked by `scripts/check.sh`.

Linux rbtree stores no keys, so the model carries node identity rather than
ordering. `struct rb_node*` is a payload type only: the model grants no
ownership and never converts a pointer to an integer.

```click
spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, Color, RbTree, RbTree),
}
```

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
does; recoloring is a separate step. `rb_rotate_left_preserves_inorder` and
`rb_rotate_right_preserves_inorder` prove that both preserve the in-order list
exactly, through per-node helpers and the standard library's append
associativity.

`rb_recolor(tree, color)` replaces the root's color, and `rb_recolor_left` and
`rb_recolor_right` recolor one child's root. `rb_rotate_left_at_left` and
`rb_rotate_right_at_right` rotate one child. Each has an in-order preservation
theorem, so the composed fixup steps below inherit sequence preservation
without a new induction.

## Red-black invariants

Predicates are written as `int32`-valued pure functions returning 1 or 0,
because a Click `predicate` has no `decreases` clause and cannot recurse.

- `black_height(tree)` counts the black nodes on the leftmost path as a `Nat`.
  `Empty` has black height `Nat::Zero`.
- `rb_root_black(tree)` is 1 for `Empty` and for a black root, 0 for a red
  root; empty subtrees count as black, which is what the red-child condition
  needs.
- `is_rb(Node(_, c, l, r))` is 1 when `is_rb(l)`, `is_rb(r)`,
  `black_height(l) == black_height(r)`, and, if `c` is `Red`, both children
  have black or empty roots. A black root is deliberately **not** required:
  Linux's `rb_insert_color` blackens the root only at the end.
- `is_rb_root(tree)` is `is_rb(tree)` plus a black root. This is the whole-tree
  invariant an entry point establishes.

`is_rb_black_node` and `is_rb_red_node` build `is_rb` at a node from its parts;
`is_rb_node_left`, `is_rb_node_right`, `is_rb_node_black_heights`, and
`is_rb_red_node_children_are_black` take it apart again. `black_height_*_node`
and `rb_root_black_*_node` compute the two summaries at a node of known color.

### Fixup invariants

Both fixup predicates follow the standard CLRS/Okasaki treatment, weakened at
exactly one point, which is the cursor.

`almost_rb_insert(Node(_, c, l, r))` requires `is_rb(l)`, `is_rb(r)`, and
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

The invariant theorems are stated on the explicit case shape, with the parts'
`is_rb`, `rb_root_black`, and `black_height` hypotheses spelled out; those are
exactly what `almost_rb_insert` at the parent unfolds to.

- `rb_insert_fix_recolor_propagates`: recoloring a black grandparent's two red
  children black and the grandparent red leaves `almost_rb_insert` holding at
  the grandparent, which is the violation moving one level up. One theorem
  covers both mirrors, because the transformation does not depend on which
  child holds the red-red pair.
- `rb_insert_fix_outer_left_restores` and
  `rb_insert_fix_outer_right_restores`: the outer case rotates and swaps the
  parent's and grandparent's colors, and the result satisfies `is_rb`.
- `rb_insert_fix_inner_left_becomes_outer` and its right mirror: the inner
  case rotates the parent and produces exactly the outer shape.
- `rb_insert_fix_inner_left_restores` and its right mirror: the inner rotation
  followed by the outer step satisfies `is_rb`.

Both mirrors are written out. Per decision D9 there is no proof reuse across
them.

## Erase: splice lemmas

`rb_remove_min(tree)` removes the leftmost node; `rb_min_list(tree)` is the
leftmost identity as a one-element list, `Nil` for `Empty`. A pure function may
not return a bare pointer type, so the successor's identity is named through a
list rather than returned directly: a proof that needs it carries the
hypothesis `rb_min_list(right) == Cons(successor, Nil)`, which a C proof
establishes from its descent.

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
  node's position yields `list_append(rb_inorder(left), rb_inorder(right))`,
  which is the entry sequence `A ++ [erased] ++ B` with exactly the erased
  identity dropped at its position.

Removal is stated as this pair of append equations rather than as
`list_remove_first(rb_inorder(t), node)`. A `list_remove_first` would need a
conditional that returns a list, and a Click `if` expression may not produce an
algebraic value: `function f(...) -> List<T> { if c { xs } else { ys } }` is
rejected with "returns List<...>, but its body is not algebraic". The append
form is also stronger, because it fixes the removed element's position instead
of relying on the identity's absence from the prefix.

## Standard library

The example adds `list_tail` locally rather than to `stdlib/prelude.click`; it
is used only here. Everything else comes from the prelude: `List`, `Nat`,
`list_append`, `list_contains`, `list_append_associative`,
`list_contains_append`, and `list_contains_cons`.
