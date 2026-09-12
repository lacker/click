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
them. [Frame-level insert fixup](#frame-level-insert-fixup) below restates each
case as a step of the fixup loop, with the table of which theorem a C proof
applies in which branch.

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

## Colors as summaries

Three small pure functions turn a node's own color into the summaries the
context predicate threads, so that no proof has to case-split on a color a
constructor has already fixed:

- `color_black(color)` is 1 for `Black` and 0 for `Red`.
  `rb_root_black_is_color_black` and `color_black_of_rb_color` bridge it to
  `rb_root_black` in both directions, because `rewrite` only replaces its
  left-hand side and a goal needs whichever orientation it already mentions.
- `frame_black_height(color, bh)` is the black height of a node of that color
  whose left subtree has black height `bh`; `black_height_node_frame` is that
  equation at a node, and `frame_black_height_red`/`_black` reduce it at a
  literal color.
- `node_color_ok(color, left_color, right_color)` is the red-child condition on
  its own: 1 for a black node, and for a red node 1 exactly when both children
  are black or empty. `is_rb_node_from_parts` builds `is_rb` at a node from
  `is_rb` of the parts, equal black heights and `node_color_ok`, and
  `is_rb_node_colors` recovers `node_color_ok` from `is_rb`.
  `node_color_ok_weaken_left` and `_weaken_right` replace one child's color by
  `Black`, which is the weakening the insert cursor needs.

Two shape rules govern these bodies, both consequences of what
`normalize() using` will reduce.

First, the flags are `Color`-typed rather than `int32`. A test `if flag == 1`
on a bare `int32` parameter unfolds to a single opaque bitvector operation that
no listed premise decides, exactly as gap 45 records for a raw pointer test;
`if color_black(flag) == 1` is a pure-call condition a premise does decide.

Second, every `if` in a new definition has **constant** branches. Reduction of
a decided `if` produces its branch, and a branch that is itself a call leaves a
term `normalize` cannot compare with 1. `is_rb`'s own red arm returns
`rb_root_black(right)`, so `is_rb_red_node_value` first states that branch as an
equation and `is_rb_red_node_right_child_is_black` rewrites through it. The new
color functions avoid the detour by ending every path in 0 or 1; `ctx_rb`'s
recursive branch below cannot, and pays for it with a `_value` lemma per frame.

## The context-level red-black predicate

`ctx_rb(ctx, bh, focus_color)` is 1 when the frames around the focus are
red-black **given** a focus that is itself a red-black subtree of black height
`bh` whose root has color `focus_color`. The focus is not an argument: two
subtrees with the same black height and root color plug into the same context
equally well, which is what a fixup step needs, since each step replaces the
focus and leaves the frames alone.

```click
function ctx_rb(ctx: Context, bh: Nat, focus_color: Color) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => if color_black(focus_color) == 1 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if is_rb(sibling_model) == 1 {
                if bh == black_height(sibling_model) {
                    if node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 {
                        ctx_rb(up_model, frame_black_height(color, bh), color)
                    } else { 0 }
                } else { 0 }
            } else { 0 },
        Context::Right(...) => /* mirror: the focus is the right child */
    }
}
```

Each frame contributes exactly its own facts: the sibling is red-black, the
sibling's black height equals the focus's, the frame node's color is compatible
with both children's colors, and the rest of the context holds around the node
this frame builds, whose black height is `frame_black_height(color, bh)` and
whose root color is `color`. `Top` contributes the root-is-black rule. Nothing
in a frame mentions the focus except through `bh` and `focus_color`.

The payoff is

```click
theorem plug_rb_from_ctx_rb(ctx: Context, sub: RbTree) {
    requires is_rb(sub) == 1;
    requires ctx_rb(ctx, black_height(sub), rb_color(sub)) == 1;

    ensures is_rb_root(plug(ctx, sub)) == 1;
}
```

proved by induction on the context with A16's generalized `ih`, instantiated at
the focused subtree one frame up, `RbTree::Node(identity, grandparent, color,
sub, sibling_model)`. `is_rb_root_from_parts`, `is_rb_root_is_rb` and
`is_rb_root_root_black` are the matching construction and decomposition lemmas
for `is_rb_root` itself.

The `Left` arm writes its height test as `bh == black_height(sibling_model)`
and the `Right` arm as `black_height(sibling_model) == bh`. The orientation is
not cosmetic: each destructor hands its equation straight to
`is_rb_node_from_parts`, whose `black_height(left) == black_height(right)`
premise puts the focus on the left in one arm and the sibling on the left in
the other. `rewrite` replaces only the left-hand side of an equality it already
matches, so `nat_eq_symmetric` and `nat_eq_transitive` are the two one-line
`Nat` lemmas the case proofs use wherever the orientation cannot be chosen in
advance.

`ctx_rb_top`, `ctx_rb_left_sibling`, `_left_height`, `_left_colors`, `_left_up`
and their right mirrors take the predicate apart one frame at a time;
`ctx_rb_top_frame`, `ctx_rb_left_frame` and `ctx_rb_right_frame` build a frame
back up. Each `_up` destructor goes through a `_value` lemma that states the
frame's own value as an equation, because the recursive call is not a constant
branch. `ctx_rb_left_red_up`, `ctx_rb_left_black_up` and their mirrors are the
two specializations a fixup uses: with the frame's color a literal,
`frame_black_height` has already reduced to `bh` or `Nat::Succ(bh)`.

### The insert cursor: one permitted red-red violation

```click
function ctx_almost_rb_insert(ctx: Context, bh: Nat) -> int32 {
    ctx_rb(ctx, bh, Color::Black)
}
```

Evaluating the context as if the focus were black exempts exactly the two
places a frame reads the focus's color: the bottom frame's red-child test and
`Top`'s root-is-black test. That is precisely the Linux insert invariant. The
whole tree is red-black except for at most one red-red edge, between the cursor
and its parent, and a red cursor that has reached the root is repaired by
blackening it. Every frame above the bottom one is still checked in full, so
the predicate permits one violation and no more.

The loop invariant `__rb_insert` wants is therefore two clauses:

```click
is_rb(sub.model) == 1
ctx_almost_rb_insert(ctx.model, black_height(sub.model)) == 1
```

`ctx_rb_weaken_to_almost` is the weakening (a context good for any focus color
is good for a black one); `ctx_almost_rb_insert_holds` and
`ctx_almost_rb_insert_black_focus` fold and unfold the name.

## Frame-level insert fixup

The five model functions above rewrite the three-level subtree at the
grandparent. The theorems in this section restate each case as a step of the
loop: the hypothesis is the loop invariant instantiated at that case's frame
shape, and the conclusion is either the next iteration's invariant or the exit
claim `is_rb_root(plug(...)) == 1`. A C proof unfolds its instances down to the
case shape and applies one theorem; it never rebuilds `is_rb` or
`almost_rb_insert` from the parts by hand.

| Fixup case | C branch | cursor frames | theorem | conclusion |
| --- | --- | --- | --- | --- |
| cursor is the root | `!parent` | `Context::Top` | `ctx_insert_root_exit` | exit |
| black parent | `rb_is_black(parent)` | one `Left` frame, `Color::Black` | `ctx_black_frame_left_restores` then `ctx_insert_black_parent_exit` | exit |
| black parent, mirror | `rb_is_black(parent)` | one `Right` frame, `Color::Black` | `ctx_black_frame_right_restores` then `ctx_insert_black_parent_exit` | exit |
| uncle red | case 1, `parent != tmp` | parent is the grandparent's left child | `ctx_insert_case1_left` | next iteration |
| uncle red, mirror | case 1, `parent == tmp` | parent is the grandparent's right child | `ctx_insert_case1_right` | next iteration |
| uncle black, inner | case 2 then 3 | `Right` frame inside a `Left` frame | `ctx_insert_case2_left` | exit |
| uncle black, inner, mirror | case 2 then 3 | `Left` frame inside a `Right` frame | `ctx_insert_case2_right` | exit |
| uncle black, outer | case 3 | `Left` frame inside a `Left` frame | `ctx_insert_case3_left` | exit |
| uncle black, outer, mirror | case 3 | `Right` frame inside a `Right` frame | `ctx_insert_case3_right` | exit |

The two uncle-red theorems are stated one level higher than the others, at the
parent's subtree rather than the cursor's, because Linux's case 1 does not care
whether the cursor is the parent's inner or outer child.
`ctx_insert_cursor_left_parent` and `ctx_insert_cursor_right_parent` are the
bridge: from `is_rb(sub) == 1` and the cursor's own frame they produce
`almost_rb_insert` at the parent's subtree, the parent's black height, the
sibling's blackness, and the grandparent frame's `ctx_rb(up_g, _, Color::Red)`,
which is exactly `ctx_insert_case1_*`'s hypothesis. Each case-1 theorem then
delivers three `ensures`: the recolored grandparent subtree is fully red-black,
its black height is one more than the parent's subtree's, and the context two
frames up satisfies `ctx_almost_rb_insert` at that height. Its root is red,
which is the next iteration's cursor color; `rb_insert_fix_recolor_root_is_red`
states that separately, and `rb_insert_fix_recolor_shape`,
`rb_insert_fix_outer_left_shape` and `rb_insert_fix_outer_right_shape` are the
unconditional equations that name each case function's result.

All six case theorems spell the grandparent's frame color as the literal
`Color::Black`, which the Linux code never tests: a red parent forces a black
grandparent, and `node_color_ok_red_focus_is_black` is that step, deriving
`color == Color::Black` from a frame whose focus is red.

The four uncle-black theorems close the loop outright. Their hypotheses are
`is_rb` at the cursor, the uncle's root being black, and the two-frame
`ctx_rb`; their conclusion applies `plug_rb_from_ctx_rb` at the frame above the
grandparent, so the C proof gets `is_rb_root(plug(up2, ...)) == 1` in one step.
The black heights are stated in reduced form — the cursor is red, so its black
height is that of its left child — which saves the C proof one rewrite at the
point where the model is already destructured.

Sequence preservation is separate and unconditional.
`plug_insert_fix_recolor_inorder`, `plug_insert_fix_outer_left_inorder`,
`plug_insert_fix_outer_right_inorder`, `plug_insert_fix_inner_left_inorder`,
`plug_insert_fix_inner_right_inorder` and `plug_recolor_inorder` say that
applying a case function (or blackening the root) under any context leaves
`rb_inorder(plug(...))` unchanged; each is the case's own in-order theorem
transported by `plug_inorder_transport`. The two inner theorems cover the whole
inner-then-outer composition, which is what the C performs between one loop
head and its exit.

Finally, `plug_left_frame` and `plug_right_frame` unfold one frame, and
`plug_left_in_left`, `plug_right_in_left`, `plug_left_in_right` and
`plug_right_in_right` rewrite a two-frame `plug` into `plug(up2, ...)` at the
grandparent-level shape the case theorems name. A fixup proof uses one of these
to move between the loop invariant's `plug(ctx.model, sub.model)` and the case
shape, with no induction of its own.

## Standard library

The example adds `list_tail` locally rather than to `stdlib/prelude.click`; it
is used only here. Everything else comes from the prelude: `List`, `Nat`,
`list_append`, `list_contains`, `list_append_associative`,
`list_contains_append`, and `list_contains_cons`.
