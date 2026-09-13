# `rb_insert_color` and `__rb_insert`: the fixup loop's exits

This is package C3 of
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md):
the unchanged Linux insert fixup, contracted over the node-keyed
`ctx_at(child, root)` frame and `rb_at(p)` subtree that
[`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md) and
[`rb_first_last.md`](rb_first_last.md) verify on. The C is verbatim: the
mainline `__rb_insert` with its `augment_rotate` callback parameter,
`rb_insert_color` calling it with `dummy_rotate`, and the `rbtree_augmented.h`
inline helpers `rb_set_parent_color`, `rb_red_parent`, `rb_parent`,
`__rb_change_child` and `__rb_rotate_set_parents`, with the header of
[`rb_parent_family.md`](rb_parent_family.md) extended by the `RB_RED`/`RB_BLACK`
colour macros, the `WRITE_ONCE` of
[`rb_ctx_change_child.md`](rb_ctx_change_child.md), and one-line definitions of
`likely`, `unlikely`, `__always_inline` and `true` that expand to what the
kernel's own headers expand them to.

The body parses in C0 as written. That is new: a declaration list writes one
`*` per declarator, so `struct rb_node *parent = rb_red_parent(node), *gparent,
*tmp;` used to stop at `expected local name, got '*'`, and the whole insert path
was out of reach before any proof could start;
[`c_local_declarator_pointer_stars.md`](c_local_declarator_pointer_stars.md) is
the rule that now accepts it. Nothing else in the function needed a translation:
`while (true)`, `!parent`, `tmp && rb_is_red(tmp)`, the statement-expression
`WRITE_ONCE`, the function-pointer parameter and the indirect call through it
all lower.

**The body's proof does not yet.** The fixup loop is `while (true)` with four
`break`s —
the root-blackening exit, the black-parent exit, and the two case-3 rotations —
and two `continue`s, the uncle-red recolours. The `loop` tactic now has a rule
for both: a `continue` is the back edge
([`loop_body_continue_back_edge.md`](loop_body_continue_back_edge.md)) and a
`break` is an exit joined into the loop's one successor
([`loop_body_break_exit.md`](loop_body_break_exit.md)). Each of this loop's four
`break`s writes a colour or rotates before leaving, so its exits reach four
different states — which used to be refused outright. They no longer are: the
exits are joined through the loop's declared binders, each given fresh fields
with the disjunction of what each exit said about them, which is decision D5
applied at the exit
([`loop_break_exit_binder_model_join.md`](loop_break_exit_binder_model_join.md)
is this loop's shape reduced to one colour, and
[`loop_break_exit_refold_join.md`](loop_break_exit_refold_join.md) is the
rotation-shaped refold).

Four smaller blockers stood in front of that one, and package A24 cleared them.
The one this fixture used to pin came before the loop tactic was reached at all:
the contract's own requirement `rb_color_bit(t.model) == 0` — the loop invariant
"node is red", which is what makes `rb_red_parent`'s untagging sound — made the
resource-derived loop frame fail to establish, with `named resource instance is
not owned`. That was the loop-frame pre-pass re-evaluating the contract's entry
transition at the frontier's start state rather than at the function's checked
entry state: the preamble unfolds `rb_at(node)` to read the inserted node's
parent word, so at the frontier `consumes t` named nothing. The frame belongs to
the contract and is now established where the contract begins.

The three the contract still shows:

- `decreases c;` now ranks this loop. The uncle-red cases set `node = gparent`,
  so the next frame is the context *above* the grandparent — `up.up` — and the
  measure accepts a strict contained descendant reached through the arms the
  body actually unfolded, rather than a direct child only
  ([`loop_decreases_strict_descendant.md`](loop_decreases_strict_descendant.md)).
- A pure function now takes the null constant where a `struct rb_node*`
  parameter is declared, so `ctx_holds`'s `Top` case is `rb_parent_is(sub, 0)`
  and the whole-tree `rb_tree_parent_consistent` is `rb_parent_consistent(t, 0)`
  rather than a copy of it written out at null
  ([`rb_pure_null_pointer_argument.md`](rb_pure_null_pointer_argument.md)).
- The produced instances are named through the root cell the context's `Top`
  frame owns, `ctx_at(root->rb_node, root)` and `rb_at(root->rb_node)`. A
  `produces` argument is the caller's view, so a parameter there means the value
  the caller passed, and `node` is one the body reassigns; `result` is the other
  spelling and this function is `void`. The root cell is read in the exit state
  and is the position the fixup links
  ([`rb_produces_through_the_root_cell.md`](rb_produces_through_the_root_cell.md)).

The loop's entry is now proved. The invariants do not follow from the contract
by `simp` alone: the contract says where the focused subtree sits in its frame,
`ctx_holds(c.model, t.model) == 1`, while the loop and the body talk about the C
local `parent` that `rb_red_parent` computed. The bridge is pure and it is in
this file. `rb_has_parent(sub, p)` says the focus is a node whose parent payload
is `p` — the `Empty` case is `0`, not `1`, so two frames that both hold the same
focus name the same node — and `ctx_holds` is restated on it.
`ctx_node_is_from_parent` then takes the contract's gluing requirement and
`rb_has_parent(t.model, node_parent)` to `ctx_node_is(c.model, node_parent) ==
1`, and `ctx_reroot_fixed` takes that to `c.model == ctx_reroot(c.model,
node_parent)`, which is the ascent shape
[`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md) carries. Both are
applied with `using`, because `apply`'s premise search does not find a pure fact
a `have` proved by rewriting through the arm's constructor
([`theorem_premise_search_names_the_premise.md`](theorem_premise_search_names_the_premise.md)).
`parent == node_parent` itself is one `simp`: the node is red by the contract,
so its parent word carries no tag and `rb_red_parent`'s cast is the payload.

Two orderings in that preamble are forced rather than chosen. A pure `have`
proved by `unfold` and `normalize` stops lowering once `parent == node_parent`
has been established, so every pure step comes first and only `simp` bridges
follow. The loop's in-order invariant names the entry tree through the entry
`match` arm's constructor rather than through `old(t.model)`. Both spell the
same tree: `old` on an instance the preamble unfolded and refolded before the
loop is the function-entry instance and lowers there too
([`loop_invariant_old_field_after_a_refold.md`](loop_invariant_old_field_after_a_refold.md)),
as it does on `c`, the context the preamble never unfolds. The arm's
constructor is the spelling this fixture keeps, because the arm bindings are
already what the case theorems are stated over.

What the fixture pins now is the body, one exit at a time. `preserve` is
written, and the frontier report says exactly how far it gets: **the
root-blackening `break` is complete**, and so is the black-parent one on both
context frames. That first exit is the whole shape in miniature — the
enclosing `if (!parent)` is a proof `if`, the write through `rb_set_parent_color`
needs `t` unfolded, and the `break` needs it folded again at the new model
`RbTree::Node(nid, 0, Color::Black, nleft, nright)`, which is a null parent and
a black colour bit. A `break` is an exit, so the invariants are not closed on
it; only the binders have to be owned.

**The black-parent `break` is complete too**, on both frame paths.
`Context::Top` is refuted for the frame by `parent != 0` against invariant 4,
so `c.model` is a `Left` or `Right` frame; `ctx_node_is_left_identity` and its
mirror take invariant 4 to `parent == cid`, which is what lets `unfold(c)` hand
the C spelling `parent->__rb_parent_color` the cells the frame owns at `cid`
(package A22's alias index). A proof `match` on the arm's own colour then
decides the guard `rb_is_black(parent)`: in the `Color::Black` arm the frame's
body fact `(parent->__rb_parent_color & 1) == color_bit(ccolor)` rewrites
through the arm's constructor to the concrete bit, and the frame's packed-word
fact carries that bit back into the whole word,
`parent->__rb_parent_color == address(cgp) + 1`, which is the spelling the
`step` at the guard decides on. The masked fact alone does not decide it; the
word does. The frame is refolded at its unchanged model before the `break`,
because a `break` owes the binders and nothing else.

That bridge did not work until the local `parent` had a layout.
`__rb_insert` is `static __always_inline`, and an inline body's kernel name
carries an `#inline:<source>` suffix, so the struct names of its automatic
locals were filed under a name no sidecar ever writes and
`parent->__rb_parent_color` lowered as a four-byte read of an eight-byte
member. Every spelling of the bridge failed differently because of it — a
`have` naming `parent` beside a pure call produced no path, and one naming the
arm binding `cid` produced a 64-bit fact that no `rewrite` could put into the
goal. `mdtests/inline_function_struct_pointer_local_layout.md` is the rule
that now keys those layouts by the source spelling.

The invariants are now stated in the frame-level form the pure library
consumes. The loop used to carry `almost_rb_insert(plug(c.model, t.model)) == 1`
and `ctx_root_black(c.model) == 1`, a claim about the whole plugged tree, while
every case theorem `examples/rbtree-model` proves for the fixup
(`ctx_insert_case1_left`, `ctx_insert_case2_left`, `ctx_insert_case3_left` and
their mirrors, `ctx_insert_black_parent_exit`, `ctx_insert_root_exit`) is stated
frame by frame over `ctx_rb(ctx, bh, focus_color)` and its `focus_color ==
Color::Black` specialization `ctx_almost_rb_insert(ctx, bh)`. The two clauses
are replaced by

```
requires is_rb(t.model) == 1;
requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
```

on both entry points and by the same pair as loop invariants. `is_rb(t.model)`
is the focused subtree being a proper red-black tree — which it is: the node the
caller inserted is a red leaf, and each recolour hands the cursor a red node
whose two children were just blackened. `ctx_almost_rb_insert(c.model, bh)` is
`ctx_rb(c.model, bh, Color::Black)`: every ancestor frame is well formed for a
focus of black height `bh`, *pretending the focus is black*, which is exactly
the one permitted violation — the focus is red and its parent may be red too.

The black height is not a loop-carried variable and not an existential. It is
`black_height(t.model)`, a pure function of the binder's own loop-carried model,
which is how C2c already spells the `bh` argument of every case theorem
(`ctx_insert_case1_left` concludes `ctx_almost_rb_insert(up2,
Nat::Succ(black_height(a)))` for the focus `a`). A `Nat` local would have to be
proved equal to it at every step; naming it directly costs nothing and keeps the
loop's state exactly the two instances.

This is a strengthening of the old requirement, not a weakening, and the
strengthened part is what the algorithm has always needed. `ctx_rb`'s `Top` case
demands `color_black(focus_color) == 1`, so `ctx_almost_rb_insert(c.model, bh)`
entails the old `ctx_root_black(c.model) == 1`; unfolding it down the spine
entails the old `almost_rb_insert(plug(c.model, t.model)) == 1`. What it adds is
per-frame black-height agreement with the sibling and the sibling's own
`is_rb`, which `almost_rb_insert` of the whole tree states only at the root.
`ctx_root_black` and `ctx_frame_root_black` are gone with it, and so is the
separate copy of the pure library this file used to carry: the whole of
[`examples/rbtree-model`](../examples/rbtree-model/README.md) is copied in
verbatim, since a fixture has no import.

Restating them cost no proof. `initialize` still closes by the same bridges,
and the root-blackening and black-parent `break`s are still complete, because a
`break` is an exit and owes the binders rather than the invariants.

The red-parent path then goes one frame further. The `Color::Red` arm of each
frame takes the colour-bit bridge in the other direction — the frame's colour
bit is `0`, so the parent's packed word is exactly `address(cgp)` — which is
what makes the inlined `rb_red_parent(parent)` cast sound and gives `gparent ==
cgp` without an untagging mask. Reading `gparent->rb_right` then needs
`Context::Top` refuted for the frame above, `cu`, and the restated invariant is
what refutes it: `ctx_almost_rb_insert(c.model, black_height(t.model)) == 1`
with a red frame gives `ctx_rb(cu.model, black_height(t.model), Color::Red) == 1`
by `ctx_rb_left_red_up`, and `ctx_rb` at `Context::Top` with a red focus is `0`.
`ctx_rb_red_focus_not_top` is that one line as a pure theorem, and it is stated
here rather than derived in place because a constructor arm may be closed by
`contradiction` only when the `contradiction` is the arm's sole tactic (see
below). With `cu.model != Context::Top` in hand the `Top` arm closes, `unfold(cu)`
exposes the grandparent's cells at the `gparent` spelling through the alias
index, and `tmp = gparent->rb_right` reads.

The next C branch, `if (parent != tmp)`, asks whether the parent is the
grandparent's left child. `cu`'s own constructor answers that, but the
disequality between `gparent->rb_left` and `gparent->rb_right` does not follow
from it: it holds because the uncle at `gparent->rb_right` is either null or a
separately owned node. So the uncle's arms are split first — the same split the
next C test, `if (tmp && rb_is_red(tmp))`, needs anyway. In the `RbTree::Empty`
arm `unfold(us)` publishes `gparent->rb_right == 0` and the two guards are
decided by null-ness in opposite directions: the parent is not null, so
`parent != tmp`, and the uncle is, so case 1 is skipped. In the `RbTree::Node`
arm `unfold(us)` owns the uncle's own parent word beside the parent's, and
`parent != tmp` is then the standing separation rule of
[`pointer_disequality_from_separation.md`](pointer_disequality_from_separation.md)
with no `have` at all.

The frontier is now statement 23, the case-2 test `tmp = parent->rb_right; if
(node == tmp)`, and it is where the four frame combinations stop agreeing: with
`c` a `Left` frame the focus is the parent's left child and the outer case 3
runs directly, with `c` a `Right` frame it is the inner case 2 first. Both need
the parent's *other* child split the same way the uncle just was. That is where
the next slice starts; the two rotation `break`s, the two recolour `continue`s,
the body's end and the post-loop `is_rb_root` are still ahead of it.

**A gap this run found, not worked around.** A proof `match` arm inside
`preserve` may be closed by `contradiction` only when the `contradiction` is the
arm's *only* tactic: `plan_execution_match` in
`src/surface/proof/proof_object/match_cases.rs` matches `[ProofTactic::Contradiction(surface)]`
on the arm's tactic list to plan the arm as excluded, so any `have` in front of
it leaves a live arm and the `contradiction` is then refused with
"`contradiction` did not verify as a checked preservation operation". The
smallest reproduction is `mdtests/loop_head_refuted_arm_closes_the_match.md`
with `have n >= 0 by { simp(); }` inserted before its `contradiction`. Lifting
the restriction means running an arm's prefix tactics during planning, which is
not a local change, so the fact a refutation needs is stated as a pure theorem
above and applied before the `match` instead.

The contract itself is D3 and D4 on the node-keyed model. `__rb_insert` returns
`void` and reassigns `node`, so the cursor at the exit has no C name and the
produced instances are named at the root cell instead. `ctx_holds(c.model,
t.model)` is the gluing requirement
that the frame's own node is the focused subtree's parent payload — the
replacement for the `parent` parameter the ascent fixtures have and this
function does not.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

#define __WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
#define WRITE_ONCE(x, value) __WRITE_ONCE(x, value)
#define likely(x) (x)
#define unlikely(x) (x)
#define __always_inline inline
#define true 1

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

struct rb_root {
    struct rb_node *rb_node;
};

#define __rb_color(pc)     ((pc) & 1)
#define __rb_is_black(pc)  __rb_color(pc)
#define __rb_is_red(pc)    (!__rb_color(pc))
#define rb_color(rb)       __rb_color((rb)->__rb_parent_color)
#define rb_is_red(rb)      __rb_is_red((rb)->__rb_parent_color)
#define rb_is_black(rb)    __rb_is_black((rb)->__rb_parent_color)

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}

static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
    rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;
}

static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int32 color) {
    rb->__rb_parent_color = (unsigned long)p | color;
}

static inline void rb_set_black(struct rb_node *rb) {
    rb->__rb_parent_color += RB_BLACK;
}

static inline struct rb_node *rb_red_parent(struct rb_node *red) {
    return (struct rb_node *)red->__rb_parent_color;
}

static inline void
__rb_change_child(struct rb_node *old, struct rb_node *new,
                  struct rb_node *parent, struct rb_root *root)
{
    if (parent) {
        if (parent->rb_left == old)
            WRITE_ONCE(parent->rb_left, new);
        else
            WRITE_ONCE(parent->rb_right, new);
    } else
        WRITE_ONCE(root->rb_node, new);
}

static inline void
__rb_rotate_set_parents(struct rb_node *old, struct rb_node *new,
                        struct rb_root *root, int color)
{
    struct rb_node *parent = rb_parent(old);
    new->__rb_parent_color = old->__rb_parent_color;
    rb_set_parent_color(old, new, color);
    __rb_change_child(old, new, parent, root);
}
#endif
```

```c filename=rb_insert_color.c
#include "rbtree.h"

static __always_inline void
__rb_insert(struct rb_node *node, struct rb_root *root,
	    void (*augment_rotate)(struct rb_node *old, struct rb_node *new))
{
	struct rb_node *parent = rb_red_parent(node), *gparent, *tmp;

	while (true) {
		/*
		 * Loop invariant: node is red.
		 */
		if (unlikely(!parent)) {
			/*
			 * The inserted node is root. Either this is the
			 * first node, or we recursed at Case 1 below and
			 * are no longer violating 4).
			 */
			rb_set_parent_color(node, NULL, RB_BLACK);
			break;
		}

		/*
		 * If there is a black parent, we are done.
		 * Otherwise, take some corrective action as,
		 * per 4), we don't want a red root or two
		 * consecutive red nodes.
		 */
		if(rb_is_black(parent))
			break;

		gparent = rb_red_parent(parent);

		tmp = gparent->rb_right;
		if (parent != tmp) {	/* parent == gparent->rb_left */
			if (tmp && rb_is_red(tmp)) {
				/*
				 * Case 1 - node's uncle is red (color flips).
				 *
				 *       G            g
				 *      / \          / \
				 *     p   u  -->   P   U
				 *    /            /
				 *   n            n
				 *
				 * However, since g's parent might be red, and
				 * 4) does not allow this, we need to recurse
				 * at g.
				 */
				rb_set_parent_color(tmp, gparent, RB_BLACK);
				rb_set_parent_color(parent, gparent, RB_BLACK);
				node = gparent;
				parent = rb_parent(node);
				rb_set_parent_color(node, parent, RB_RED);
				continue;
			}

			tmp = parent->rb_right;
			if (node == tmp) {
				/*
				 * Case 2 - node's uncle is black and node is
				 * the parent's right child (left rotate at parent).
				 *
				 *      G             G
				 *     / \           / \
				 *    p   U  -->    n   U
				 *     \           /
				 *      n         p
				 *
				 * This still leaves us in violation of 4), the
				 * continuation into Case 3 will fix that.
				 */
				tmp = node->rb_left;
				WRITE_ONCE(parent->rb_right, tmp);
				WRITE_ONCE(node->rb_left, parent);
				if (tmp)
					rb_set_parent_color(tmp, parent,
							    RB_BLACK);
				rb_set_parent_color(parent, node, RB_RED);
				augment_rotate(parent, node);
				parent = node;
				tmp = node->rb_right;
			}

			/*
			 * Case 3 - node's uncle is black and node is
			 * the parent's left child (right rotate at gparent).
			 *
			 *        G           P
			 *       / \         / \
			 *      p   U  -->  n   g
			 *     /                 \
			 *    n                   U
			 */
			WRITE_ONCE(gparent->rb_left, tmp); /* == parent->rb_right */
			WRITE_ONCE(parent->rb_right, gparent);
			if (tmp)
				rb_set_parent_color(tmp, gparent, RB_BLACK);
			__rb_rotate_set_parents(gparent, parent, root, RB_RED);
			augment_rotate(gparent, parent);
			break;
		} else {
			tmp = gparent->rb_left;
			if (tmp && rb_is_red(tmp)) {
				/* Case 1 - color flips */
				rb_set_parent_color(tmp, gparent, RB_BLACK);
				rb_set_parent_color(parent, gparent, RB_BLACK);
				node = gparent;
				parent = rb_parent(node);
				rb_set_parent_color(node, parent, RB_RED);
				continue;
			}

			tmp = parent->rb_left;
			if (node == tmp) {
				/* Case 2 - right rotate at parent */
				tmp = node->rb_right;
				WRITE_ONCE(parent->rb_left, tmp);
				WRITE_ONCE(node->rb_right, parent);
				if (tmp)
					rb_set_parent_color(tmp, parent,
							    RB_BLACK);
				rb_set_parent_color(parent, node, RB_RED);
				augment_rotate(parent, node);
				parent = node;
				tmp = node->rb_left;
			}

			/* Case 3 - left rotate at gparent */
			WRITE_ONCE(gparent->rb_right, tmp); /* == parent->rb_left */
			WRITE_ONCE(parent->rb_left, gparent);
			if (tmp)
				rb_set_parent_color(tmp, gparent, RB_BLACK);
			__rb_rotate_set_parents(gparent, parent, root, RB_RED);
			augment_rotate(gparent, parent);
			break;
		}
	}
}

static inline void dummy_rotate(struct rb_node *old, struct rb_node *new) {}

void rb_insert_color(struct rb_node *node, struct rb_root *root)
{
	__rb_insert(node, root, dummy_rotate);
}
```

```click
verifying "rb_insert_color.c";

spec enum Color {
    Red,
    Black,
}

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, struct rb_node*, Color, RbTree, Context),
}

function rb_inorder(tree: RbTree) -> List<struct rb_node*>
    decreases tree
{
    match tree {
        RbTree::Empty => List<struct rb_node*>::Nil,
        RbTree::Node(node, parent, color, left, right) =>
            list_append(rb_inorder(left),
                List<struct rb_node*>::Cons(node, rb_inorder(right))),
    }
}

function rb_member(tree: RbTree, target: struct rb_node*) -> int32
    decreases tree
{
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(node, parent, color, left, right) =>
            if node == target {
                1
            } else {
                if rb_member(left, target) == 1 {
                    1
                } else {
                    rb_member(right, target)
                }
            },
    }
}

theorem rb_member_is_inorder_membership(tree: RbTree, target: struct rb_node*) {
    ensures rb_member(tree, target) == list_contains(rb_inorder(tree), target) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_member(RbTree::Empty, target));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_contains(List<struct rb_node*>::Nil, target));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(ih(left, target));
                apply(ih(right, target));
                unfold(rb_member(RbTree::Node(node, parent, color, left, right), target));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                apply(list_contains_append(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(right)), target));
                rewrite(list_contains(list_append(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))), target)
                    == if list_contains(rb_inorder(left), target) == 1 {
                        1
                    } else {
                        list_contains(List<struct rb_node*>::Cons(node, rb_inorder(right)), target)
                    });
                apply(list_contains_cons(node, rb_inorder(right), target));
                rewrite(list_contains(List<struct rb_node*>::Cons(node, rb_inorder(right)), target)
                    == if node == target {
                        1
                    } else {
                        list_contains(rb_inorder(right), target)
                    });
                rewrite(rb_member(left, target) == list_contains(rb_inorder(left), target));
                rewrite(rb_member(right, target) == list_contains(rb_inorder(right), target));
                if node == target {
                    normalize() using { node == target; }
                } else {
                    normalize() using { not(node == target); }
                }
            }
        }
    }
}

function black_height(tree: RbTree) -> Nat
    decreases tree
{
    match tree {
        RbTree::Empty => Nat::Zero,
        RbTree::Node(node, parent, color, left, right) => match color {
            Color::Red => black_height(left),
            Color::Black => Nat::Succ(black_height(left)),
        },
    }
}

function rb_root_black(tree: RbTree) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) => match color {
            Color::Red => 0,
            Color::Black => 1,
        },
    }
}

function is_rb(tree: RbTree) -> int32
    decreases tree
{
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if is_rb(left) == 1 {
                if is_rb(right) == 1 {
                    if black_height(left) == black_height(right) {
                        match color {
                            Color::Red =>
                                if rb_root_black(left) == 1 {
                                    rb_root_black(right)
                                } else {
                                    0
                                },
                            Color::Black => 1,
                        }
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function rb_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => left,
    }
}

function rb_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => right,
    }
}

function rb_color(tree: RbTree) -> Color {
    match tree {
        RbTree::Empty => Color::Black,
        RbTree::Node(node, parent, color, left, right) => color,
    }
}

function rb_reparent(tree: RbTree, new_parent: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            RbTree::Node(node, new_parent, color, left, right),
    }
}

theorem rb_reparent_preserves_inorder(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_inorder(rb_reparent(tree, new_parent)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(rb_inorder(RbTree::Node(node, new_parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_is_rb(tree: RbTree, new_parent: struct rb_node*) {
    ensures is_rb(rb_reparent(tree, new_parent)) == is_rb(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(is_rb(RbTree::Node(node, new_parent, color, left, right)));
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_black_height(tree: RbTree, new_parent: struct rb_node*) {
    ensures black_height(rb_reparent(tree, new_parent)) == black_height(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(black_height(RbTree::Node(node, new_parent, color, left, right)));
                unfold(black_height(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_rb_root_black(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_root_black(rb_reparent(tree, new_parent)) == rb_root_black(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(rb_root_black(RbTree::Node(node, new_parent, color, left, right)));
                unfold(rb_root_black(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

function rb_rotate_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match right {
            RbTree::Empty => tree,
            RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right) =>
                RbTree::Node(pivot, parent, pivot_color,
                    RbTree::Node(node, pivot, color, left, rb_reparent(middle, node)),
                    far_right),
        },
    }
}

function rb_rotate_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => tree,
            RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle) =>
                RbTree::Node(pivot, parent, pivot_color, far_left,
                    RbTree::Node(node, pivot, color, rb_reparent(middle, node), right)),
        },
    }
}

theorem rb_rotate_left_node_preserves_inorder(node: struct rb_node*, parent: struct rb_node*,
                                              color: Color, left: RbTree, right: RbTree) {
    ensures rb_inorder(rb_rotate_left(RbTree::Node(node, parent, color, left, right)))
        == rb_inorder(RbTree::Node(node, parent, color, left, right)) by {
        induct(right) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left, RbTree::Empty)));
                normalize();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right) => {
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right))));
                unfold(rb_inorder(RbTree::Node(pivot, parent, pivot_color,
                    RbTree::Node(node, pivot, color, left, rb_reparent(middle, node)),
                    far_right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right))));
                unfold(rb_inorder(RbTree::Node(node, pivot, color, left,
                    rb_reparent(middle, node))));
                unfold(rb_inorder(RbTree::Node(pivot, pivot_parent, pivot_color,
                    middle, far_right)));
                apply(rb_reparent_preserves_inorder(middle, node));
                rewrite(rb_inorder(rb_reparent(middle, node)) == rb_inorder(middle));
                apply(list_append_associative(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(far_right))));
                rewrite(list_append(list_append(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(middle))),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(far_right)))
                    == list_append(rb_inorder(left),
                        list_append(List<struct rb_node*>::Cons(node, rb_inorder(middle)),
                            List<struct rb_node*>::Cons(pivot, rb_inorder(far_right)))));
                unfold(list_append(List<struct rb_node*>::Cons(node, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(far_right))));
                normalize();
            }
        }
    }
}

theorem rb_rotate_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_left(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_left_node_preserves_inorder(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

theorem rb_rotate_right_node_preserves_inorder(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree, right: RbTree) {
    ensures rb_inorder(rb_rotate_right(RbTree::Node(node, parent, color, left, right)))
        == rb_inorder(RbTree::Node(node, parent, color, left, right)) by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                normalize();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle) => {
                unfold(rb_rotate_right(RbTree::Node(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right)));
                unfold(rb_inorder(RbTree::Node(pivot, parent, pivot_color, far_left,
                    RbTree::Node(node, pivot, color, rb_reparent(middle, node), right))));
                unfold(rb_inorder(RbTree::Node(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right)));
                unfold(rb_inorder(RbTree::Node(node, pivot, color,
                    rb_reparent(middle, node), right)));
                unfold(rb_inorder(RbTree::Node(pivot, pivot_parent, pivot_color,
                    far_left, middle)));
                apply(rb_reparent_preserves_inorder(middle, node));
                rewrite(rb_inorder(rb_reparent(middle, node)) == rb_inorder(middle));
                apply(list_append_associative(rb_inorder(far_left),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                rewrite(list_append(list_append(rb_inorder(far_left),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(middle))),
                    List<struct rb_node*>::Cons(node, rb_inorder(right)))
                    == list_append(rb_inorder(far_left),
                        list_append(List<struct rb_node*>::Cons(pivot, rb_inorder(middle)),
                            List<struct rb_node*>::Cons(node, rb_inorder(right)))));
                unfold(list_append(List<struct rb_node*>::Cons(pivot, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                normalize();
            }
        }
    }
}

theorem rb_rotate_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_right(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_right_node_preserves_inorder(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

function rb_recolor(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, old_color, left, right) =>
            RbTree::Node(node, parent, color, left, right),
    }
}

function rb_recolor_left(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, old_color, left, right) =>
            RbTree::Node(node, parent, old_color, rb_recolor(left, color), right),
    }
}

function rb_recolor_right(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, old_color, left, right) =>
            RbTree::Node(node, parent, old_color, left, rb_recolor(right, color)),
    }
}

function rb_rotate_left_at_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            RbTree::Node(node, parent, color, rb_rotate_left(left), right),
    }
}

function rb_rotate_right_at_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            RbTree::Node(node, parent, color, left, rb_rotate_right(right)),
    }
}

theorem rb_recolor_preserves_inorder(tree: RbTree, color: Color) {
    ensures rb_inorder(rb_recolor(tree, color)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_recolor_left_preserves_inorder(tree: RbTree, color: Color) {
    ensures rb_inorder(rb_recolor_left(tree, color)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor_left(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor_left(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color,
                    rb_recolor(left, color), right)));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left, right)));
                apply(rb_recolor_preserves_inorder(left, color));
                rewrite(rb_inorder(rb_recolor(left, color)) == rb_inorder(left));
                normalize();
            }
        }
    }
}

theorem rb_recolor_right_preserves_inorder(tree: RbTree, color: Color) {
    ensures rb_inorder(rb_recolor_right(tree, color)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor_right(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor_right(RbTree::Node(node, parent, old_color, left, right),
                    color));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left,
                    rb_recolor(right, color))));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left, right)));
                apply(rb_recolor_preserves_inorder(right, color));
                rewrite(rb_inorder(rb_recolor(right, color)) == rb_inorder(right));
                normalize();
            }
        }
    }
}

theorem rb_rotate_left_at_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_left_at_left(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left_at_left(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_rotate_left_at_left(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, rb_rotate_left(left), right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                apply(rb_rotate_left_preserves_inorder(left));
                rewrite(rb_inorder(rb_rotate_left(left)) == rb_inorder(left));
                normalize();
            }
        }
    }
}

theorem rb_rotate_right_at_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_right_at_right(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right_at_right(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_rotate_right_at_right(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left,
                    rb_rotate_right(right))));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                apply(rb_rotate_right_preserves_inorder(right));
                rewrite(rb_inorder(rb_rotate_right(right)) == rb_inorder(right));
                normalize();
            }
        }
    }
}

theorem black_height_black_node(node: struct rb_node*, parent: struct rb_node*,
                                left: RbTree, right: RbTree) {
    ensures black_height(RbTree::Node(node, parent, Color::Black, left, right))
        == Nat::Succ(black_height(left)) by {
        unfold(black_height(RbTree::Node(node, parent, Color::Black, left, right)));
        normalize();
    }
}

theorem black_height_red_node(node: struct rb_node*, parent: struct rb_node*,
                              left: RbTree, right: RbTree) {
    ensures black_height(RbTree::Node(node, parent, Color::Red, left, right))
        == black_height(left) by {
        unfold(black_height(RbTree::Node(node, parent, Color::Red, left, right)));
        normalize();
    }
}

theorem rb_root_black_black_node(node: struct rb_node*, parent: struct rb_node*,
                                 left: RbTree, right: RbTree) {
    ensures rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by {
        unfold(rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)));
        normalize();
    }
}

theorem rb_root_black_red_node(node: struct rb_node*, parent: struct rb_node*,
                               left: RbTree, right: RbTree) {
    ensures rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) == 0 by {
        unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)));
        normalize();
    }
}

theorem is_rb_black_node(node: struct rb_node*, parent: struct rb_node*,
                         left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);

    ensures is_rb(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by {
        unfold(is_rb(RbTree::Node(node, parent, Color::Black, left, right)));
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
        }
    }
}

theorem is_rb_red_node(node: struct rb_node*, parent: struct rb_node*,
                       left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);
    requires rb_root_black(left) == 1;
    requires rb_root_black(right) == 1;

    ensures is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1 by {
        unfold(is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
        rewrite(rb_root_black(right) == 1);
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
            rb_root_black(left) == 1;
        }
    }
}

theorem is_rb_node_left(node: struct rb_node*, parent: struct rb_node*, color: Color,
                        left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(left) == 1 by {
        if is_rb(left) == 1 {
            assumption();
        } else {
            have is_rb(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize() using { not(is_rb(left) == 1); }
            }
            contradiction(is_rb(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_node_right(node: struct rb_node*, parent: struct rb_node*, color: Color,
                         left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(right) == 1 by {
        if is_rb(right) == 1 {
            assumption();
        } else {
            apply(is_rb_node_left(node, parent, color, left, right));
            have is_rb(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize() using { is_rb(left) == 1; not(is_rb(right) == 1); }
            }
            contradiction(is_rb(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_node_black_heights(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                 left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures black_height(left) == black_height(right) by {
        if black_height(left) == black_height(right) {
            assumption();
        } else {
            apply(is_rb_node_left(node, parent, color, left, right));
            apply(is_rb_node_right(node, parent, color, left, right));
            have is_rb(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize() using {
                    is_rb(left) == 1;
                    is_rb(right) == 1;
                    not(black_height(left) == black_height(right));
                }
            }
            contradiction(is_rb(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_red_node_children_are_black(node: struct rb_node*, parent: struct rb_node*,
                                          left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1;

    ensures rb_root_black(left) == 1 by {
        if rb_root_black(left) == 1 {
            assumption();
        } else {
            apply(is_rb_node_left(node, parent, Color::Red, left, right));
            apply(is_rb_node_right(node, parent, Color::Red, left, right));
            apply(is_rb_node_black_heights(node, parent, Color::Red, left, right));
            have is_rb(RbTree::Node(node, parent, Color::Red, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
                normalize() using {
                    is_rb(left) == 1;
                    is_rb(right) == 1;
                    black_height(left) == black_height(right);
                    not(rb_root_black(left) == 1);
                }
            }
            contradiction(is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1);
        }
    }
}

function is_rb_root(tree: RbTree) -> int32 {
    if is_rb(tree) == 1 {
        rb_root_black(tree)
    } else {
        0
    }
}

function almost_rb_insert(tree: RbTree) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if is_rb(left) == 1 {
                if is_rb(right) == 1 {
                    if black_height(left) == black_height(right) {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function almost_rb_erase(tree: RbTree, required: Nat) -> int32 {
    if is_rb(tree) == 1 {
        if Nat::Succ(black_height(tree)) == required {
            1
        } else {
            0
        }
    } else {
        0
    }
}

theorem almost_rb_insert_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                              left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);

    ensures almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1 by {
        unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
        }
    }
}

theorem almost_rb_insert_node_left(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                   left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(left) == 1 by {
        if is_rb(left) == 1 {
            assumption();
        } else {
            have almost_rb_insert(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
                normalize() using { not(is_rb(left) == 1); }
            }
            contradiction(almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem almost_rb_insert_node_right(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                    left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(right) == 1 by {
        if is_rb(right) == 1 {
            assumption();
        } else {
            apply(almost_rb_insert_node_left(node, parent, color, left, right));
            have almost_rb_insert(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
                normalize() using { is_rb(left) == 1; not(is_rb(right) == 1); }
            }
            contradiction(almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem almost_rb_insert_node_black_heights(node: struct rb_node*, parent: struct rb_node*,
                                            color: Color, left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures black_height(left) == black_height(right) by {
        if black_height(left) == black_height(right) {
            assumption();
        } else {
            apply(almost_rb_insert_node_left(node, parent, color, left, right));
            apply(almost_rb_insert_node_right(node, parent, color, left, right));
            have almost_rb_insert(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
                normalize() using {
                    is_rb(left) == 1;
                    is_rb(right) == 1;
                    not(black_height(left) == black_height(right));
                }
            }
            contradiction(almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_is_almost_rb_insert(tree: RbTree) {
    requires is_rb(tree) == 1;

    ensures almost_rb_insert(tree) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(almost_rb_insert(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(is_rb_node_left(node, parent, color, left, right));
                apply(is_rb_node_right(node, parent, color, left, right));
                apply(is_rb_node_black_heights(node, parent, color, left, right));
                apply(almost_rb_insert_node(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

theorem almost_rb_insert_black_root_is_rb(node: struct rb_node*, parent: struct rb_node*,
                                          left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, Color::Black, left, right)) == 1;

    ensures is_rb(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by {
        apply(almost_rb_insert_node_left(node, parent, Color::Black, left, right));
        apply(almost_rb_insert_node_right(node, parent, Color::Black, left, right));
        apply(almost_rb_insert_node_black_heights(node, parent, Color::Black, left, right));
        apply(is_rb_black_node(node, parent, left, right));
        assumption();
    }
}

theorem rb_blacken_root_restores_rb(tree: RbTree) {
    requires almost_rb_insert(tree) == 1;

    ensures is_rb_root(rb_recolor(tree, Color::Black)) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, Color::Black));
                unfold(is_rb_root(RbTree::Empty));
                unfold(is_rb(RbTree::Empty));
                unfold(rb_root_black(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(almost_rb_insert_node_left(node, parent, color, left, right));
                apply(almost_rb_insert_node_right(node, parent, color, left, right));
                apply(almost_rb_insert_node_black_heights(node, parent, color, left, right));
                apply(is_rb_black_node(node, parent, left, right));
                apply(rb_root_black_black_node(node, parent, left, right));
                unfold(rb_recolor(RbTree::Node(node, parent, color, left, right), Color::Black));
                unfold(is_rb_root(RbTree::Node(node, parent, Color::Black, left, right)));
                rewrite(rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)) == 1);
                normalize() using {
                    is_rb(RbTree::Node(node, parent, Color::Black, left, right)) == 1;
                }
            }
        }
    }
}

theorem almost_rb_erase_node(tree: RbTree, required: Nat) {
    requires is_rb(tree) == 1;
    requires Nat::Succ(black_height(tree)) == required;

    ensures almost_rb_erase(tree, required) == 1 by {
        unfold(almost_rb_erase(tree, required));
        normalize() using {
            is_rb(tree) == 1;
            Nat::Succ(black_height(tree)) == required;
        }
    }
}

theorem almost_rb_erase_is_rb(tree: RbTree, required: Nat) {
    requires almost_rb_erase(tree, required) == 1;

    ensures is_rb(tree) == 1 by {
        if is_rb(tree) == 1 {
            assumption();
        } else {
            have almost_rb_erase(tree, required) != 1 by {
                unfold(almost_rb_erase(tree, required));
                normalize() using { not(is_rb(tree) == 1); }
            }
            contradiction(almost_rb_erase(tree, required) == 1);
        }
    }
}

theorem almost_rb_erase_black_deficit(tree: RbTree, required: Nat) {
    requires almost_rb_erase(tree, required) == 1;

    ensures Nat::Succ(black_height(tree)) == required by {
        if Nat::Succ(black_height(tree)) == required {
            assumption();
        } else {
            apply(almost_rb_erase_is_rb(tree, required));
            have almost_rb_erase(tree, required) != 1 by {
                unfold(almost_rb_erase(tree, required));
                normalize() using {
                    is_rb(tree) == 1;
                    not(Nat::Succ(black_height(tree)) == required);
                }
            }
            contradiction(almost_rb_erase(tree, required) == 1);
        }
    }
}

function rb_insert_fix_recolor(tree: RbTree) -> RbTree {
    rb_recolor(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red)
}

function rb_insert_fix_inner_left(tree: RbTree) -> RbTree {
    rb_rotate_left_at_left(tree)
}

function rb_insert_fix_inner_right(tree: RbTree) -> RbTree {
    rb_rotate_right_at_right(tree)
}

function rb_insert_fix_outer_left(tree: RbTree) -> RbTree {
    rb_recolor(rb_recolor_right(rb_rotate_right(tree), Color::Red), Color::Black)
}

function rb_insert_fix_outer_right(tree: RbTree) -> RbTree {
    rb_recolor(rb_recolor_left(rb_rotate_left(tree), Color::Red), Color::Black)
}


theorem rb_insert_fix_recolor_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_recolor(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_recolor(tree));
        apply(rb_recolor_preserves_inorder(
            rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red));
        rewrite(rb_inorder(rb_recolor(
            rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red))
            == rb_inorder(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black)));
        apply(rb_recolor_left_preserves_inorder(
            rb_recolor_right(tree, Color::Black), Color::Black));
        rewrite(rb_inorder(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black))
            == rb_inorder(rb_recolor_right(tree, Color::Black)));
        apply(rb_recolor_right_preserves_inorder(tree, Color::Black));
        assumption();
    }
}

theorem rb_insert_fix_inner_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_inner_left(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_inner_left(tree));
        apply(rb_rotate_left_at_left_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_inner_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_inner_right(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_inner_right(tree));
        apply(rb_rotate_right_at_right_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_outer_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_outer_left(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_outer_left(tree));
        apply(rb_recolor_preserves_inorder(
            rb_recolor_right(rb_rotate_right(tree), Color::Red), Color::Black));
        rewrite(rb_inorder(rb_recolor(
            rb_recolor_right(rb_rotate_right(tree), Color::Red), Color::Black))
            == rb_inorder(rb_recolor_right(rb_rotate_right(tree), Color::Red)));
        apply(rb_recolor_right_preserves_inorder(rb_rotate_right(tree), Color::Red));
        rewrite(rb_inorder(rb_recolor_right(rb_rotate_right(tree), Color::Red))
            == rb_inorder(rb_rotate_right(tree)));
        apply(rb_rotate_right_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_outer_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_outer_right(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_outer_right(tree));
        apply(rb_recolor_preserves_inorder(
            rb_recolor_left(rb_rotate_left(tree), Color::Red), Color::Black));
        rewrite(rb_inorder(rb_recolor(
            rb_recolor_left(rb_rotate_left(tree), Color::Red), Color::Black))
            == rb_inorder(rb_recolor_left(rb_rotate_left(tree), Color::Red)));
        apply(rb_recolor_left_preserves_inorder(rb_rotate_left(tree), Color::Red));
        rewrite(rb_inorder(rb_recolor_left(rb_rotate_left(tree), Color::Red))
            == rb_inorder(rb_rotate_left(tree)));
        apply(rb_rotate_left_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_recolor_propagates(grandparent: struct rb_node*,
                                         above: struct rb_node*,
                                         parent: struct rb_node*,
                                         uncle: struct rb_node*,
                                         a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures almost_rb_insert(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d)))) == 1 by {
        unfold(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        unfold(rb_recolor_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d)), Color::Black));
        unfold(rb_recolor(RbTree::Node(uncle, grandparent, Color::Red, c, d), Color::Black));
        unfold(rb_recolor_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d)), Color::Black));
        unfold(rb_recolor(RbTree::Node(parent, grandparent, Color::Red, a, b), Color::Black));
        unfold(rb_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d)), Color::Red));
        apply(is_rb_black_node(parent, grandparent, a, b));
        apply(is_rb_black_node(uncle, grandparent, c, d));
        apply(black_height_black_node(parent, grandparent, a, b));
        apply(black_height_black_node(uncle, grandparent, c, d));
        have black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
            == black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d)) by {
            rewrite(black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
                == Nat::Succ(black_height(a)));
            rewrite(black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d))
                == Nat::Succ(black_height(c)));
            rewrite(black_height(a) == black_height(b));
            rewrite(black_height(b) == black_height(c));
            normalize();
        }
        apply(almost_rb_insert_node(grandparent, above, Color::Red,
            RbTree::Node(parent, grandparent, Color::Black, a, b),
            RbTree::Node(uncle, grandparent, Color::Black, c, d)));
        assumption();
    }
}

theorem rb_insert_fix_outer_left_restores(grandparent: struct rb_node*,
                                          above: struct rb_node*,
                                          parent: struct rb_node*,
                                          cursor: struct rb_node*,
                                          a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b), c),
            d))) == 1 by {
        unfold(rb_insert_fix_outer_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_rotate_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_recolor_right(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Black,
                    rb_reparent(c, grandparent), d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black,
            rb_reparent(c, grandparent), d), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d)), Color::Black));
        apply(rb_reparent_preserves_is_rb(c, grandparent));
        apply(rb_reparent_preserves_black_height(c, grandparent));
        apply(rb_reparent_preserves_rb_root_black(c, grandparent));
        have is_rb(rb_reparent(c, grandparent)) == 1 by {
            rewrite(is_rb(rb_reparent(c, grandparent)) == is_rb(c));
            assumption();
        }
        have rb_root_black(rb_reparent(c, grandparent)) == 1 by {
            rewrite(rb_root_black(rb_reparent(c, grandparent)) == rb_root_black(c));
            assumption();
        }
        have black_height(rb_reparent(c, grandparent)) == black_height(d) by {
            rewrite(black_height(rb_reparent(c, grandparent)) == black_height(c));
            assumption();
        }
        apply(is_rb_red_node(cursor, parent, a, b));
        apply(is_rb_red_node(grandparent, parent, rb_reparent(c, grandparent), d));
        apply(black_height_red_node(cursor, parent, a, b));
        apply(black_height_red_node(grandparent, parent, rb_reparent(c, grandparent), d));
        have black_height(RbTree::Node(cursor, parent, Color::Red, a, b))
            == black_height(RbTree::Node(grandparent, parent, Color::Red,
                rb_reparent(c, grandparent), d)) by {
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, a, b))
                == black_height(a));
            rewrite(black_height(RbTree::Node(grandparent, parent, Color::Red,
                rb_reparent(c, grandparent), d)) == black_height(rb_reparent(c, grandparent)));
            rewrite(black_height(rb_reparent(c, grandparent)) == black_height(c));
            rewrite(black_height(a) == black_height(b));
            rewrite(black_height(b) == black_height(c));
            normalize();
        }
        apply(is_rb_black_node(parent, above,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)));
        assumption();
    }
}

theorem rb_insert_fix_outer_right_restores(grandparent: struct rb_node*,
                                           above: struct rb_node*,
                                           parent: struct rb_node*,
                                           cursor: struct rb_node*,
                                           a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red, b,
                RbTree::Node(cursor, parent, Color::Red, c, d))))) == 1 by {
        unfold(rb_insert_fix_outer_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_rotate_left(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_recolor_left(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Black, a,
                    rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black, a,
            rb_reparent(b, grandparent)), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Black));
        apply(rb_reparent_preserves_is_rb(b, grandparent));
        apply(rb_reparent_preserves_black_height(b, grandparent));
        apply(rb_reparent_preserves_rb_root_black(b, grandparent));
        have is_rb(rb_reparent(b, grandparent)) == 1 by {
            rewrite(is_rb(rb_reparent(b, grandparent)) == is_rb(b));
            assumption();
        }
        have rb_root_black(rb_reparent(b, grandparent)) == 1 by {
            rewrite(rb_root_black(rb_reparent(b, grandparent)) == rb_root_black(b));
            assumption();
        }
        have black_height(a) == black_height(rb_reparent(b, grandparent)) by {
            rewrite(black_height(rb_reparent(b, grandparent)) == black_height(b));
            assumption();
        }
        apply(is_rb_red_node(grandparent, parent, a, rb_reparent(b, grandparent)));
        apply(is_rb_red_node(cursor, parent, c, d));
        apply(black_height_red_node(grandparent, parent, a, rb_reparent(b, grandparent)));
        apply(black_height_red_node(cursor, parent, c, d));
        have black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent)))
            == black_height(RbTree::Node(cursor, parent, Color::Red, c, d)) by {
            rewrite(black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent))) == black_height(a));
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, c, d))
                == black_height(c));
            rewrite(black_height(a) == black_height(b));
            rewrite(black_height(b) == black_height(c));
            normalize();
        }
        apply(is_rb_black_node(parent, above,
            RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)));
        assumption();
    }
}

theorem rb_insert_fix_inner_left_becomes_outer(grandparent: struct rb_node*,
                                               above: struct rb_node*,
                                               parent: struct rb_node*,
                                               cursor: struct rb_node*,
                                               a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_inner_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c)),
            d))
        == RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(cursor, grandparent, Color::Red,
                RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c),
            d) by {
        unfold(rb_insert_fix_inner_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d)));
        unfold(rb_rotate_left_at_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d)));
        unfold(rb_rotate_left(
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c))));
        normalize();
    }
}

theorem rb_insert_fix_inner_right_becomes_outer(grandparent: struct rb_node*,
                                                above: struct rb_node*,
                                                parent: struct rb_node*,
                                                cursor: struct rb_node*,
                                                a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_inner_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d)))
        == RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(cursor, grandparent, Color::Red, b,
                RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) by {
        unfold(rb_insert_fix_inner_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        unfold(rb_rotate_right_at_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        unfold(rb_rotate_right(
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d)));
        normalize();
    }
}

theorem rb_insert_fix_inner_left_restores(grandparent: struct rb_node*,
                                          above: struct rb_node*,
                                          parent: struct rb_node*,
                                          cursor: struct rb_node*,
                                          a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c)),
            d)))) == 1 by {
        apply(rb_insert_fix_inner_left_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        rewrite(rb_insert_fix_inner_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d))
            == RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(cursor, grandparent, Color::Red,
                    RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c),
                d));
        apply(rb_reparent_preserves_is_rb(b, parent));
        apply(rb_reparent_preserves_black_height(b, parent));
        apply(rb_reparent_preserves_rb_root_black(b, parent));
        have is_rb(rb_reparent(b, parent)) == 1 by {
            rewrite(is_rb(rb_reparent(b, parent)) == is_rb(b));
            assumption();
        }
        have rb_root_black(rb_reparent(b, parent)) == 1 by {
            rewrite(rb_root_black(rb_reparent(b, parent)) == rb_root_black(b));
            assumption();
        }
        have black_height(a) == black_height(rb_reparent(b, parent)) by {
            rewrite(black_height(rb_reparent(b, parent)) == black_height(b));
            assumption();
        }
        have black_height(rb_reparent(b, parent)) == black_height(c) by {
            rewrite(black_height(rb_reparent(b, parent)) == black_height(b));
            assumption();
        }
        apply(rb_insert_fix_outer_left_restores(grandparent, above, cursor, parent,
            a, rb_reparent(b, parent), c, d));
        assumption();
    }
}

theorem rb_insert_fix_inner_right_restores(grandparent: struct rb_node*,
                                           above: struct rb_node*,
                                           parent: struct rb_node*,
                                           cursor: struct rb_node*,
                                           a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d))))) == 1 by {
        apply(rb_insert_fix_inner_right_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        rewrite(rb_insert_fix_inner_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d)))
            == RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(cursor, grandparent, Color::Red, b,
                    RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))));
        apply(rb_reparent_preserves_is_rb(c, parent));
        apply(rb_reparent_preserves_black_height(c, parent));
        apply(rb_reparent_preserves_rb_root_black(c, parent));
        have is_rb(rb_reparent(c, parent)) == 1 by {
            rewrite(is_rb(rb_reparent(c, parent)) == is_rb(c));
            assumption();
        }
        have rb_root_black(rb_reparent(c, parent)) == 1 by {
            rewrite(rb_root_black(rb_reparent(c, parent)) == rb_root_black(c));
            assumption();
        }
        have black_height(b) == black_height(rb_reparent(c, parent)) by {
            rewrite(black_height(rb_reparent(c, parent)) == black_height(c));
            assumption();
        }
        have black_height(rb_reparent(c, parent)) == black_height(d) by {
            rewrite(black_height(rb_reparent(c, parent)) == black_height(c));
            assumption();
        }
        apply(rb_insert_fix_outer_right_restores(grandparent, above, cursor, parent,
            a, b, rb_reparent(c, parent), d));
        assumption();
    }
}

function list_tail<T>(xs: List<T>) -> List<T> {
    match xs {
        List::Nil => List<T>::Nil,
        List::Cons(head, tail) => tail,
    }
}

theorem list_tail_cons<T>(head: T, tail: List<T>) {
    ensures list_tail(List<T>::Cons(head, tail)) == tail by {
        unfold(list_tail(List<T>::Cons(head, tail)));
        normalize();
    }
}

function rb_min_list(tree: RbTree) -> List<struct rb_node*>
    decreases tree
{
    match tree {
        RbTree::Empty => List<struct rb_node*>::Nil,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => List<struct rb_node*>::Cons(node, List<struct rb_node*>::Nil),
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) =>
                rb_min_list(left),
        },
    }
}

function rb_remove_min(tree: RbTree) -> RbTree
    decreases tree
{
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => rb_reparent(right, parent),
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) =>
                RbTree::Node(node, parent, color, rb_remove_min(left), right),
        },
    }
}

theorem rb_inorder_node_splits(node: struct rb_node*, parent: struct rb_node*, color: Color,
                               left: RbTree, right: RbTree) {
    ensures rb_inorder(RbTree::Node(node, parent, color, left, right))
        == list_append(rb_inorder(left),
            List<struct rb_node*>::Cons(node, rb_inorder(right))) by {
        unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
        normalize();
    }
}

theorem rb_erase_no_left_child(erased: struct rb_node*, parent: struct rb_node*, color: Color,
                               right: RbTree) {
    ensures rb_inorder(RbTree::Node(erased, parent, color, RbTree::Empty, right))
        == List<struct rb_node*>::Cons(erased, rb_inorder(right)) by {
        unfold(rb_inorder(RbTree::Node(erased, parent, color, RbTree::Empty, right)));
        unfold(rb_inorder(RbTree::Empty));
        unfold(list_append(List<struct rb_node*>::Nil,
            List<struct rb_node*>::Cons(erased, rb_inorder(right))));
        normalize();
    }
}

theorem rb_erase_no_right_child(erased: struct rb_node*, parent: struct rb_node*, color: Color,
                                left: RbTree) {
    ensures rb_inorder(RbTree::Node(erased, parent, color, left, RbTree::Empty))
        == list_append(rb_inorder(left),
            List<struct rb_node*>::Cons(erased, List<struct rb_node*>::Nil)) by {
        unfold(rb_inorder(RbTree::Node(erased, parent, color, left, RbTree::Empty)));
        unfold(rb_inorder(RbTree::Empty));
        normalize();
    }
}

theorem rb_min_list_splits_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                left: RbTree, right: RbTree) {
    requires rb_inorder(left)
        == list_append(rb_min_list(left), rb_inorder(rb_remove_min(left)));

    ensures rb_inorder(RbTree::Node(node, parent, color, left, right))
        == list_append(rb_min_list(RbTree::Node(node, parent, color, left, right)),
            rb_inorder(rb_remove_min(RbTree::Node(node, parent, color, left, right)))) by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_min_list(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                apply(rb_reparent_preserves_inorder(right, parent));
                rewrite(rb_inorder(rb_reparent(right, parent)) == rb_inorder(right));
                unfold(rb_inorder(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_append(List<struct rb_node*>::Nil,
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                unfold(list_append(List<struct rb_node*>::Cons(node,
                    List<struct rb_node*>::Nil), rb_inorder(right)));
                unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(right)));
                normalize();
            }
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) => {
                unfold(rb_min_list(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                unfold(rb_remove_min(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color,
                    rb_remove_min(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    right)));
                rewrite(rb_inorder(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right))
                    == list_append(
                        rb_min_list(RbTree::Node(inner_node, inner_parent, inner_color,
                            inner_left, inner_right)),
                        rb_inorder(rb_remove_min(
                            RbTree::Node(inner_node, inner_parent, inner_color,
                                inner_left, inner_right)))));
                apply(list_append_associative(
                    rb_min_list(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    rb_inorder(rb_remove_min(
                        RbTree::Node(inner_node, inner_parent, inner_color,
                            inner_left, inner_right))),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                assumption();
            }
        }
    }
}

theorem rb_min_list_splits_inorder(tree: RbTree) {
    ensures rb_inorder(tree)
        == list_append(rb_min_list(tree), rb_inorder(rb_remove_min(tree))) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_min_list(RbTree::Empty));
                unfold(rb_remove_min(RbTree::Empty));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_append(List<struct rb_node*>::Nil, List<struct rb_node*>::Nil));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(ih(left));
                apply(rb_min_list_splits_node(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

theorem rb_remove_min_drops_head(tree: RbTree, minimum: struct rb_node*) {
    requires rb_min_list(tree)
        == List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil);

    ensures rb_inorder(tree)
        == List<struct rb_node*>::Cons(minimum, rb_inorder(rb_remove_min(tree))) by {
        apply(rb_min_list_splits_inorder(tree));
        rewrite(rb_inorder(tree)
            == list_append(rb_min_list(tree), rb_inorder(rb_remove_min(tree))));
        rewrite(rb_min_list(tree)
            == List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil));
        unfold(list_append(
            List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil),
            rb_inorder(rb_remove_min(tree))));
        unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(rb_remove_min(tree))));
        normalize();
    }
}

theorem rb_remove_min_is_inorder_tail(tree: RbTree, minimum: struct rb_node*) {
    requires rb_min_list(tree)
        == List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil);

    ensures rb_inorder(rb_remove_min(tree)) == list_tail(rb_inorder(tree)) by {
        apply(rb_remove_min_drops_head(tree, minimum));
        rewrite(rb_inorder(tree)
            == List<struct rb_node*>::Cons(minimum, rb_inorder(rb_remove_min(tree))));
        unfold(list_tail(List<struct rb_node*>::Cons(minimum,
            rb_inorder(rb_remove_min(tree)))));
        normalize();
    }
}

theorem rb_erase_two_child_splice(erased: struct rb_node*, successor: struct rb_node*,
                                  parent: struct rb_node*, color: Color,
                                  left: RbTree, right: RbTree) {
    requires rb_min_list(right)
        == List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil);

    ensures rb_inorder(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor)))
        == list_append(rb_inorder(left), rb_inorder(right)) by {
        unfold(rb_inorder(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor))));
        apply(rb_reparent_preserves_inorder(left, successor));
        rewrite(rb_inorder(rb_reparent(left, successor)) == rb_inorder(left));
        apply(rb_reparent_preserves_inorder(rb_remove_min(right), successor));
        rewrite(rb_inorder(rb_reparent(rb_remove_min(right), successor))
            == rb_inorder(rb_remove_min(right)));
        apply(rb_min_list_splits_inorder(right));
        rewrite(rb_inorder(right)
            == list_append(rb_min_list(right), rb_inorder(rb_remove_min(right))));
        rewrite(rb_min_list(right)
            == List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil));
        unfold(list_append(
            List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil),
            rb_inorder(rb_remove_min(right))));
        unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(rb_remove_min(right))));
        normalize();
    }
}

function rb_node_is(a: struct rb_node*, b: struct rb_node*) -> int32 {
    if a == b { 1 } else { 0 }
}

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
    }
}

function rb_parent_consistent(t: RbTree, p: struct rb_node*) -> int32
    decreases t
{
    match t {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if rb_parent_consistent(left, node) == 1 {
                if rb_parent_consistent(right, node) == 1 {
                    if rb_node_is(parent, p) == 1 { 1 } else { 0 }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function rb_leaf(node: struct rb_node*, parent: struct rb_node*) -> RbTree {
    RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)
}

theorem rb_node_is_reflexive(a: struct rb_node*) {
    ensures rb_node_is(a, a) == 1 by {
        unfold(rb_node_is(a, a));
        normalize();
    }
}

theorem rb_node_is_equal(a: struct rb_node*, b: struct rb_node*) {
    requires a == b;

    ensures rb_node_is(a, b) == 1 by {
        unfold(rb_node_is(a, b));
        normalize() using { a == b; }
    }
}

theorem rb_node_is_same(a: struct rb_node*, b: struct rb_node*) {
    requires rb_node_is(a, b) == 1;

    ensures a == b by {
        if a == b {
            assumption();
        } else {
            have rb_node_is(a, b) != 1 by {
                unfold(rb_node_is(a, b));
                normalize() using { not(a == b); }
            }
            contradiction(rb_node_is(a, b) == 1);
        }
    }
}

theorem rb_parent_is_node_is(node: struct rb_node*, parent: struct rb_node*, color: Color,
                             left: RbTree, right: RbTree, p: struct rb_node*) {
    ensures rb_parent_is(RbTree::Node(node, parent, color, left, right), p)
        == rb_node_is(parent, p) by {
        unfold(rb_parent_is(RbTree::Node(node, parent, color, left, right), p));
        unfold(rb_node_is(parent, p));
        normalize();
    }
}

theorem rb_parent_consistent_empty(p: struct rb_node*) {
    ensures rb_parent_consistent(RbTree::Empty, p) == 1 by {
        unfold(rb_parent_consistent(RbTree::Empty, p));
        normalize();
    }
}

theorem rb_parent_consistent_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                  left: RbTree, right: RbTree, p: struct rb_node*) {
    requires rb_node_is(parent, p) == 1;
    requires rb_parent_consistent(left, node) == 1;
    requires rb_parent_consistent(right, node) == 1;

    ensures rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1 by {
        unfold(rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p));
        rewrite(rb_node_is(parent, p) == 1);
        normalize() using {
            rb_parent_consistent(left, node) == 1;
            rb_parent_consistent(right, node) == 1;
        }
    }
}

theorem rb_parent_consistent_node_left(node: struct rb_node*, parent: struct rb_node*,
                                       color: Color, left: RbTree, right: RbTree,
                                       p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(left, node) == 1 by {
        if rb_parent_consistent(left, node) == 1 {
            assumption();
        } else {
            have rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_consistent(
                    RbTree::Node(node, parent, color, left, right), p));
                normalize() using { not(rb_parent_consistent(left, node) == 1); }
            }
            contradiction(rb_parent_consistent(
                RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_parent_consistent_node_right(node: struct rb_node*, parent: struct rb_node*,
                                        color: Color, left: RbTree, right: RbTree,
                                        p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(right, node) == 1 by {
        if rb_parent_consistent(right, node) == 1 {
            assumption();
        } else {
            apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
            have rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_consistent(
                    RbTree::Node(node, parent, color, left, right), p));
                normalize() using {
                    rb_parent_consistent(left, node) == 1;
                    not(rb_parent_consistent(right, node) == 1);
                }
            }
            contradiction(rb_parent_consistent(
                RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_parent_consistent_node_parent(node: struct rb_node*, parent: struct rb_node*,
                                         color: Color, left: RbTree, right: RbTree,
                                         p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_node_is(parent, p) == 1 by {
        if rb_node_is(parent, p) == 1 {
            assumption();
        } else {
            apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
            apply(rb_parent_consistent_node_right(node, parent, color, left, right, p));
            have rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_consistent(
                    RbTree::Node(node, parent, color, left, right), p));
                normalize() using {
                    rb_parent_consistent(left, node) == 1;
                    rb_parent_consistent(right, node) == 1;
                    not(rb_node_is(parent, p) == 1);
                }
            }
            contradiction(rb_parent_consistent(
                RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_reparent_parent_consistent_at(tree: RbTree, p: struct rb_node*,
                                         new_parent: struct rb_node*, q: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;
    requires rb_node_is(new_parent, q) == 1;

    ensures rb_parent_consistent(rb_reparent(tree, new_parent), q) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                apply(rb_parent_consistent_empty(q));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
                apply(rb_parent_consistent_node_right(node, parent, color, left, right, p));
                apply(rb_parent_consistent_node(node, new_parent, color, left, right, q));
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                assumption();
            }
        }
    }
}

theorem rb_reparent_parent_consistent(tree: RbTree, p: struct rb_node*,
                                      new_parent: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_reparent(tree, new_parent), new_parent) == 1 by {
        apply(rb_node_is_reflexive(new_parent));
        apply(rb_reparent_parent_consistent_at(tree, p, new_parent, new_parent));
        assumption();
    }
}

theorem rb_rotate_left_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                              color: Color, left: RbTree, right: RbTree,
                                              p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(
        rb_rotate_left(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(right) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left, RbTree::Empty)));
                assumption();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right), p));
                apply(rb_parent_consistent_node_right(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right), p));
                apply(rb_parent_consistent_node_parent(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right), p));
                apply(rb_parent_consistent_node_left(pivot, pivot_parent, pivot_color,
                    middle, far_right, node));
                apply(rb_parent_consistent_node_right(pivot, pivot_parent, pivot_color,
                    middle, far_right, node));
                apply(rb_reparent_parent_consistent(middle, pivot, node));
                apply(rb_node_is_reflexive(pivot));
                apply(rb_parent_consistent_node(node, pivot, color, left,
                    rb_reparent(middle, node), pivot));
                apply(rb_parent_consistent_node(pivot, parent, pivot_color,
                    RbTree::Node(node, pivot, color, left, rb_reparent(middle, node)),
                    far_right, p));
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right))));
                assumption();
            }
        }
    }
}

theorem rb_rotate_left_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_rotate_left(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_left_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_rotate_right_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree, right: RbTree,
                                               p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(
        rb_rotate_right(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                assumption();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle) => {
                apply(rb_parent_consistent_node_left(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right, p));
                apply(rb_parent_consistent_node_right(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right, p));
                apply(rb_parent_consistent_node_left(pivot, pivot_parent, pivot_color,
                    far_left, middle, node));
                apply(rb_parent_consistent_node_right(pivot, pivot_parent, pivot_color,
                    far_left, middle, node));
                apply(rb_reparent_parent_consistent(middle, pivot, node));
                apply(rb_node_is_reflexive(pivot));
                apply(rb_parent_consistent_node(node, pivot, color,
                    rb_reparent(middle, node), right, pivot));
                apply(rb_parent_consistent_node(pivot, parent, pivot_color, far_left,
                    RbTree::Node(node, pivot, color, rb_reparent(middle, node), right), p));
                unfold(rb_rotate_right(RbTree::Node(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right)));
                assumption();
            }
        }
    }
}

theorem rb_rotate_right_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_rotate_right(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_right_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_recolor_parent_consistent(tree: RbTree, color: Color, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_recolor(tree, color), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, color));
                assumption();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, old_color, left, right, p));
                apply(rb_parent_consistent_node_right(node, parent, old_color, left, right, p));
                apply(rb_parent_consistent_node_parent(node, parent, old_color, left, right, p));
                apply(rb_parent_consistent_node(node, parent, color, left, right, p));
                unfold(rb_recolor(RbTree::Node(node, parent, old_color, left, right), color));
                assumption();
            }
        }
    }
}

theorem rb_leaf_parent_consistent(node: struct rb_node*, parent: struct rb_node*) {
    ensures rb_parent_consistent(rb_leaf(node, parent), parent) == 1 by {
        apply(rb_parent_consistent_empty(node));
        apply(rb_node_is_reflexive(parent));
        apply(rb_parent_consistent_node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty,
            parent));
        unfold(rb_leaf(node, parent));
        assumption();
    }
}

theorem rb_insert_leaf_left_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                              color: Color, right: RbTree,
                                              fresh: struct rb_node*, p: struct rb_node*) {
    requires rb_parent_consistent(
        RbTree::Node(node, parent, color, RbTree::Empty, right), p) == 1;

    ensures rb_parent_consistent(
        RbTree::Node(node, parent, color, rb_leaf(fresh, node), right), p) == 1 by {
        apply(rb_parent_consistent_node_right(node, parent, color, RbTree::Empty, right, p));
        apply(rb_parent_consistent_node_parent(node, parent, color, RbTree::Empty, right, p));
        apply(rb_leaf_parent_consistent(fresh, node));
        apply(rb_parent_consistent_node(node, parent, color, rb_leaf(fresh, node), right, p));
        assumption();
    }
}

theorem rb_insert_leaf_right_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree,
                                               fresh: struct rb_node*, p: struct rb_node*) {
    requires rb_parent_consistent(
        RbTree::Node(node, parent, color, left, RbTree::Empty), p) == 1;

    ensures rb_parent_consistent(
        RbTree::Node(node, parent, color, left, rb_leaf(fresh, node)), p) == 1 by {
        apply(rb_parent_consistent_node_left(node, parent, color, left, RbTree::Empty, p));
        apply(rb_parent_consistent_node_parent(node, parent, color, left, RbTree::Empty, p));
        apply(rb_leaf_parent_consistent(fresh, node));
        apply(rb_parent_consistent_node(node, parent, color, left, rb_leaf(fresh, node), p));
        assumption();
    }
}

theorem rb_remove_min_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                             color: Color, left: RbTree, right: RbTree,
                                             p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;
    requires rb_parent_consistent(rb_remove_min(left), node) == 1;

    ensures rb_parent_consistent(
        rb_remove_min(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(left) as ih {
            RbTree::Empty => {
                apply(rb_parent_consistent_node_right(node, parent, color, RbTree::Empty,
                    right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color, RbTree::Empty,
                    right, p));
                apply(rb_reparent_parent_consistent_at(right, node, parent, p));
                unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                assumption();
            }
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) => {
                apply(rb_parent_consistent_node_right(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right, p));
                apply(rb_parent_consistent_node(node, parent, color,
                    rb_remove_min(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    right, p));
                unfold(rb_remove_min(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                assumption();
            }
        }
    }
}

theorem rb_remove_min_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_remove_min(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_remove_min(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
                apply(ih(left, node));
                apply(rb_remove_min_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_erase_two_child_splice_parent_consistent(erased: struct rb_node*,
                                                    successor: struct rb_node*,
                                                    parent: struct rb_node*, color: Color,
                                                    left: RbTree, right: RbTree,
                                                    p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(erased, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor)), p) == 1 by {
        apply(rb_parent_consistent_node_left(erased, parent, color, left, right, p));
        apply(rb_parent_consistent_node_right(erased, parent, color, left, right, p));
        apply(rb_parent_consistent_node_parent(erased, parent, color, left, right, p));
        apply(rb_reparent_parent_consistent(left, erased, successor));
        apply(rb_remove_min_parent_consistent(right, erased));
        apply(rb_reparent_parent_consistent(rb_remove_min(right), erased, successor));
        apply(rb_parent_consistent_node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor), p));
        assumption();
    }
}

function plug(ctx: Context, sub: RbTree) -> RbTree
    decreases ctx
{
    match ctx {
        Context::Top => sub,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model)),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub)),
    }
}

function ctx_consistent(ctx: Context, sub: RbTree, root_parent: struct rb_node*) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => if rb_parent_consistent(sub, root_parent) == 1 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if rb_parent_consistent(sub, identity) == 1 {
                if rb_parent_consistent(sibling_model, identity) == 1 {
                    if ctx_consistent(up_model,
                            RbTree::Node(identity, grandparent, color, sub, sibling_model),
                            root_parent) == 1 {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if rb_parent_consistent(sub, identity) == 1 {
                if rb_parent_consistent(sibling_model, identity) == 1 {
                    if ctx_consistent(up_model,
                            RbTree::Node(identity, grandparent, color, sibling_model, sub),
                            root_parent) == 1 {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

theorem plug_inorder_transport(ctx: Context, a: RbTree, b: RbTree) {
    requires rb_inorder(a) == rb_inorder(b);

    ensures rb_inorder(plug(ctx, a)) == rb_inorder(plug(ctx, b)) by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, a));
                unfold(plug(Context::Top, b));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have rb_inorder(RbTree::Node(identity, grandparent, color, a, sibling_model))
                    == rb_inorder(RbTree::Node(identity, grandparent, color, b, sibling_model)) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, a, sibling_model)));
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, b, sibling_model)));
                    rewrite(rb_inorder(a) == rb_inorder(b));
                    normalize();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, a, sibling_model),
                    RbTree::Node(identity, grandparent, color, b, sibling_model)));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    a));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    b));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, a))
                    == rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, b)) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sibling_model, a)));
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sibling_model, b)));
                    rewrite(rb_inorder(a) == rb_inorder(b));
                    normalize();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, a),
                    RbTree::Node(identity, grandparent, color, sibling_model, b)));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    a));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    b));
                assumption();
            }
        }
    }
}

theorem ctx_consistent_top(sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(Context::Top, sub, root_parent) == 1;

    ensures rb_parent_consistent(sub, root_parent) == 1 by {
        if rb_parent_consistent(sub, root_parent) == 1 {
            assumption();
        } else {
            have ctx_consistent(Context::Top, sub, root_parent) != 1 by {
                unfold(ctx_consistent(Context::Top, sub, root_parent));
                normalize() using { not(rb_parent_consistent(sub, root_parent) == 1); }
            }
            contradiction(ctx_consistent(Context::Top, sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_top_frame(sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(sub, root_parent) == 1;

    ensures ctx_consistent(Context::Top, sub, root_parent) == 1 by {
        unfold(ctx_consistent(Context::Top, sub, root_parent));
        normalize() using { rb_parent_consistent(sub, root_parent) == 1; }
    }
}

theorem ctx_consistent_left_focus(identity: struct rb_node*, grandparent: struct rb_node*,
                                  color: Color, sibling_model: RbTree, up_model: Context,
                                  sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sub, identity) == 1 by {
        if rb_parent_consistent(sub, identity) == 1 {
            assumption();
        } else {
            have ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using { not(rb_parent_consistent(sub, identity) == 1); }
            }
            contradiction(ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_left_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                                    color: Color, sibling_model: RbTree, up_model: Context,
                                    sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sibling_model, identity) == 1 by {
        if rb_parent_consistent(sibling_model, identity) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    not(rb_parent_consistent(sibling_model, identity) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_left_up(identity: struct rb_node*, grandparent: struct rb_node*,
                               color: Color, sibling_model: RbTree, up_model: Context,
                               sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sub, sibling_model), root_parent) == 1 by {
        if ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sub, sibling_model),
                root_parent) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            apply(ctx_consistent_left_sibling(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    rb_parent_consistent(sibling_model, identity) == 1;
                    not(ctx_consistent(up_model,
                        RbTree::Node(identity, grandparent, color, sub, sibling_model),
                        root_parent) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_left_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                                  color: Color, sibling_model: RbTree, up_model: Context,
                                  sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(sub, identity) == 1;
    requires rb_parent_consistent(sibling_model, identity) == 1;
    requires ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sub, sibling_model), root_parent) == 1;

    ensures ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1 by {
        unfold(ctx_consistent(
            Context::Left(identity, grandparent, color, sibling_model, up_model),
            sub, root_parent));
        normalize() using {
            rb_parent_consistent(sub, identity) == 1;
            rb_parent_consistent(sibling_model, identity) == 1;
            ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sub, sibling_model),
                root_parent) == 1;
        }
    }
}

theorem ctx_consistent_right_focus(identity: struct rb_node*, grandparent: struct rb_node*,
                                   color: Color, sibling_model: RbTree, up_model: Context,
                                   sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sub, identity) == 1 by {
        if rb_parent_consistent(sub, identity) == 1 {
            assumption();
        } else {
            have ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using { not(rb_parent_consistent(sub, identity) == 1); }
            }
            contradiction(ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_right_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                                     color: Color, sibling_model: RbTree, up_model: Context,
                                     sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sibling_model, identity) == 1 by {
        if rb_parent_consistent(sibling_model, identity) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    not(rb_parent_consistent(sibling_model, identity) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_right_up(identity: struct rb_node*, grandparent: struct rb_node*,
                                color: Color, sibling_model: RbTree, up_model: Context,
                                sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sibling_model, sub), root_parent) == 1 by {
        if ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sibling_model, sub),
                root_parent) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            apply(ctx_consistent_right_sibling(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    rb_parent_consistent(sibling_model, identity) == 1;
                    not(ctx_consistent(up_model,
                        RbTree::Node(identity, grandparent, color, sibling_model, sub),
                        root_parent) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_right_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                                   color: Color, sibling_model: RbTree, up_model: Context,
                                   sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(sub, identity) == 1;
    requires rb_parent_consistent(sibling_model, identity) == 1;
    requires ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sibling_model, sub), root_parent) == 1;

    ensures ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1 by {
        unfold(ctx_consistent(
            Context::Right(identity, grandparent, color, sibling_model, up_model),
            sub, root_parent));
        normalize() using {
            rb_parent_consistent(sub, identity) == 1;
            rb_parent_consistent(sibling_model, identity) == 1;
            ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sibling_model, sub),
                root_parent) == 1;
        }
    }
}

theorem plug_parent_consistent_transport(ctx: Context, sub: RbTree,
                                         root_parent: struct rb_node*) {
    requires ctx_consistent(ctx, sub, root_parent) == 1;

    ensures rb_parent_consistent(plug(ctx, sub), root_parent) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(sub, root_parent));
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_consistent_left_up(identity, grandparent, color, sibling_model,
                    up_model, sub, root_parent));
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sub, sibling_model),
                    root_parent));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_consistent_right_up(identity, grandparent, color, sibling_model,
                    up_model, sub, root_parent));
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, sub),
                    root_parent));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub));
                assumption();
            }
        }
    }
}

function color_black(color: Color) -> int32 {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function frame_black_height(color: Color, bh: Nat) -> Nat {
    match color {
        Color::Red => bh,
        Color::Black => Nat::Succ(bh),
    }
}

function node_color_ok(color: Color, left_color: Color, right_color: Color) -> int32 {
    match color {
        Color::Red =>
            if color_black(left_color) == 1 {
                if color_black(right_color) == 1 {
                    1
                } else {
                    0
                }
            } else {
                0
            },
        Color::Black => 1,
    }
}

theorem color_black_red() {
    ensures color_black(Color::Red) == 0 by {
        unfold(color_black(Color::Red));
        normalize();
    }
}

theorem color_black_black() {
    ensures color_black(Color::Black) == 1 by {
        unfold(color_black(Color::Black));
        normalize();
    }
}

theorem frame_black_height_red(bh: Nat) {
    ensures frame_black_height(Color::Red, bh) == bh by {
        unfold(frame_black_height(Color::Red, bh));
        normalize();
    }
}

theorem frame_black_height_black(bh: Nat) {
    ensures frame_black_height(Color::Black, bh) == Nat::Succ(bh) by {
        unfold(frame_black_height(Color::Black, bh));
        normalize();
    }
}

theorem rb_root_black_is_color_black(tree: RbTree) {
    ensures rb_root_black(tree) == color_black(rb_color(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_root_black(RbTree::Empty));
                unfold(rb_color(RbTree::Empty));
                unfold(color_black(Color::Black));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_root_black(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
                unfold(color_black(color));
                normalize();
            }
        }
    }
}

theorem color_black_of_rb_color(tree: RbTree) {
    ensures color_black(rb_color(tree)) == rb_root_black(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_root_black(RbTree::Empty));
                unfold(rb_color(RbTree::Empty));
                unfold(color_black(Color::Black));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_root_black(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
                unfold(color_black(color));
                normalize();
            }
        }
    }
}

theorem black_height_node_frame(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                left: RbTree, right: RbTree) {
    ensures black_height(RbTree::Node(node, parent, color, left, right))
        == frame_black_height(color, black_height(left)) by {
        unfold(black_height(RbTree::Node(node, parent, color, left, right)));
        unfold(frame_black_height(color, black_height(left)));
        normalize();
    }
}

theorem rb_color_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                      left: RbTree, right: RbTree) {
    ensures rb_color(RbTree::Node(node, parent, color, left, right)) == color by {
        unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
        normalize();
    }
}

theorem node_color_ok_black(left_color: Color, right_color: Color) {
    ensures node_color_ok(Color::Black, left_color, right_color) == 1 by {
        unfold(node_color_ok(Color::Black, left_color, right_color));
        normalize();
    }
}

theorem node_color_ok_red(left_color: Color, right_color: Color) {
    requires color_black(left_color) == 1;
    requires color_black(right_color) == 1;

    ensures node_color_ok(Color::Red, left_color, right_color) == 1 by {
        unfold(node_color_ok(Color::Red, left_color, right_color));
        normalize() using {
            color_black(left_color) == 1;
            color_black(right_color) == 1;
        }
    }
}

theorem node_color_ok_red_left(left_color: Color, right_color: Color) {
    requires node_color_ok(Color::Red, left_color, right_color) == 1;

    ensures color_black(left_color) == 1 by {
        if color_black(left_color) == 1 {
            assumption();
        } else {
            have node_color_ok(Color::Red, left_color, right_color) != 1 by {
                unfold(node_color_ok(Color::Red, left_color, right_color));
                normalize() using { not(color_black(left_color) == 1); }
            }
            contradiction(node_color_ok(Color::Red, left_color, right_color) == 1);
        }
    }
}

theorem node_color_ok_red_right(left_color: Color, right_color: Color) {
    requires node_color_ok(Color::Red, left_color, right_color) == 1;

    ensures color_black(right_color) == 1 by {
        if color_black(right_color) == 1 {
            assumption();
        } else {
            apply(node_color_ok_red_left(left_color, right_color));
            have node_color_ok(Color::Red, left_color, right_color) != 1 by {
                unfold(node_color_ok(Color::Red, left_color, right_color));
                normalize() using {
                    color_black(left_color) == 1;
                    not(color_black(right_color) == 1);
                }
            }
            contradiction(node_color_ok(Color::Red, left_color, right_color) == 1);
        }
    }
}

theorem is_rb_red_node_value(node: struct rb_node*, parent: struct rb_node*,
                             left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);
    requires rb_root_black(left) == 1;

    ensures rb_root_black(right)
        == is_rb(RbTree::Node(node, parent, Color::Red, left, right)) by {
        unfold(is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
            rb_root_black(left) == 1;
        }
    }
}

theorem is_rb_red_node_right_child_is_black(node: struct rb_node*, parent: struct rb_node*,
                                            left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1;

    ensures rb_root_black(right) == 1 by {
        apply(is_rb_node_left(node, parent, Color::Red, left, right));
        apply(is_rb_node_right(node, parent, Color::Red, left, right));
        apply(is_rb_node_black_heights(node, parent, Color::Red, left, right));
        apply(is_rb_red_node_children_are_black(node, parent, left, right));
        apply(is_rb_red_node_value(node, parent, left, right));
        rewrite(rb_root_black(right)
            == is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
        assumption();
    }
}

theorem is_rb_node_from_parts(node: struct rb_node*, parent: struct rb_node*, color: Color,
                              left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);
    requires node_color_ok(color, rb_color(left), rb_color(right)) == 1;

    ensures is_rb(RbTree::Node(node, parent, color, left, right)) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(is_rb_black_node(node, parent, left, right));
                assumption();
            }
            Color::Red => {
                apply(node_color_ok_red_left(rb_color(left), rb_color(right)));
                apply(node_color_ok_red_right(rb_color(left), rb_color(right)));
                apply(rb_root_black_is_color_black(left));
                apply(rb_root_black_is_color_black(right));
                have rb_root_black(left) == 1 by {
                    rewrite(rb_root_black(left) == color_black(rb_color(left)));
                    assumption();
                }
                have rb_root_black(right) == 1 by {
                    rewrite(rb_root_black(right) == color_black(rb_color(right)));
                    assumption();
                }
                apply(is_rb_red_node(node, parent, left, right));
                assumption();
            }
        }
    }
}

theorem is_rb_node_colors(node: struct rb_node*, parent: struct rb_node*, color: Color,
                          left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures node_color_ok(color, rb_color(left), rb_color(right)) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(node_color_ok_black(rb_color(left), rb_color(right)));
                assumption();
            }
            Color::Red => {
                apply(is_rb_red_node_children_are_black(node, parent, left, right));
                apply(is_rb_red_node_right_child_is_black(node, parent, left, right));
                apply(color_black_of_rb_color(left));
                apply(color_black_of_rb_color(right));
                have color_black(rb_color(left)) == 1 by {
                    rewrite(color_black(rb_color(left)) == rb_root_black(left));
                    assumption();
                }
                have color_black(rb_color(right)) == 1 by {
                    rewrite(color_black(rb_color(right)) == rb_root_black(right));
                    assumption();
                }
                apply(node_color_ok_red(rb_color(left), rb_color(right)));
                assumption();
            }
        }
    }
}

theorem is_rb_root_from_parts(tree: RbTree) {
    requires is_rb(tree) == 1;
    requires rb_root_black(tree) == 1;

    ensures is_rb_root(tree) == 1 by {
        unfold(is_rb_root(tree));
        rewrite(rb_root_black(tree) == 1);
        normalize() using { is_rb(tree) == 1; }
    }
}

function ctx_rb(ctx: Context, bh: Nat, focus_color: Color) -> int32
    decreases ctx
{
    match ctx {
        Context::Top =>
            if color_black(focus_color) == 1 {
                1
            } else {
                0
            },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if is_rb(sibling_model) == 1 {
                if bh == black_height(sibling_model) {
                    if node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 {
                        ctx_rb(up_model, frame_black_height(color, bh), color)
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if is_rb(sibling_model) == 1 {
                if black_height(sibling_model) == bh {
                    if node_color_ok(color, rb_color(sibling_model), focus_color) == 1 {
                        ctx_rb(up_model, frame_black_height(color, bh), color)
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

theorem ctx_rb_top(bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Top, bh, focus_color) == 1;

    ensures color_black(focus_color) == 1 by {
        if color_black(focus_color) == 1 {
            assumption();
        } else {
            have ctx_rb(Context::Top, bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Top, bh, focus_color));
                normalize() using { not(color_black(focus_color) == 1); }
            }
            contradiction(ctx_rb(Context::Top, bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_top_frame(bh: Nat, focus_color: Color) {
    requires color_black(focus_color) == 1;

    ensures ctx_rb(Context::Top, bh, focus_color) == 1 by {
        unfold(ctx_rb(Context::Top, bh, focus_color));
        normalize() using { color_black(focus_color) == 1; }
    }
}

theorem ctx_rb_left_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                            color: Color, sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures is_rb(sibling_model) == 1 by {
        if is_rb(sibling_model) == 1 {
            assumption();
        } else {
            have ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using { not(is_rb(sibling_model) == 1); }
            }
            contradiction(ctx_rb(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_left_height(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures bh == black_height(sibling_model) by {
        if bh == black_height(sibling_model) {
            assumption();
        } else {
            apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    not(bh == black_height(sibling_model));
                }
            }
            contradiction(ctx_rb(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_left_colors(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 by {
        if node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 {
            assumption();
        } else {
            apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    bh == black_height(sibling_model);
                    not(node_color_ok(color, focus_color, rb_color(sibling_model)) == 1);
                }
            }
            contradiction(ctx_rb(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_left_value(identity: struct rb_node*, grandparent: struct rb_node*,
                          color: Color, sibling_model: RbTree, up_model: Context,
                          bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires bh == black_height(sibling_model);
    requires node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color)
        == ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color) by {
        unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        normalize() using {
            is_rb(sibling_model) == 1;
            bh == black_height(sibling_model);
            node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;
        }
    }
}

theorem ctx_rb_left_up(identity: struct rb_node*, grandparent: struct rb_node*,
                       color: Color, sibling_model: RbTree, up_model: Context,
                       bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color) == 1 by {
        apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_value(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color)
            == ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_left_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                          color: Color, sibling_model: RbTree, up_model: Context,
                          bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires bh == black_height(sibling_model);
    requires node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;
    requires ctx_rb(up_model, frame_black_height(color, bh), color) == 1;

    ensures ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1 by {
        unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color) == 1);
        normalize() using {
            is_rb(sibling_model) == 1;
            bh == black_height(sibling_model);
            node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;
        }
    }
}

theorem ctx_rb_right_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                             color: Color, sibling_model: RbTree, up_model: Context,
                             bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures is_rb(sibling_model) == 1 by {
        if is_rb(sibling_model) == 1 {
            assumption();
        } else {
            have ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using { not(is_rb(sibling_model) == 1); }
            }
            contradiction(ctx_rb(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_right_height(identity: struct rb_node*, grandparent: struct rb_node*,
                            color: Color, sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures black_height(sibling_model) == bh by {
        if black_height(sibling_model) == bh {
            assumption();
        } else {
            apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    not(black_height(sibling_model) == bh);
                }
            }
            contradiction(ctx_rb(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_right_colors(identity: struct rb_node*, grandparent: struct rb_node*,
                            color: Color, sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures node_color_ok(color, rb_color(sibling_model), focus_color) == 1 by {
        if node_color_ok(color, rb_color(sibling_model), focus_color) == 1 {
            assumption();
        } else {
            apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    black_height(sibling_model) == bh;
                    not(node_color_ok(color, rb_color(sibling_model), focus_color) == 1);
                }
            }
            contradiction(ctx_rb(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_right_value(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires black_height(sibling_model) == bh;
    requires node_color_ok(color, rb_color(sibling_model), focus_color) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color)
        == ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color) by {
        unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        normalize() using {
            is_rb(sibling_model) == 1;
            black_height(sibling_model) == bh;
            node_color_ok(color, rb_color(sibling_model), focus_color) == 1;
        }
    }
}

theorem ctx_rb_right_up(identity: struct rb_node*, grandparent: struct rb_node*,
                        color: Color, sibling_model: RbTree, up_model: Context,
                        bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color) == 1 by {
        apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_value(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color)
            == ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_right_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires black_height(sibling_model) == bh;
    requires node_color_ok(color, rb_color(sibling_model), focus_color) == 1;
    requires ctx_rb(up_model, frame_black_height(color, bh), color) == 1;

    ensures ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1 by {
        unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color) == 1);
        normalize() using {
            is_rb(sibling_model) == 1;
            black_height(sibling_model) == bh;
            node_color_ok(color, rb_color(sibling_model), focus_color) == 1;
        }
    }
}

theorem plug_rb_from_ctx_rb(ctx: Context, sub: RbTree) {
    requires is_rb(sub) == 1;
    requires ctx_rb(ctx, black_height(sub), rb_color(sub)) == 1;

    ensures is_rb_root(plug(ctx, sub)) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_rb_top(black_height(sub), rb_color(sub)));
                apply(rb_root_black_is_color_black(sub));
                have rb_root_black(sub) == 1 by {
                    rewrite(rb_root_black(sub) == color_black(rb_color(sub)));
                    assumption();
                }
                apply(is_rb_root_from_parts(sub));
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_left_up(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(is_rb_node_from_parts(identity, grandparent, color, sub, sibling_model));
                apply(black_height_node_frame(identity, grandparent, color, sub, sibling_model));
                apply(rb_color_node(identity, grandparent, color, sub, sibling_model));
                have ctx_rb(up_model,
                        black_height(RbTree::Node(identity, grandparent, color, sub,
                            sibling_model)),
                        rb_color(RbTree::Node(identity, grandparent, color, sub,
                            sibling_model))) == 1 by {
                    rewrite(black_height(RbTree::Node(identity, grandparent, color, sub,
                        sibling_model)) == frame_black_height(color, black_height(sub)));
                    rewrite(rb_color(RbTree::Node(identity, grandparent, color, sub,
                        sibling_model)) == color);
                    assumption();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sub, sibling_model)));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_right_up(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(is_rb_node_from_parts(identity, grandparent, color, sibling_model, sub));
                apply(black_height_node_frame(identity, grandparent, color, sibling_model, sub));
                apply(rb_color_node(identity, grandparent, color, sibling_model, sub));
                have ctx_rb(up_model,
                        black_height(RbTree::Node(identity, grandparent, color, sibling_model,
                            sub)),
                        rb_color(RbTree::Node(identity, grandparent, color, sibling_model,
                            sub))) == 1 by {
                    rewrite(rb_color(RbTree::Node(identity, grandparent, color, sibling_model,
                        sub)) == color);
                    rewrite(black_height(RbTree::Node(identity, grandparent, color,
                        sibling_model, sub))
                        == frame_black_height(color, black_height(sibling_model)));
                    rewrite(black_height(sibling_model) == black_height(sub));
                    assumption();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, sub)));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), sub));
                assumption();
            }
        }
    }
}

theorem is_rb_root_is_rb(tree: RbTree) {
    requires is_rb_root(tree) == 1;

    ensures is_rb(tree) == 1 by {
        if is_rb(tree) == 1 {
            assumption();
        } else {
            have is_rb_root(tree) != 1 by {
                unfold(is_rb_root(tree));
                normalize() using { not(is_rb(tree) == 1); }
            }
            contradiction(is_rb_root(tree) == 1);
        }
    }
}

theorem is_rb_root_value(tree: RbTree) {
    requires is_rb(tree) == 1;

    ensures rb_root_black(tree) == is_rb_root(tree) by {
        unfold(is_rb_root(tree));
        normalize() using { is_rb(tree) == 1; }
    }
}

theorem is_rb_root_root_black(tree: RbTree) {
    requires is_rb_root(tree) == 1;

    ensures rb_root_black(tree) == 1 by {
        apply(is_rb_root_is_rb(tree));
        apply(is_rb_root_value(tree));
        rewrite(rb_root_black(tree) == is_rb_root(tree));
        assumption();
    }
}

theorem node_color_ok_weaken_left(color: Color, left_color: Color, right_color: Color) {
    requires node_color_ok(color, left_color, right_color) == 1;

    ensures node_color_ok(color, Color::Black, right_color) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(node_color_ok_black(Color::Black, right_color));
                assumption();
            }
            Color::Red => {
                apply(node_color_ok_red_right(left_color, right_color));
                apply(color_black_black());
                apply(node_color_ok_red(Color::Black, right_color));
                assumption();
            }
        }
    }
}

theorem node_color_ok_weaken_right(color: Color, left_color: Color, right_color: Color) {
    requires node_color_ok(color, left_color, right_color) == 1;

    ensures node_color_ok(color, left_color, Color::Black) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(node_color_ok_black(left_color, Color::Black));
                assumption();
            }
            Color::Red => {
                apply(node_color_ok_red_left(left_color, right_color));
                apply(color_black_black());
                apply(node_color_ok_red(left_color, Color::Black));
                assumption();
            }
        }
    }
}

function ctx_almost_rb_insert(ctx: Context, bh: Nat) -> int32 {
    ctx_rb(ctx, bh, Color::Black)
}

theorem ctx_almost_rb_insert_unfolds(ctx: Context, bh: Nat) {
    ensures ctx_almost_rb_insert(ctx, bh) == ctx_rb(ctx, bh, Color::Black) by {
        unfold(ctx_almost_rb_insert(ctx, bh));
        normalize();
    }
}

theorem ctx_almost_rb_insert_folds(ctx: Context, bh: Nat) {
    ensures ctx_rb(ctx, bh, Color::Black) == ctx_almost_rb_insert(ctx, bh) by {
        unfold(ctx_almost_rb_insert(ctx, bh));
        normalize();
    }
}

theorem ctx_almost_rb_insert_holds(ctx: Context, bh: Nat) {
    requires ctx_rb(ctx, bh, Color::Black) == 1;

    ensures ctx_almost_rb_insert(ctx, bh) == 1 by {
        apply(ctx_almost_rb_insert_unfolds(ctx, bh));
        rewrite(ctx_almost_rb_insert(ctx, bh) == ctx_rb(ctx, bh, Color::Black));
        assumption();
    }
}

theorem ctx_almost_rb_insert_black_focus(ctx: Context, bh: Nat) {
    requires ctx_almost_rb_insert(ctx, bh) == 1;

    ensures ctx_rb(ctx, bh, Color::Black) == 1 by {
        apply(ctx_almost_rb_insert_folds(ctx, bh));
        rewrite(ctx_rb(ctx, bh, Color::Black) == ctx_almost_rb_insert(ctx, bh));
        assumption();
    }
}

theorem ctx_rb_weaken_to_almost(ctx: Context, bh: Nat, focus_color: Color) {
    requires ctx_rb(ctx, bh, focus_color) == 1;

    ensures ctx_almost_rb_insert(ctx, bh) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(color_black_black());
                apply(ctx_rb_top_frame(bh, Color::Black));
                apply(ctx_almost_rb_insert_holds(Context::Top, bh));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_left_up(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(node_color_ok_weaken_left(color, focus_color, rb_color(sibling_model)));
                apply(ctx_rb_left_frame(identity, grandparent, color, sibling_model, up_model,
                    bh, Color::Black));
                apply(ctx_almost_rb_insert_holds(
                    Context::Left(identity, grandparent, color, sibling_model, up_model), bh));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_right_up(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(node_color_ok_weaken_right(color, rb_color(sibling_model), focus_color));
                apply(ctx_rb_right_frame(identity, grandparent, color, sibling_model, up_model,
                    bh, Color::Black));
                apply(ctx_almost_rb_insert_holds(
                    Context::Right(identity, grandparent, color, sibling_model, up_model), bh));
                assumption();
            }
        }
    }
}

theorem ctx_rb_left_red_up(identity: struct rb_node*, grandparent: struct rb_node*,
                           sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, bh, Color::Red) == 1 by {
        apply(ctx_rb_left_sibling(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_height(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_colors(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Red, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                bh == black_height(sibling_model);
                node_color_ok(Color::Red, focus_color, rb_color(sibling_model)) == 1;
            }
        }
        rewrite(ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_left_black_up(identity: struct rb_node*, grandparent: struct rb_node*,
                             sibling_model: RbTree, up_model: Context,
                             bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, Nat::Succ(bh), Color::Black) == 1 by {
        apply(ctx_rb_left_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_colors(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Black, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                bh == black_height(sibling_model);
                node_color_ok(Color::Black, focus_color, rb_color(sibling_model)) == 1;
            }
        }
        rewrite(ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_right_red_up(identity: struct rb_node*, grandparent: struct rb_node*,
                            sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, bh, Color::Red) == 1 by {
        apply(ctx_rb_right_sibling(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_height(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_colors(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Red, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                black_height(sibling_model) == bh;
                node_color_ok(Color::Red, rb_color(sibling_model), focus_color) == 1;
            }
        }
        rewrite(ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_right_black_up(identity: struct rb_node*, grandparent: struct rb_node*,
                              sibling_model: RbTree, up_model: Context,
                              bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, Nat::Succ(bh), Color::Black) == 1 by {
        apply(ctx_rb_right_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_colors(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(
                Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Black, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                black_height(sibling_model) == bh;
                node_color_ok(Color::Black, rb_color(sibling_model), focus_color) == 1;
            }
        }
        rewrite(ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(
                Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_black_frame_left_restores(identity: struct rb_node*, grandparent: struct rb_node*,
                                      sibling_model: RbTree, up_model: Context,
                                      bh: Nat, focus_color: Color) {
    requires ctx_almost_rb_insert(
        Context::Left(identity, grandparent, Color::Black, sibling_model, up_model), bh) == 1;

    ensures ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1 by {
        apply(ctx_almost_rb_insert_black_focus(
            Context::Left(identity, grandparent, Color::Black, sibling_model, up_model), bh));
        apply(ctx_rb_left_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_left_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_left_up(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(node_color_ok_black(focus_color, rb_color(sibling_model)));
        apply(ctx_rb_left_frame(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        assumption();
    }
}

theorem ctx_black_frame_right_restores(identity: struct rb_node*, grandparent: struct rb_node*,
                                       sibling_model: RbTree, up_model: Context,
                                       bh: Nat, focus_color: Color) {
    requires ctx_almost_rb_insert(
        Context::Right(identity, grandparent, Color::Black, sibling_model, up_model), bh) == 1;

    ensures ctx_rb(Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1 by {
        apply(ctx_almost_rb_insert_black_focus(
            Context::Right(identity, grandparent, Color::Black, sibling_model, up_model), bh));
        apply(ctx_rb_right_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_right_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_right_up(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(node_color_ok_black(rb_color(sibling_model), focus_color));
        apply(ctx_rb_right_frame(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        assumption();
    }
}

theorem ctx_insert_black_parent_exit(ctx: Context, sub: RbTree) {
    requires is_rb(sub) == 1;
    requires ctx_rb(ctx, black_height(sub), rb_color(sub)) == 1;

    ensures is_rb_root(plug(ctx, sub)) == 1 by {
        apply(plug_rb_from_ctx_rb(ctx, sub));
        assumption();
    }
}

theorem ctx_insert_root_exit(sub: RbTree) {
    requires is_rb(sub) == 1;

    ensures is_rb_root(plug(Context::Top, rb_recolor(sub, Color::Black))) == 1 by {
        apply(is_rb_is_almost_rb_insert(sub));
        apply(rb_blacken_root_restores_rb(sub));
        unfold(plug(Context::Top, rb_recolor(sub, Color::Black)));
        assumption();
    }
}

theorem node_color_ok_red_focus_is_black(color: Color, right_color: Color) {
    requires node_color_ok(color, Color::Red, right_color) == 1;

    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Black => {
                normalize();
            }
            Color::Red => {
                apply(node_color_ok_red_left(Color::Red, right_color));
                apply(color_black_red());
                have color_black(Color::Red) != 1 by {
                    rewrite(color_black(Color::Red) == 0);
                    normalize();
                }
                contradiction(color_black(Color::Red) == 1);
            }
        }
    }
}

theorem nat_eq_symmetric(x: Nat, y: Nat) {
    requires x == y;

    ensures y == x by {
        rewrite(x == y);
        normalize();
    }
}

theorem nat_eq_transitive(x: Nat, y: Nat, z: Nat) {
    requires x == y;
    requires y == z;

    ensures x == z by {
        rewrite(x == y);
        assumption();
    }
}

theorem ctx_insert_cursor_left_parent(parent: struct rb_node*, grandparent: struct rb_node*,
                                      sub: RbTree, sibling_model: RbTree, up_g: Context) {
    requires is_rb(sub) == 1;
    requires ctx_rb(Context::Left(parent, grandparent, Color::Red, sibling_model, up_g),
        black_height(sub), Color::Black) == 1;

    ensures almost_rb_insert(
        RbTree::Node(parent, grandparent, Color::Red, sub, sibling_model)) == 1 by {
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(almost_rb_insert_node(parent, grandparent, Color::Red, sub, sibling_model));
        assumption();
    }

    ensures rb_root_black(sibling_model) == 1 by {
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(sibling_model)));
        apply(rb_root_black_is_color_black(sibling_model));
        rewrite(rb_root_black(sibling_model) == color_black(rb_color(sibling_model)));
        assumption();
    }

    ensures black_height(RbTree::Node(parent, grandparent, Color::Red, sub, sibling_model))
        == black_height(sub) by {
        apply(black_height_red_node(parent, grandparent, sub, sibling_model));
        assumption();
    }

    ensures ctx_rb(up_g, black_height(sub), Color::Red) == 1 by {
        apply(ctx_rb_left_red_up(parent, grandparent, sibling_model, up_g,
            black_height(sub), Color::Black));
        assumption();
    }
}

theorem ctx_insert_cursor_right_parent(parent: struct rb_node*, grandparent: struct rb_node*,
                                       sub: RbTree, sibling_model: RbTree, up_g: Context) {
    requires is_rb(sub) == 1;
    requires ctx_rb(Context::Right(parent, grandparent, Color::Red, sibling_model, up_g),
        black_height(sub), Color::Black) == 1;

    ensures almost_rb_insert(
        RbTree::Node(parent, grandparent, Color::Red, sibling_model, sub)) == 1 by {
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(almost_rb_insert_node(parent, grandparent, Color::Red, sibling_model, sub));
        assumption();
    }

    ensures rb_root_black(sibling_model) == 1 by {
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(node_color_ok_red_left(rb_color(sibling_model), Color::Black));
        apply(rb_root_black_is_color_black(sibling_model));
        rewrite(rb_root_black(sibling_model) == color_black(rb_color(sibling_model)));
        assumption();
    }

    ensures black_height(sibling_model) == black_height(sub) by {
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        assumption();
    }

    ensures black_height(RbTree::Node(parent, grandparent, Color::Red, sibling_model, sub))
        == black_height(sub) by {
        apply(black_height_red_node(parent, grandparent, sibling_model, sub));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        rewrite(black_height(RbTree::Node(parent, grandparent, Color::Red, sibling_model, sub))
            == black_height(sibling_model));
        assumption();
    }

    ensures ctx_rb(up_g, black_height(sub), Color::Red) == 1 by {
        apply(ctx_rb_right_red_up(parent, grandparent, sibling_model, up_g,
            black_height(sub), Color::Black));
        assumption();
    }
}

theorem rb_insert_fix_recolor_shape(grandparent: struct rb_node*, above: struct rb_node*,
                                    left_node: struct rb_node*, right_node: struct rb_node*,
                                    ll: RbTree, lr: RbTree, rl: RbTree, rr: RbTree) {
    ensures rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))
        == RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)) by {
        unfold(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr))));
        unfold(rb_recolor_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr)), Color::Black));
        unfold(rb_recolor(RbTree::Node(right_node, grandparent, Color::Red, rl, rr),
            Color::Black));
        unfold(rb_recolor_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)), Color::Black));
        unfold(rb_recolor(RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            Color::Black));
        unfold(rb_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)), Color::Red));
        normalize();
    }
}

theorem rb_insert_fix_recolor_black_height(grandparent: struct rb_node*,
                                           above: struct rb_node*,
                                           left_node: struct rb_node*,
                                           right_node: struct rb_node*,
                                           ll: RbTree, lr: RbTree, rl: RbTree, rr: RbTree) {
    ensures black_height(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Red, rl, rr))))
        == Nat::Succ(black_height(ll)) by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, left_node, right_node,
            ll, lr, rl, rr));
        apply(black_height_red_node(grandparent, above,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        apply(black_height_black_node(left_node, grandparent, ll, lr));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        rewrite(black_height(RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)))
            == black_height(RbTree::Node(left_node, grandparent, Color::Black, ll, lr)));
        rewrite(black_height(RbTree::Node(left_node, grandparent, Color::Black, ll, lr))
            == Nat::Succ(black_height(ll)));
        normalize();
    }
}

theorem rb_insert_fix_recolor_root_is_red(grandparent: struct rb_node*,
                                          above: struct rb_node*,
                                          left_node: struct rb_node*,
                                          right_node: struct rb_node*,
                                          ll: RbTree, lr: RbTree, rl: RbTree, rr: RbTree) {
    ensures rb_color(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))) == Color::Red by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, left_node, right_node,
            ll, lr, rl, rr));
        apply(rb_color_node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        rewrite(rb_color(RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr))) == Color::Red);
        normalize();
    }
}

theorem ctx_insert_case1_left(above: struct rb_node*, grandparent: struct rb_node*,
                              parent: struct rb_node*, uncle: struct rb_node*,
                              a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires almost_rb_insert(RbTree::Node(parent, grandparent, Color::Red, a, b)) == 1;
    requires ctx_rb(Context::Left(grandparent, above, Color::Black,
        RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
        black_height(a), Color::Red) == 1;

    ensures is_rb(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d)))) == 1 by {
        apply(almost_rb_insert_node_left(parent, grandparent, Color::Red, a, b));
        apply(almost_rb_insert_node_right(parent, grandparent, Color::Red, a, b));
        apply(almost_rb_insert_node_black_heights(parent, grandparent, Color::Red, a, b));
        apply(ctx_rb_left_sibling(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            black_height(a), Color::Red));
        apply(is_rb_node_left(uncle, grandparent, Color::Red, c, d));
        apply(is_rb_node_right(uncle, grandparent, Color::Red, c, d));
        apply(is_rb_node_black_heights(uncle, grandparent, Color::Red, c, d));
        apply(ctx_rb_left_height(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            black_height(a), Color::Red));
        apply(black_height_red_node(uncle, grandparent, c, d));
        have black_height(a) == black_height(c) by {
            rewrite(black_height(a)
                == black_height(RbTree::Node(uncle, grandparent, Color::Red, c, d)));
            assumption();
        }
        apply(is_rb_black_node(parent, grandparent, a, b));
        apply(is_rb_black_node(uncle, grandparent, c, d));
        apply(rb_root_black_black_node(parent, grandparent, a, b));
        apply(rb_root_black_black_node(uncle, grandparent, c, d));
        apply(black_height_black_node(parent, grandparent, a, b));
        apply(black_height_black_node(uncle, grandparent, c, d));
        have black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
            == black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d)) by {
            rewrite(black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
                == Nat::Succ(black_height(a)));
            rewrite(black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d))
                == Nat::Succ(black_height(c)));
            rewrite(black_height(a) == black_height(c));
            normalize();
        }
        apply(is_rb_red_node(grandparent, above,
            RbTree::Node(parent, grandparent, Color::Black, a, b),
            RbTree::Node(uncle, grandparent, Color::Black, c, d)));
        apply(rb_insert_fix_recolor_shape(grandparent, above, parent, uncle, a, b, c, d));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d)));
        assumption();
    }

    ensures black_height(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d))))
        == Nat::Succ(black_height(a)) by {
        apply(rb_insert_fix_recolor_black_height(grandparent, above, parent, uncle,
            a, b, c, d));
        assumption();
    }

    ensures ctx_almost_rb_insert(up2, Nat::Succ(black_height(a))) == 1 by {
        apply(ctx_rb_left_black_up(grandparent, above,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            black_height(a), Color::Red));
        apply(ctx_almost_rb_insert_holds(up2, Nat::Succ(black_height(a))));
        assumption();
    }
}

theorem ctx_insert_case1_right(above: struct rb_node*, grandparent: struct rb_node*,
                               parent: struct rb_node*, uncle: struct rb_node*,
                               a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires almost_rb_insert(RbTree::Node(parent, grandparent, Color::Red, c, d)) == 1;
    requires ctx_rb(Context::Right(grandparent, above, Color::Black,
        RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
        black_height(c), Color::Red) == 1;

    ensures is_rb(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b),
            RbTree::Node(parent, grandparent, Color::Red, c, d)))) == 1 by {
        apply(almost_rb_insert_node_left(parent, grandparent, Color::Red, c, d));
        apply(almost_rb_insert_node_right(parent, grandparent, Color::Red, c, d));
        apply(almost_rb_insert_node_black_heights(parent, grandparent, Color::Red, c, d));
        apply(ctx_rb_right_sibling(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(is_rb_node_left(uncle, grandparent, Color::Red, a, b));
        apply(is_rb_node_right(uncle, grandparent, Color::Red, a, b));
        apply(is_rb_node_black_heights(uncle, grandparent, Color::Red, a, b));
        apply(ctx_rb_right_height(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(black_height_red_node(uncle, grandparent, a, b));
        have black_height(a) == black_height(c) by {
            rewrite(black_height(a)
                == black_height(RbTree::Node(uncle, grandparent, Color::Red, a, b)));
            assumption();
        }
        apply(is_rb_black_node(uncle, grandparent, a, b));
        apply(is_rb_black_node(parent, grandparent, c, d));
        apply(rb_root_black_black_node(uncle, grandparent, a, b));
        apply(rb_root_black_black_node(parent, grandparent, c, d));
        apply(black_height_black_node(uncle, grandparent, a, b));
        apply(black_height_black_node(parent, grandparent, c, d));
        have black_height(RbTree::Node(uncle, grandparent, Color::Black, a, b))
            == black_height(RbTree::Node(parent, grandparent, Color::Black, c, d)) by {
            rewrite(black_height(RbTree::Node(uncle, grandparent, Color::Black, a, b))
                == Nat::Succ(black_height(a)));
            rewrite(black_height(RbTree::Node(parent, grandparent, Color::Black, c, d))
                == Nat::Succ(black_height(c)));
            rewrite(black_height(a) == black_height(c));
            normalize();
        }
        apply(is_rb_red_node(grandparent, above,
            RbTree::Node(uncle, grandparent, Color::Black, a, b),
            RbTree::Node(parent, grandparent, Color::Black, c, d)));
        apply(rb_insert_fix_recolor_shape(grandparent, above, uncle, parent, a, b, c, d));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d)));
        assumption();
    }

    ensures black_height(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b),
            RbTree::Node(parent, grandparent, Color::Red, c, d))))
        == Nat::Succ(black_height(a)) by {
        apply(rb_insert_fix_recolor_black_height(grandparent, above, uncle, parent,
            a, b, c, d));
        assumption();
    }

    ensures ctx_almost_rb_insert(up2, Nat::Succ(black_height(c))) == 1 by {
        apply(ctx_rb_right_black_up(grandparent, above,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(ctx_almost_rb_insert_holds(up2, Nat::Succ(black_height(c))));
        assumption();
    }
}

theorem rb_insert_fix_outer_left_shape(grandparent: struct rb_node*, above: struct rb_node*,
                                       parent: struct rb_node*, cursor: struct rb_node*,
                                       a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_outer_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b), c),
            d))
        == RbTree::Node(parent, above, Color::Black,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red,
                rb_reparent(c, grandparent), d)) by {
        unfold(rb_insert_fix_outer_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_rotate_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_recolor_right(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Black,
                    rb_reparent(c, grandparent), d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black,
            rb_reparent(c, grandparent), d), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d)), Color::Black));
        normalize();
    }
}

theorem rb_insert_fix_outer_right_shape(grandparent: struct rb_node*, above: struct rb_node*,
                                        parent: struct rb_node*, cursor: struct rb_node*,
                                        a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_outer_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red, b,
                RbTree::Node(cursor, parent, Color::Red, c, d))))
        == RbTree::Node(parent, above, Color::Black,
            RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)) by {
        unfold(rb_insert_fix_outer_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_rotate_left(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_recolor_left(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Black, a,
                    rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black, a,
            rb_reparent(b, grandparent)), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Red, a,
                    rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Black));
        normalize();
    }
}

theorem ctx_insert_case3_left(above: struct rb_node*, grandparent: struct rb_node*,
                              parent: struct rb_node*, cursor: struct rb_node*,
                              a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, a, b)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(
        Context::Left(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2)),
        black_height(a), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b), c),
            d)))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, a, b));
        apply(is_rb_node_right(cursor, parent, Color::Red, a, b));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, a, b));
        apply(is_rb_red_node_children_are_black(cursor, parent, a, b));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, a, b));
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(c)));
        apply(rb_root_black_is_color_black(c));
        have rb_root_black(c) == 1 by {
            rewrite(rb_root_black(c) == color_black(rb_color(c)));
            assumption();
        }
        apply(ctx_rb_left_red_up(parent, grandparent, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(ctx_rb_left_sibling(grandparent, above, Color::Black, d, up2,
            black_height(a), Color::Red));
        apply(ctx_rb_left_height(grandparent, above, Color::Black, d, up2,
            black_height(a), Color::Red));
        apply(ctx_rb_left_black_up(grandparent, above, d, up2,
            black_height(a), Color::Red));
        apply(nat_eq_symmetric(black_height(a), black_height(b)));
        apply(nat_eq_transitive(black_height(b), black_height(a), black_height(c)));
        apply(nat_eq_symmetric(black_height(a), black_height(c)));
        apply(nat_eq_transitive(black_height(c), black_height(a), black_height(d)));
        apply(rb_insert_fix_outer_left_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_left_shape(grandparent, above, parent, cursor, a, b, c, d));
        apply(black_height_black_node(parent, above,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)));
        apply(black_height_red_node(cursor, parent, a, b));
        apply(rb_color_node(parent, above, Color::Black,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)));
        have black_height(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Nat::Succ(black_height(a)) by {
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(cursor, parent, Color::Red, a, b),
                    RbTree::Node(grandparent, parent, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(black_height(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d)))
                == Nat::Succ(black_height(RbTree::Node(cursor, parent, Color::Red, a, b))));
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, a, b))
                == black_height(a));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Color::Black by {
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(cursor, parent, Color::Red, a, b),
                    RbTree::Node(grandparent, parent, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(rb_color(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d))) == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, a, b), c),
                        d))),
                rb_color(rb_insert_fix_outer_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, a, b), c),
                        d)))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Nat::Succ(black_height(a)));
            rewrite(rb_color(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d))));
        assumption();
    }
}

theorem ctx_insert_case3_right(above: struct rb_node*, grandparent: struct rb_node*,
                               parent: struct rb_node*, cursor: struct rb_node*,
                               a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, c, d)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(
        Context::Right(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2)),
        black_height(c), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red, b,
                RbTree::Node(cursor, parent, Color::Red, c, d)))))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, c, d));
        apply(is_rb_node_right(cursor, parent, Color::Red, c, d));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, c, d));
        apply(is_rb_red_node_children_are_black(cursor, parent, c, d));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, c, d));
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(node_color_ok_red_left(rb_color(b), Color::Black));
        apply(rb_root_black_is_color_black(b));
        have rb_root_black(b) == 1 by {
            rewrite(rb_root_black(b) == color_black(rb_color(b)));
            assumption();
        }
        apply(ctx_rb_right_red_up(parent, grandparent, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(ctx_rb_right_sibling(grandparent, above, Color::Black, a, up2,
            black_height(c), Color::Red));
        apply(ctx_rb_right_height(grandparent, above, Color::Black, a, up2,
            black_height(c), Color::Red));
        apply(ctx_rb_right_black_up(grandparent, above, a, up2,
            black_height(c), Color::Red));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        apply(nat_eq_transitive(black_height(a), black_height(c), black_height(b)));
        apply(rb_insert_fix_outer_right_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_right_shape(grandparent, above, parent, cursor, a, b, c, d));
        apply(black_height_black_node(parent, above,
            RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)));
        apply(black_height_red_node(grandparent, parent, a, rb_reparent(b, grandparent)));
        apply(rb_color_node(parent, above, Color::Black,
            RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)));
        have black_height(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
            == Nat::Succ(black_height(c)) by {
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d))))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(grandparent, parent, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(cursor, parent, Color::Red, c, d)));
            rewrite(black_height(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)))
                == Nat::Succ(black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                    rb_reparent(b, grandparent)))));
            rewrite(black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent))) == black_height(a));
            rewrite(black_height(a) == black_height(c));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
            == Color::Black by {
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d))))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(grandparent, parent, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(cursor, parent, Color::Red, c, d)));
            rewrite(rb_color(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d))) == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red, b,
                            RbTree::Node(cursor, parent, Color::Red, c, d))))),
                rb_color(rb_insert_fix_outer_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red, b,
                            RbTree::Node(cursor, parent, Color::Red, c, d)))))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
                == Nat::Succ(black_height(c)));
            rewrite(rb_color(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
                == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d))))));
        assumption();
    }
}

theorem ctx_insert_case2_left(above: struct rb_node*, grandparent: struct rb_node*,
                              parent: struct rb_node*, cursor: struct rb_node*,
                              a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(
        Context::Right(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2)),
        black_height(b), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_left(rb_insert_fix_inner_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c)),
            d))))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(node_color_ok_red_left(rb_color(a), Color::Black));
        apply(rb_root_black_is_color_black(a));
        have rb_root_black(a) == 1 by {
            rewrite(rb_root_black(a) == color_black(rb_color(a)));
            assumption();
        }
        apply(ctx_rb_right_red_up(parent, grandparent, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_left_sibling(grandparent, above, Color::Black, d, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_left_height(grandparent, above, Color::Black, d, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_left_black_up(grandparent, above, d, up2,
            black_height(b), Color::Red));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        apply(nat_eq_transitive(black_height(c), black_height(b), black_height(d)));
        apply(rb_insert_fix_inner_left_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_inner_left_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_left_shape(grandparent, above, cursor, parent,
            a, rb_reparent(b, parent), c, d));
        apply(black_height_black_node(cursor, above,
            RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
            RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d)));
        apply(black_height_red_node(parent, cursor, a, rb_reparent(b, parent)));
        apply(rb_color_node(cursor, above, Color::Black,
            RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
            RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d)));
        have black_height(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Nat::Succ(black_height(b)) by {
            rewrite(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d))
                == RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d));
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                    RbTree::Node(grandparent, cursor, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(black_height(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                RbTree::Node(grandparent, cursor, Color::Red,
                    rb_reparent(c, grandparent), d)))
                == Nat::Succ(black_height(RbTree::Node(parent, cursor, Color::Red, a,
                    rb_reparent(b, parent)))));
            rewrite(black_height(RbTree::Node(parent, cursor, Color::Red, a,
                rb_reparent(b, parent))) == black_height(a));
            rewrite(black_height(a) == black_height(b));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Color::Black by {
            rewrite(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d))
                == RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d));
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                    RbTree::Node(grandparent, cursor, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(rb_color(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                RbTree::Node(grandparent, cursor, Color::Red,
                    rb_reparent(c, grandparent), d))) == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red, a,
                            RbTree::Node(cursor, parent, Color::Red, b, c)),
                        d)))),
                rb_color(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red, a,
                            RbTree::Node(cursor, parent, Color::Red, b, c)),
                        d))))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Nat::Succ(black_height(b)));
            rewrite(rb_color(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_left(rb_insert_fix_inner_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d)))));
        assumption();
    }
}

theorem ctx_insert_case2_right(above: struct rb_node*, grandparent: struct rb_node*,
                               parent: struct rb_node*, cursor: struct rb_node*,
                               a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(
        Context::Left(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2)),
        black_height(b), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_right(rb_insert_fix_inner_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d)))))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(d)));
        apply(rb_root_black_is_color_black(d));
        have rb_root_black(d) == 1 by {
            rewrite(rb_root_black(d) == color_black(rb_color(d)));
            assumption();
        }
        apply(ctx_rb_left_red_up(parent, grandparent, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_right_sibling(grandparent, above, Color::Black, a, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_right_height(grandparent, above, Color::Black, a, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_right_black_up(grandparent, above, a, up2,
            black_height(b), Color::Red));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        apply(nat_eq_transitive(black_height(c), black_height(b), black_height(d)));
        apply(rb_insert_fix_inner_right_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_inner_right_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_right_shape(grandparent, above, cursor, parent,
            a, b, rb_reparent(c, parent), d));
        apply(black_height_black_node(cursor, above,
            RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        apply(black_height_red_node(grandparent, cursor, a, rb_reparent(b, grandparent)));
        apply(rb_color_node(cursor, above, Color::Black,
            RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        have black_height(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
            == Nat::Succ(black_height(b)) by {
            rewrite(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))
                == RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))));
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(grandparent, cursor, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
            rewrite(black_height(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))
                == Nat::Succ(black_height(RbTree::Node(grandparent, cursor, Color::Red, a,
                    rb_reparent(b, grandparent)))));
            rewrite(black_height(RbTree::Node(grandparent, cursor, Color::Red, a,
                rb_reparent(b, grandparent))) == black_height(a));
            rewrite(black_height(a) == black_height(b));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
            == Color::Black by {
            rewrite(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))
                == RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))));
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(grandparent, cursor, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
            rewrite(rb_color(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))
                == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, b, c), d))))),
                rb_color(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, b, c), d)))))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
                == Nat::Succ(black_height(b)));
            rewrite(rb_color(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
                == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_right(rb_insert_fix_inner_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d))))));
        assumption();
    }
}

theorem plug_left_frame(identity: struct rb_node*, grandparent: struct rb_node*, color: Color,
                        sibling_model: RbTree, up_model: Context, sub: RbTree) {
    ensures plug(Context::Left(identity, grandparent, color, sibling_model, up_model), sub)
        == plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model)) by {
        unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), sub));
        normalize();
    }
}

theorem plug_right_frame(identity: struct rb_node*, grandparent: struct rb_node*, color: Color,
                         sibling_model: RbTree, up_model: Context, sub: RbTree) {
    ensures plug(Context::Right(identity, grandparent, color, sibling_model, up_model), sub)
        == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub)) by {
        unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), sub));
        normalize();
    }
}

theorem plug_left_in_left(above: struct rb_node*, grandparent: struct rb_node*,
                          parent: struct rb_node*, gcolor: Color, pcolor: Color,
                          sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Left(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model), uncle)) by {
        apply(plug_left_frame(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_left_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        rewrite(plug(Context::Left(parent, grandparent, pcolor, sibling_model,
                Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Left(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        assumption();
    }
}

theorem plug_right_in_left(above: struct rb_node*, grandparent: struct rb_node*,
                           parent: struct rb_node*, gcolor: Color, pcolor: Color,
                           sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Right(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub), uncle)) by {
        apply(plug_right_frame(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_left_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        rewrite(plug(Context::Right(parent, grandparent, pcolor, sibling_model,
                Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Left(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        assumption();
    }
}

theorem plug_left_in_right(above: struct rb_node*, grandparent: struct rb_node*,
                           parent: struct rb_node*, gcolor: Color, pcolor: Color,
                           sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Left(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor, uncle,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model))) by {
        apply(plug_left_frame(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_right_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        rewrite(plug(Context::Left(parent, grandparent, pcolor, sibling_model,
                Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Right(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        assumption();
    }
}

theorem plug_right_in_right(above: struct rb_node*, grandparent: struct rb_node*,
                            parent: struct rb_node*, gcolor: Color, pcolor: Color,
                            sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Right(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor, uncle,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub))) by {
        apply(plug_right_frame(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_right_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        rewrite(plug(Context::Right(parent, grandparent, pcolor, sibling_model,
                Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Right(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        assumption();
    }
}

theorem plug_recolor_inorder(ctx: Context, tree: RbTree, color: Color) {
    ensures rb_inorder(plug(ctx, rb_recolor(tree, color))) == rb_inorder(plug(ctx, tree)) by {
        apply(rb_recolor_preserves_inorder(tree, color));
        apply(plug_inorder_transport(ctx, rb_recolor(tree, color), tree));
        assumption();
    }
}

theorem plug_insert_fix_recolor_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_recolor(tree)))
        == rb_inorder(plug(ctx, tree)) by {
        apply(rb_insert_fix_recolor_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_recolor(tree), tree));
        assumption();
    }
}

theorem plug_insert_fix_outer_left_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_left(tree)))
        == rb_inorder(plug(ctx, tree)) by {
        apply(rb_insert_fix_outer_left_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_outer_left(tree), tree));
        assumption();
    }
}

theorem plug_insert_fix_outer_right_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_right(tree)))
        == rb_inorder(plug(ctx, tree)) by {
        apply(rb_insert_fix_outer_right_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_outer_right(tree), tree));
        assumption();
    }
}

theorem plug_insert_fix_inner_left_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_left(rb_insert_fix_inner_left(tree))))
        == rb_inorder(plug(ctx, tree)) by {
        apply(plug_insert_fix_outer_left_inorder(ctx, rb_insert_fix_inner_left(tree)));
        apply(rb_insert_fix_inner_left_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_inner_left(tree), tree));
        rewrite(rb_inorder(plug(ctx, rb_insert_fix_outer_left(rb_insert_fix_inner_left(tree))))
            == rb_inorder(plug(ctx, rb_insert_fix_inner_left(tree))));
        assumption();
    }
}

theorem plug_insert_fix_inner_right_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_right(rb_insert_fix_inner_right(tree))))
        == rb_inorder(plug(ctx, tree)) by {
        apply(plug_insert_fix_outer_right_inorder(ctx, rb_insert_fix_inner_right(tree)));
        apply(rb_insert_fix_inner_right_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_inner_right(tree), tree));
        rewrite(rb_inorder(plug(ctx, rb_insert_fix_outer_right(rb_insert_fix_inner_right(tree))))
            == rb_inorder(plug(ctx, rb_insert_fix_inner_right(tree))));
        assumption();
    }
}

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function rb_color_bit(tree: RbTree) -> int {
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(identity, parent, color, left, right) => color_bit(color),
    }
}

function rb_has_parent(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
    }
}

function ctx_node_is(ctx: Context, p: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => if p == 0 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if p == identity { 1 } else { 0 },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if p == identity { 1 } else { 0 },
    }
}

function ctx_reroot(ctx: Context, p: struct rb_node*) -> Context {
    match ctx {
        Context::Top => Context::Top,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            Context::Left(p, grandparent, color, sibling_model, up_model),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            Context::Right(p, grandparent, color, sibling_model, up_model),
    }
}

function rb_tree_parent_consistent(t: RbTree) -> int32 {
    rb_parent_consistent(t, 0)
}

function ctx_holds(ctx: Context, sub: RbTree) -> int32 {
    match ctx {
        Context::Top => rb_has_parent(sub, 0),
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            rb_has_parent(sub, identity),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            rb_has_parent(sub, identity),
    }
}



theorem ctx_rb_red_focus_not_top(ctx: Context, bh: Nat) {
    requires ctx_rb(ctx, bh, Color::Red) == 1;

    ensures ctx != Context::Top by {
        induct(ctx) as ih {
            Context::Top => {
                have ctx_rb(Context::Top, bh, Color::Red) != 1 by {
                    unfold(ctx_rb(Context::Top, bh, Color::Red));
                    unfold(color_black(Color::Red));
                    normalize();
                }
                contradiction(ctx_rb(Context::Top, bh, Color::Red) == 1);
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                normalize();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                normalize();
            }
        }
    }
}

theorem rb_ptr_transitive(a: struct rb_node*, b: struct rb_node*, c: struct rb_node*) {
    requires a == b;
    requires a == c;

    ensures c == b by { simp(); }
}

theorem rb_has_parent_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                           left: RbTree, right: RbTree, q: struct rb_node*) {
    requires rb_has_parent(RbTree::Node(identity, parent, color, left, right), q) == 1;

    ensures parent == q by {
        if parent == q {
            assumption();
        } else {
            have rb_has_parent(RbTree::Node(identity, parent, color, left, right), q) != 1 by {
                unfold(rb_has_parent(
                    RbTree::Node(identity, parent, color, left, right), q));
                normalize() using { not(parent == q); }
            }
            contradiction(rb_has_parent(
                RbTree::Node(identity, parent, color, left, right), q) == 1);
        }
    }
}

theorem rb_has_parent_same(sub: RbTree, q: struct rb_node*, p: struct rb_node*) {
    requires rb_has_parent(sub, q) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures p == q by {
        induct(sub) as ih {
            RbTree::Empty => {
                have rb_has_parent(RbTree::Empty, q) != 1 by {
                    unfold(rb_has_parent(RbTree::Empty, q));
                    normalize();
                }
                contradiction(rb_has_parent(RbTree::Empty, q) == 1);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                apply(rb_has_parent_node(identity, parent, color, left, right, q));
                apply(rb_has_parent_node(identity, parent, color, left, right, p));
                apply(rb_ptr_transitive(parent, q, p));
                assumption();
            }
        }
    }
}

theorem ctx_holds_top_parent(sub: RbTree) {
    requires ctx_holds(Context::Top, sub) == 1;

    ensures rb_has_parent(sub, 0) == 1 by {
        unfold(ctx_holds(Context::Top, sub));
        rewrite(rb_has_parent(sub, 0) == ctx_holds(Context::Top, sub));
        assumption();
    }
}

theorem ctx_holds_left_parent(cid: struct rb_node*, grandparent: struct rb_node*,
                              ccolor: Color, sibling_model: RbTree, up_model: Context,
                              sub: RbTree) {
    requires ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        sub) == 1;

    ensures rb_has_parent(sub, cid) == 1 by {
        unfold(ctx_holds(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), sub));
        rewrite(rb_has_parent(sub, cid)
            == ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        assumption();
    }
}

theorem ctx_holds_right_parent(cid: struct rb_node*, grandparent: struct rb_node*,
                               ccolor: Color, sibling_model: RbTree, up_model: Context,
                               sub: RbTree) {
    requires ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        sub) == 1;

    ensures rb_has_parent(sub, cid) == 1 by {
        unfold(ctx_holds(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), sub));
        rewrite(rb_has_parent(sub, cid)
            == ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        assumption();
    }
}

theorem ctx_node_is_from_parent(ctx: Context, sub: RbTree, p: struct rb_node*) {
    requires ctx_holds(ctx, sub) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures ctx_node_is(ctx, p) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_holds_top_parent(sub));
                apply(rb_has_parent_same(sub, 0, p));
                have ctx_node_is(Context::Top, p) == 1 by {
                    unfold(ctx_node_is(Context::Top, p));
                    normalize() using { p == 0; }
                }
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_holds_left_parent(cid, grandparent, ccolor, sibling_model,
                    up_model, sub));
                apply(rb_has_parent_same(sub, cid, p));
                have ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                    p) == 1 by {
                    unfold(ctx_node_is(
                        Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                    normalize() using { p == cid; }
                }
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_holds_right_parent(cid, grandparent, ccolor, sibling_model,
                    up_model, sub));
                apply(rb_has_parent_same(sub, cid, p));
                have ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                    p) == 1 by {
                    unfold(ctx_node_is(
                        Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                    normalize() using { p == cid; }
                }
                assumption();
            }
        }
    }
}

theorem ctx_node_is_left_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                  ccolor: Color, sibling_model: RbTree, up_model: Context,
                                  p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_node_is_right_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                   ccolor: Color, sibling_model: RbTree, up_model: Context,
                                   p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_top_fixed(p: struct rb_node*) {
    ensures Context::Top == ctx_reroot(Context::Top, p) by {
        unfold(ctx_reroot(Context::Top, p));
        normalize();
    }
}

theorem ctx_reroot_left_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
                              ccolor: Color, sibling_model: RbTree, up_model: Context,
                              p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures Context::Left(cid, grandparent, ccolor, sibling_model, up_model)
        == ctx_reroot(Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_right_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
                               ccolor: Color, sibling_model: RbTree, up_model: Context,
                               p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures Context::Right(cid, grandparent, ccolor, sibling_model, up_model)
        == ctx_reroot(Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_fixed(ctx: Context, p: struct rb_node*) {
    requires ctx_node_is(ctx, p) == 1;

    ensures ctx == ctx_reroot(ctx, p) by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_reroot_top_fixed(p));
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_left_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_right_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                assumption();
            }
        }
    }
}

resource rb_at(p: struct rb_node*) {
    field model: RbTree;
    match model {
        RbTree::Empty => { fact p == 0; },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns p->rb_left;
            owns p->rb_right;
            owns left: rb_at(p->rb_left);
            owns right: rb_at(p->rb_right);
            fact p != 0;
            fact p == identity;
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact (p->__rb_parent_color & 1) == color_bit(color);
            fact left.model == left_model;
            fact right.model == right_model;
            fact rb_parent_is(left_model, p) == 1;
            fact rb_parent_is(right_model, p) == 1;
        },
    }
}

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => {
            owns root->rb_node;
            fact root != 0;
            fact root->rb_node == child;
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_left);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_right == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
    }
}

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
} by {
    execute();
    simp();
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires AugmentRotate(augment_rotate);
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces ctx: ctx_at(root->rb_node, root);
    produces sub: rb_at(root->rb_node);
    ensures rb_inorder(plug(ctx.model, sub.model))
        == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(plug(ctx.model, sub.model)) == 1;
    ensures rb_tree_parent_consistent(plug(ctx.model, sub.model)) == 1;
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, node_parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, node_parent, color, left_model, right_model)));
                assumption();
            }
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == rb_color_bit(old(t.model)));
                simp();
            }
            have node->__rb_parent_color == address(node_parent) by {
                rewrite(node->__rb_parent_color
                    == address(node_parent) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0);
                normalize();
            }
            step();
            step();
            step();
            step();
            let t = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            have rb_has_parent(t.model, node_parent) == 1 by {
                rewrite(t.model
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_has_parent(
                    RbTree::Node(identity, node_parent, color, left_model, right_model),
                    node_parent));
                normalize();
            }
            have ctx_node_is(c.model, node_parent) == 1 by {
                apply(ctx_node_is_from_parent(c.model, t.model, node_parent)) using {
                    ctx_holds(c.model, t.model) == 1;
                    rb_has_parent(t.model, node_parent) == 1;
                }
                assumption();
            }
            have c.model == ctx_reroot(c.model, node_parent) by {
                apply(ctx_reroot_fixed(c.model, node_parent)) using {
                    ctx_node_is(c.model, node_parent) == 1;
                }
                assumption();
            }
            have parent == node_parent by { simp(); }
            have rb_has_parent(t.model, parent) == 1 by { simp(); }
            have ctx_node_is(c.model, parent) == 1 by { simp(); }
            have c.model == ctx_reroot(c.model, parent) by { simp(); }
            have rb_parent_is(t.model, parent) == 1 by { simp(); }
            have t.model
                == RbTree::Node(identity, node_parent, color, left_model, right_model) by {
                simp();
            }
            have rb_inorder(plug(c.model, t.model))
                == rb_inorder(plug(old(c.model),
                    RbTree::Node(identity, node_parent, color,
                        left_model, right_model))) by {
                rewrite(t.model
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                simp();
            }
            loop {
                owns c: ctx_at(node, root);
                owns t: rb_at(node);
                decreases c;
                invariant t.model != RbTree::Empty;
                invariant rb_color_bit(t.model) == 0;
                invariant rb_parent_is(t.model, parent) == 1;
                invariant ctx_node_is(c.model, parent) == 1;
                invariant c.model == ctx_reroot(c.model, parent);
                invariant is_rb(t.model) == 1;
                invariant ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
                invariant rb_inorder(plug(c.model, t.model))
                    == rb_inorder(plug(old(c.model),
                        RbTree::Node(identity, node_parent, color,
                            left_model, right_model)));
                invariant rb_tree_parent_consistent(plug(c.model, t.model)) == 1;

                preserve by {
                    match t.model {
                        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                        RbTree::Node(nid, nparent, ncolor, nleft, nright) => {
                            if parent == 0 {
                                unfold(t) as { left: l, right: r };
                                step();
                                step();
                                have (node->__rb_parent_color & 1)
                                    == color_bit(Color::Black) by {
                                    unfold(color_bit(Color::Black));
                                    simp();
                                }
                                let t = fold(rb_at(node),
                                    { model: RbTree::Node(nid, 0, Color::Black, nleft, nright) },
                                    { left: l, right: r });
                                step();
                            } else {
                                match c.model {
                                    Context::Top => {
                                        contradiction(c.model == Context::Top);
                                    },
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor,
                                                csib, cup, parent)) using {
                                                ctx_node_is(Context::Left(cid, cgp, ccolor,
                                                    csib, cup), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        have ctx_rb(Context::Left(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model))) using {
                                                ctx_almost_rb_insert(c.model,
                                                    black_height(t.model)) == 1;
                                            }
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        unfold(c) as { sibling: cs, up: cu };
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    simp();
                                                }
                                                have parent->__rb_parent_color
                                                    == address(cgp) + 1 by {
                                                    rewrite(parent->__rb_parent_color
                                                        == address(cgp)
                                                            + (parent->__rb_parent_color & 1));
                                                    rewrite((parent->__rb_parent_color & 1) == 1);
                                                    normalize();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    { model: Context::Left(cid, cgp, ccolor,
                                                        csib, cup) },
                                                    { sibling: cs, up: cu });
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    simp();
                                                }
                                                have (parent->__rb_parent_color & 1) == 0 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    simp();
                                                }
                                                have parent->__rb_parent_color
                                                    == address(cgp) + 0 by {
                                                    rewrite(parent->__rb_parent_color
                                                        == address(cgp)
                                                            + (parent->__rb_parent_color & 1));
                                                    rewrite((parent->__rb_parent_color & 1) == 0);
                                                    normalize();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_left_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black)) using {
                                                        ctx_rb(Context::Left(cid, cgp, Color::Red,
                                                            csib, cup), black_height(t.model),
                                                            Color::Black) == 1;
                                                    }
                                                    rewrite(cu.model == cup);
                                                    assumption();
                                                }
                                                step();
                                                step();
                                                step();
                                                have gparent == cgp by { simp(); }
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model))) using {
                                                        ctx_rb(cu.model,
                                                            black_height(t.model),
                                                            Color::Red) == 1;
                                                    }
                                                    assumption();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    contradiction(cu.model == Context::Top);
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have gparent == uid by { simp(); }
                                                    unfold(cu) as { sibling: us, up: uu };
                                                    step();
                                                    match us.model {
                                                        RbTree::Empty => {
                                                            unfold(us);
                                                            have tmp == 0 by { simp(); }
                                                            have parent != tmp by { simp(); }
                                                            step();
                                                            step();
                                                            step();
                                                        },
                                                        RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                            unfold(us) as { left: ul, right: ur };
                                                            step();
                                                        },
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have gparent == uid by { simp(); }
                                                    unfold(cu) as { sibling: us, up: uu };
                                                    step();
                                                    match us.model {
                                                        RbTree::Empty => {
                                                            unfold(us);
                                                            have tmp == 0 by { simp(); }
                                                            have parent != tmp by { simp(); }
                                                            step();
                                                            step();
                                                            step();
                                                        },
                                                        RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                            unfold(us) as { left: ul, right: ur };
                                                            step();
                                                        },
                                                    }
                                                },
                                                }
                                            },
                                        }
                                    },
                                    Context::Right(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Right(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor,
                                                csib, cup, parent)) using {
                                                ctx_node_is(Context::Right(cid, cgp, ccolor,
                                                    csib, cup), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        have ctx_rb(Context::Right(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model))) using {
                                                ctx_almost_rb_insert(c.model,
                                                    black_height(t.model)) == 1;
                                            }
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        unfold(c) as { sibling: cs, up: cu };
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    simp();
                                                }
                                                have parent->__rb_parent_color
                                                    == address(cgp) + 1 by {
                                                    rewrite(parent->__rb_parent_color
                                                        == address(cgp)
                                                            + (parent->__rb_parent_color & 1));
                                                    rewrite((parent->__rb_parent_color & 1) == 1);
                                                    normalize();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    { model: Context::Right(cid, cgp, ccolor,
                                                        csib, cup) },
                                                    { sibling: cs, up: cu });
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    simp();
                                                }
                                                have (parent->__rb_parent_color & 1) == 0 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    simp();
                                                }
                                                have parent->__rb_parent_color
                                                    == address(cgp) + 0 by {
                                                    rewrite(parent->__rb_parent_color
                                                        == address(cgp)
                                                            + (parent->__rb_parent_color & 1));
                                                    rewrite((parent->__rb_parent_color & 1) == 0);
                                                    normalize();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_right_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black)) using {
                                                        ctx_rb(Context::Right(cid, cgp, Color::Red,
                                                            csib, cup), black_height(t.model),
                                                            Color::Black) == 1;
                                                    }
                                                    rewrite(cu.model == cup);
                                                    assumption();
                                                }
                                                step();
                                                step();
                                                step();
                                                have gparent == cgp by { simp(); }
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model))) using {
                                                        ctx_rb(cu.model,
                                                            black_height(t.model),
                                                            Color::Red) == 1;
                                                    }
                                                    assumption();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    contradiction(cu.model == Context::Top);
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have gparent == uid by { simp(); }
                                                    unfold(cu) as { sibling: us, up: uu };
                                                    step();
                                                    match us.model {
                                                        RbTree::Empty => {
                                                            unfold(us);
                                                            have tmp == 0 by { simp(); }
                                                            have parent != tmp by { simp(); }
                                                            step();
                                                            step();
                                                            step();
                                                        },
                                                        RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                            unfold(us) as { left: ul, right: ur };
                                                            step();
                                                        },
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have gparent == uid by { simp(); }
                                                    unfold(cu) as { sibling: us, up: uu };
                                                    step();
                                                    match us.model {
                                                        RbTree::Empty => {
                                                            unfold(us);
                                                            have tmp == 0 by { simp(); }
                                                            have parent != tmp by { simp(); }
                                                            step();
                                                            step();
                                                            step();
                                                        },
                                                        RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                            unfold(us) as { left: ul, right: ur };
                                                            step();
                                                        },
                                                    }
                                                },
                                                }
                                            },
                                        }
                                    },
                                }
                            }
                        },
                    }
                }
            }
            simp();
        },
    }
}

void rb_insert_color(struct rb_node* node, struct rb_root* root) {
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces ctx: ctx_at(root->rb_node, root);
    produces sub: rb_at(root->rb_node);
    ensures rb_inorder(plug(ctx.model, sub.model))
        == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(plug(ctx.model, sub.model)) == 1;
    ensures rb_tree_parent_consistent(plug(ctx.model, sub.model)) == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: the frontier is at statement 23, `tmp = load_int32_pointer(byte_offset(parent, 8))`, after tactic 32 `step`; still ahead on this path: the body's end and 1 `break`. Already complete: 2 at a `break`
```
