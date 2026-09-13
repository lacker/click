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

The remaining two `break`s are the two rotations, and with the two `continue`s
they wait on a contract change: the frame-level case theorems
`examples/rbtree-model` proves for them (`ctx_insert_case1_left`,
`ctx_insert_case2_left`, `ctx_insert_case3_left` and their mirrors) are stated
over `ctx_rb(ctx, bh, focus_color)` and `ctx_almost_rb_insert(ctx, bh)`, while
this loop carries `almost_rb_insert(plug(c.model, t.model)) == 1` and
`ctx_root_black(c.model) == 1`. The invariants have to be restated in the
frame-level form the pure library consumes, with the black height as a
loop-carried `Nat`, before the recolour `continue`s can close and before the
post-loop `simp()` can reach `is_rb_root(plug(ctx.model, sub.model)) == 1`.
The `Color::Red` arm of each frame is where that work starts. It takes the
same two steps in the other direction — the frame's colour bit is `0`, so the
parent's packed word is exactly `address(cgp)` — which is what makes the
inlined `rb_red_parent(parent)` cast sound and gives `gparent == cgp` without
an untagging mask. The frontier is then at `tmp = gparent->rb_right`, whose
cells belong to the frame above, `cu`: reading them needs `Context::Top`
refuted for `cu`, which follows from `ctx_root_black(c.model) == 1` and a red
parent but has no pure theorem here yet.

The contract itself is D3 and D4 on the node-keyed model. `__rb_insert` returns
`void` and reassigns `node`, so the cursor at the exit has no C name and the
produced instances are named at the root cell instead. `ctx_holds(c.model,
t.model)` is the gluing requirement
that the frame's own node is the focused subtree's parent payload — the
replacement for the `parent` parameter the ascent fixtures have and this
function does not. `ctx_root_black(c.model)` is what refutes `Context::Top` for
the grandparent when the parent is red, which is what makes `gparent->rb_right`
a safe read; without it the verbatim body dereferences a null grandparent.
`almost_rb_insert` and `plug` come from
[`examples/rbtree-model`](../examples/rbtree-model/README.md) unchanged, since a
fixture has no import.

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

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
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

function rb_node_is(a: struct rb_node*, b: struct rb_node*) -> int32 {
    if a == b { 1 } else { 0 }
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

function rb_tree_parent_consistent(t: RbTree) -> int32 {
    rb_parent_consistent(t, 0)
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

function ctx_holds(ctx: Context, sub: RbTree) -> int32 {
    match ctx {
        Context::Top => rb_has_parent(sub, 0),
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            rb_has_parent(sub, identity),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            rb_has_parent(sub, identity),
    }
}

function ctx_frame_root_black(color: Color, up: Context) -> int32 {
    match up {
        Context::Top => if color_bit(color) == 1 { 1 } else { 0 },
        Context::Left(identity, grandparent, up_color, sibling_model, up_model) => 1,
        Context::Right(identity, grandparent, up_color, sibling_model, up_model) => 1,
    }
}

function ctx_root_black(ctx: Context) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => 1,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if ctx_frame_root_black(color, up_model) == 1 {
                ctx_root_black(up_model)
            } else {
                0
            },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if ctx_frame_root_black(color, up_model) == 1 {
                ctx_root_black(up_model)
            } else {
                0
            },
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
    requires ctx_root_black(c.model) == 1;
    requires almost_rb_insert(plug(c.model, t.model)) == 1;
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
                invariant ctx_root_black(c.model) == 1;
                invariant almost_rb_insert(plug(c.model, t.model)) == 1;
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
                                                step();
                                                step();
                                                step();
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
                                                step();
                                                step();
                                                step();
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
    requires ctx_root_black(c.model) == 1;
    requires almost_rb_insert(plug(c.model, t.model)) == 1;
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
fail: still ahead on this path: the body's end, 2 `break`s, and 2 `continue`s. Already complete: 2 at a `break`
```
