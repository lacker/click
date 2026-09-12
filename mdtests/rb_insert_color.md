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

**The proof does not.** The fixup loop is `while (true)` with four `break`s —
the root-blackening exit, the black-parent exit, and the two case-3 rotations —
and two `continue`s, the uncle-red recolours. The `loop` tactic now has a rule
for both: a `continue` is the back edge
([`loop_body_continue_back_edge.md`](loop_body_continue_back_edge.md)) and a
`break` is an exit joined into the loop's one successor
([`loop_body_break_exit.md`](loop_body_break_exit.md)). This loop still cannot
use it. Each of its four `break`s writes a colour or rotates before leaving, so
the four exits reach four different states, and a loop statement has one
successor; the exits are refused by name rather than dropped
([`loop_body_break_exit_state_rejected.md`](loop_body_break_exit_state_rejected.md)).
Describing the state a loop exits in, the way `branch ensuring` describes the
state two arms join in, is the missing piece. So no exit of this loop can be
certified yet, and the contract below is the one the fixup wants rather than one
that holds.

What this fixture pins is the refusal that comes first, before the loop tactic
is reached at all: the contract's own requirement `rb_color_bit(t.model) == 0` —
the loop invariant "node is red", which is what makes `rb_red_parent`'s
untagging sound — makes the resource-derived loop frame fail to establish, with
`named resource instance is not owned`. Dropping just that one clause from the
same contract lowers and reaches the proof. That is a second, independent
blocker and it is smaller than the first.

Two further limits are recorded here because the contract shows them:

- `decreases c;` cannot rank this loop even once the exits are certified. The
  uncle-red cases set `node = gparent`, so the next frame is the context *above*
  the grandparent — `up.up` — while `loop_structural_descent_failure` accepts
  only a direct contained child of the instance the binder held at the head.
  A two-frame climb needs the loop measure to accept a strict descendant, which
  is for loop measures what package A16 was for induction hypotheses.
- A pure function cannot take the null constant where a `struct rb_node*`
  parameter is declared: `rb_parent_is(sub, 0)` is refused with `function
  `rb_parent_is` argument 1 expects int32*, got int32`, in a pure body and in a
  contract clause alike. `ctx_holds`'s `Top` case and the whole-tree
  `rb_tree_parent_consistent` below are written out at null rather than applied
  at it.

The contract itself is D3 and D4 on the node-keyed model. `__rb_insert` returns
`void` and reassigns `node`, so the cursor at the exit has no C name: the
instances are `owns` on both sides rather than `consumes`/`produces`, since a
`produces` clause needs an argument that names the final position and only
`result` works there. `ctx_holds(c.model, t.model)` is the gluing requirement
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

function ctx_node_is(ctx: Context, p: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => if p == 0 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
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
    match t {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if rb_parent_consistent(left, node) == 1 {
                if rb_parent_consistent(right, node) == 1 {
                    if parent == 0 { 1 } else { 0 }
                } else {
                    0
                }
            } else {
                0
            },
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

function rb_parent_is_null(tree: RbTree) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == 0 { 1 } else { 0 },
    }
}

function ctx_holds(ctx: Context, sub: RbTree) -> int32 {
    match ctx {
        Context::Top => rb_parent_is_null(sub),
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            rb_parent_is(sub, identity),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            rb_parent_is(sub, identity),
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
    produces ctx: ctx_at(node, root);
    produces sub: rb_at(node);
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
                    == rb_inorder(plug(old(c.model), old(t.model)));
                invariant rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
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
    produces ctx: ctx_at(node, root);
    produces sub: rb_at(node);
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
fail: could not establish resource-derived loop frames for
```
