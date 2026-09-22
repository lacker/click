# `rb_next`'s ascent needs a conjunctive guard

The unchanged Linux `rb_next` is two walks. The first is a descent — right once,
then left as far as it goes — and it is the same shape as
[`rb_first_last.md`](rb_first_last.md), which the node-keyed model verifies. The
second is the ascent
`while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;`,
which now parses unchanged. C0 lowers the call, conversion to `parent`'s
pointer type, write, and expression result into checked statements at the loop
head. That prefix is re-executed on every iteration, including after
`continue`, and the existing logical `&&` keeps the parent-link read lazy.

Because a C function verifies as a whole, the descent cannot land ahead of the
ascent. This fixture keeps the C verbatim and now pins the next honest proof
frontier rather than claiming the traversal is complete: the bare `execute()`
first reaches `if (node->rb_right)` with `t: rb_at(node)` still folded, so the
branch cannot obtain the required view of that link. Unfolding the entry shape
and proving the complete descent and ascent remain C4b proof work.

The frame here is `ctx_at(child)` with no `rb_root` argument, because `rb_next`
takes only the node. That is the other half of gap 35: with the parent in the
payload the focused node is the only name a frame needs, so `rb_next`'s entry
frame becomes spellable for the first time — `ctx_at(child, parent, root)`
could not be written at all here.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}
#endif
```

```c filename=rb_next_guard.c
#include "rbtree.h"

struct rb_node *rb_next(struct rb_node *node)
{
	struct rb_node *parent;

	if (node->rb_right) {
		node = node->rb_right;
		while (node->rb_left)
			node = node->rb_left;
		return node;
	}

	while ((parent = rb_parent(node)) && node == parent->rb_right)
		node = parent;

	return parent;
}
```

```click
verifying "rb_next_guard.c";

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

resource rb_at(p: struct rb_node*) {
    field model: RbTree;
    match model {
        RbTree::Empty => { fact p == 0; },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns &p->rb_left;
            owns &p->rb_right;
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
        },
    }
}

resource ctx_at(child: struct rb_node*) {
    field model: Context;
    match model {
        Context::Top => { },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns &identity->rb_left;
            owns &identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: ctx_at(identity);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns &identity->rb_left;
            owns &identity->rb_right;
            owns sibling: rb_at(identity->rb_left);
            owns up: ctx_at(identity);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_right == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

struct rb_node* rb_next(struct rb_node* node) {
    consumes c: ctx_at(node);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    produces ctx: ctx_at(result);
    produces sub: rb_at(result);
    ensures plug(ctx.model, sub.model) == plug(old(c.model), old(t.model));
} by {
    execute();
    simp();
}
```

```expect
fail: MissingResource
```
