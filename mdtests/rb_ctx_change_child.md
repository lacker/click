# `__rb_change_child` over an rbtree context frame

`ctx_at(child, root)` is the zipper frame for the rbtree: it is keyed by the
focused child, owns the ancestors' cells, and bottoms out at `Top`, which owns
`root->rb_node`. `plug` rebuilds the whole model from a frame and the focused
subtree, so a frame plus a subtree is a whole tree.

`__rb_change_child` writes exactly one of `parent->rb_left`,
`parent->rb_right`, or `root->rb_node` — always a cell the frame owns — so its
effect is stated on the frame: the same context model now focuses the new
subtree. The helper's two nested `if`s are decided before execution, so no
path is left to search: `Context::Top` fixes `parent == 0`, `Context::Left`
gives `parent->rb_left == child`, and in the `Right` case the requirement
`parent->rb_left != old_child` sends the helper down its `else` path. That
last requirement reads a cell of a still-folded frame, which is exactly what
arm selection at contract lowering grants: the constructor equality entails
one arm, and that arm owns `parent->rb_left`.

Each case is a separate contracted wrapper around the one unchanged helper,
because a requirement has to entail a single frame constructor before the
frame's cells are readable and its payload is named. The frames here are one
level deep with an empty sibling, which is what a requirement can spell today:
a general frame would have to relate the `parent` the model carries to the
helper's `parent` argument, and a pointer payload cannot yet be compared with
a C pointer, while an existential requirement cannot bind the arm's `Color`,
`RbTree` and `Context` payloads.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0
#define RB_RED 0
#define RB_BLACK 1

#define __WRITE_ONCE(x, value) ({ typeof(x) __value = (value); (*(volatile typeof(x) *)&(x)) = __value; __value; })
#define WRITE_ONCE(x, value) __WRITE_ONCE(x, value)

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

struct rb_root {
    struct rb_node *rb_node;
};

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
#endif
```

```c filename=rb_ctx_change_child.c
#include "rbtree.h"

void change_child_root(struct rb_node *old_child, struct rb_node *new_child,
                       struct rb_node *parent, struct rb_root *root) {
    __rb_change_child(old_child, new_child, parent, root);
}

void change_child_left(struct rb_node *old_child, struct rb_node *new_child,
                       struct rb_node *parent, struct rb_node *grandparent,
                       struct rb_root *root) {
    __rb_change_child(old_child, new_child, parent, root);
}

void change_child_right(struct rb_node *old_child, struct rb_node *new_child,
                        struct rb_node *parent, struct rb_node *grandparent,
                        struct rb_root *root) {
    __rb_change_child(old_child, new_child, parent, root);
}
```

```click
verifying "rb_ctx_change_child.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, Color, RbTree, RbTree),
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
        Context::Left(parent, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(parent, color, sub, sibling_model)),
        Context::Right(parent, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(parent, color, sibling_model, sub)),
    }
}

theorem plug_top_is_the_subtree(sub: RbTree) {
    ensures plug(Context::Top, sub) == sub by {
        unfold(plug(Context::Top, sub));
        normalize();
    }
}

theorem plug_left_frame(parent: struct rb_node*, grandparent: struct rb_node*,
                        color: Color, sibling: RbTree, sub: RbTree) {
    ensures plug(Context::Left(parent, grandparent, color, sibling, Context::Top), sub)
        == RbTree::Node(parent, color, sub, sibling) by {
        unfold(plug(Context::Left(parent, grandparent, color, sibling, Context::Top), sub));
        unfold(plug(Context::Top, RbTree::Node(parent, color, sub, sibling)));
        normalize();
    }
}

theorem plug_right_frame(parent: struct rb_node*, grandparent: struct rb_node*,
                         color: Color, sibling: RbTree, sub: RbTree) {
    ensures plug(Context::Right(parent, grandparent, color, sibling, Context::Top), sub)
        == RbTree::Node(parent, color, sibling, sub) by {
        unfold(plug(Context::Right(parent, grandparent, color, sibling, Context::Top), sub));
        unfold(plug(Context::Top, RbTree::Node(parent, color, sibling, sub)));
        normalize();
    }
}

resource rb_at(p: struct rb_node*, parent: struct rb_node*) {
    field model: RbTree;
    match model {
        RbTree::Empty => { fact p == 0; },
        RbTree::Node(identity, color, left_model, right_model) => {
            owns p->__rb_parent_color;
            owns p->rb_left;
            owns p->rb_right;
            owns left: rb_at(p->rb_left, p);
            owns right: rb_at(p->rb_right, p);
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

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => {
            owns root->rb_node;
            fact root != 0;
            fact root->rb_node == child;
        },
        Context::Left(parent, grandparent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_right, parent);
            owns up: ctx_at(parent, root);
            fact parent != 0;
            fact aligned(parent, 8);
            fact aligned(grandparent, 8);
            fact parent->rb_left == child;
            fact parent->__rb_parent_color
                == address(grandparent) + (parent->__rb_parent_color & 1);
            fact (parent->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(parent, grandparent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_left, parent);
            owns up: ctx_at(parent, root);
            fact parent != 0;
            fact aligned(parent, 8);
            fact aligned(grandparent, 8);
            fact parent->rb_right == child;
            fact parent->__rb_parent_color
                == address(grandparent) + (parent->__rb_parent_color & 1);
            fact (parent->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

void change_child_root(struct rb_node* old_child, struct rb_node* new_child,
                       struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(old_child, root);
    owns s: rb_at(new_child, parent);
    requires parent == 0;
    requires c.model == Context::Top;
    produces d: ctx_at(new_child, root);
    ensures d.model == old(c.model);
    ensures s.model == old(s.model);
} by {
    unfold(c);
    execute();
    let d = fold(ctx_at(new_child, root), { model: old(c.model) }, {});
    simp();
}

void change_child_left(struct rb_node* old_child, struct rb_node* new_child,
                       struct rb_node* parent, struct rb_node* grandparent,
                       struct rb_root* root) {
    consumes c: ctx_at(old_child, root);
    owns s: rb_at(new_child, parent);
    requires c.model
        == Context::Left(parent, grandparent, Color::Black, RbTree::Empty, Context::Top);
    produces d: ctx_at(new_child, root);
    ensures d.model == old(c.model);
    ensures s.model == old(s.model);
} by {
    unfold(c) as { sibling: sib, up: u };
    execute();
    let d = fold(ctx_at(new_child, root), { model: old(c.model) }, { sibling: sib, up: u });
    simp();
}

void change_child_right(struct rb_node* old_child, struct rb_node* new_child,
                        struct rb_node* parent, struct rb_node* grandparent,
                        struct rb_root* root) {
    consumes c: ctx_at(old_child, root);
    owns s: rb_at(new_child, parent);
    requires c.model
        == Context::Right(parent, grandparent, Color::Black, RbTree::Empty, Context::Top);
    requires parent->rb_left != old_child;
    produces d: ctx_at(new_child, root);
    ensures d.model == old(c.model);
    ensures s.model == old(s.model);
} by {
    unfold(c) as { sibling: sib, up: u };
    execute();
    let d = fold(ctx_at(new_child, root), { model: old(c.model) }, { sibling: sib, up: u });
    simp();
}
```

```expect
pass
```
