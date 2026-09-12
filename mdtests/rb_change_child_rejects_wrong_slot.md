# a change-child that writes the other slot is refused

This is `__rb_change_child` with its two writes exchanged, kept under a
different name so the real helper stays verbatim. It is contracted exactly like
the `Left` case of `mdtests/rb_ctx_change_child.md`: consume a `Context::Left`
frame focused on `old_child` and produce the same frame focused on `new_child`.
Because it stores into `parent->rb_right`, the cell the `Left` frame's sibling
subtree is reached through now points at `new_child`, so the sibling it kept is
no longer a child of the proposed frame and the fold is refused. The focused
child is not moved either: `parent->rb_left` still names `old_child`.

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
__rb_change_child_wrong_slot(struct rb_node *old, struct rb_node *new,
                             struct rb_node *parent, struct rb_root *root)
{
    if (parent) {
        if (parent->rb_left == old)
            WRITE_ONCE(parent->rb_right, new);
        else
            WRITE_ONCE(parent->rb_left, new);
    } else
        WRITE_ONCE(root->rb_node, new);
}
#endif
```

```c filename=rb_change_child_wrong_slot.c
#include "rbtree.h"

void change_child_left(struct rb_node *old_child, struct rb_node *new_child,
                       struct rb_node *parent, struct rb_node *grandparent,
                       struct rb_root *root) {
    __rb_change_child_wrong_slot(old_child, new_child, parent, root);
}
```

```click
verifying "rb_change_child_wrong_slot.c";

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
```

```expect
fail: selected child does not satisfy the proposed parent model
```
