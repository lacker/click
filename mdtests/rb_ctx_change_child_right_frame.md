# The `Context::Right` frame decides `__rb_change_child` without being told

`mdtests/rb_ctx_change_child.md` verifies the right-child frame of the
unchanged Linux helper only by handing it the answer:
`requires parent->rb_left != old_child;`. The frame already says everything
that decides the helper's inner `parent->rb_left == old` test, and that
requirement was there because the chain from "this pointer is null" to "it
differs from that non-null one" was not available.

Here the frame states it. The focused child is the right child, the left
sibling is an empty subtree, so `parent->rb_left` is null; the caller passes a
child that exists, so `old_child` is not null. One null pointer and one
non-null pointer are different pointers, and the helper goes down its `else`
path with no requirement about `parent->rb_left` at all. The empty sibling is
unfolded because an `Empty` arm's `fact p == 0` is what carries the
null-ness, and refolded from its constructor afterwards: the write goes to
`parent->rb_right`, which leaves `parent->rb_left` alone.

The frame is keyed by the focused child's parent, `ctx_at(child, parent,
root)`, per the D3 amendment in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md).

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

```c filename=rb_ctx_change_child_right_frame.c
#include "rbtree.h"

void change_child_right(struct rb_node *old_child, struct rb_node *new_child,
                        struct rb_node *parent, struct rb_node *grandparent,
                        struct rb_root *root) {
    __rb_change_child(old_child, new_child, parent, root);
}
```

```click
verifying "rb_ctx_change_child_right_frame.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Right(struct rb_node*, Color, RbTree, Context),
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

resource ctx_at(child: struct rb_node*, parent: struct rb_node*,
                root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => {
            owns root->rb_node;
            fact root != 0;
            fact parent == 0;
            fact root->rb_node == child;
        },
        Context::Right(grandparent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_left, parent);
            owns up: ctx_at(parent, grandparent, root);
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

void change_child_right(struct rb_node* old_child, struct rb_node* new_child,
                        struct rb_node* parent, struct rb_node* grandparent,
                        struct rb_root* root) {
    consumes c: ctx_at(old_child, parent, root);
    owns s: rb_at(new_child, parent);
    requires old_child != 0;
    requires c.model
        == Context::Right(grandparent, Color::Black, RbTree::Empty, Context::Top);
    produces d: ctx_at(new_child, parent, root);
    ensures d.model == old(c.model);
    ensures s.model == old(s.model);
} by {
    unfold(c) as { sibling: sib, up: u };
    unfold(sib);
    execute();
    let refolded_sib = fold(rb_at(parent->rb_left, parent), { model: RbTree::Empty }, {});
    let d = fold(ctx_at(new_child, parent, root), { model: old(c.model) },
                 { sibling: refolded_sib, up: u });
    simp();
}
```

```expect
pass
```
