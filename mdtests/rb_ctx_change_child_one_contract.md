# One contract over two `__rb_change_child` frames

`mdtests/rb_ctx_change_child.md` needs one contracted wrapper per frame
constructor, because a requirement has to entail a single constructor before
the frame's cells are readable. A proof `match` on `c.model` supplies that
constructor per arm instead, so one contract covers several frames of the
unchanged helper.

The frame is keyed by the focused child's parent, `ctx_at(child, parent,
root)`, per the D3 amendment in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md):
with the parent as a resource argument the arm's cells are `parent`'s, and no
pure accessor from the model to a parent pointer is needed. Unlike the
per-frame wrappers, the sibling subtree and the frame above are arbitrary
here: `Left` carries a general `rb_at(parent->rb_right, parent)` and a
recursive `up`.

What each arm needs is that its frame's other facts survive the one link the
helper writes. `Left` writes `parent->rb_left` and refolds a frame whose
packed parent word is unchanged; that word is an `unsigned long` cell, and its
load is named by its cell's epoch, which the write to a disjoint cell of the
same node does not end.

`Context::Right` is not covered. Its arm would have to decide the helper's
inner `parent->rb_left == old` test, and the fact that decides it,
`parent->rb_left != child`, is about the focused child, so refolding the frame
around the new child would demand it again of a pointer only the caller knows
anything about. That is a separate gap from this one; the three-wrapper
fixture still spells the `Right` case with its own requirement.

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

```c filename=rb_ctx_change_child_one_contract.c
#include "rbtree.h"

void change_child(struct rb_node *old_child, struct rb_node *new_child,
                  struct rb_node *parent, struct rb_root *root) {
    __rb_change_child(old_child, new_child, parent, root);
}
```

```click
verifying "rb_ctx_change_child_one_contract.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, Color, RbTree, Context),
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
        Context::Left(grandparent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_right, parent);
            owns up: ctx_at(parent, grandparent, root);
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
    }
}

void change_child(struct rb_node* old_child, struct rb_node* new_child,
                  struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(old_child, parent, root);
    owns s: rb_at(new_child, parent);
    produces d: ctx_at(new_child, parent, root);
    ensures d.model == old(c.model);
    ensures s.model == old(s.model);
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: old(c.model) }, {});
            simp();
        },
        Context::Left(grandparent, color, sibling_model, up_model) => {
            unfold(c) as { sibling: sib, up: u };
            execute();
            let d = fold(ctx_at(new_child, parent, root), { model: old(c.model) },
                         { sibling: sib, up: u });
            simp();
        },
    }
}
```

```expect
pass
```
