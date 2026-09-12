# a parent word naming another node cannot be folded at that parent

`rb_at(p, parent)`'s `Node` arm states what the node's own word holds, so a
node whose `__rb_parent_color` was set to `other` is not an `rb_at(node, parent)`
for a different `parent`. The fold is refused; the frame cannot be re-parented
by claiming it.

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

static inline unsigned long rb_color(struct rb_node *rb) {
    return rb->__rb_parent_color & 1;
}

static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
    rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;
}
#endif
```

```c filename=rb_at_wrong_parent.c
#include "rbtree.h"

void set_parent_elsewhere(struct rb_node *node, struct rb_node *old_parent,
                          struct rb_node *parent, struct rb_node *other) {
    rb_set_parent(node, other);
}
```

```click
verifying "rb_at_wrong_parent.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, Color, RbTree, RbTree),
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

void set_parent_elsewhere(struct rb_node* node, struct rb_node* old_parent,
                          struct rb_node* parent, struct rb_node* other) {
    consumes t: rb_at(node, old_parent);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    requires aligned(other, 8);
    requires other != parent;
    produces u: rb_at(node, parent);
    ensures u.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            execute();
            let u = fold(rb_at(node, parent), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}
```

```expect
fail: fold requires the instance body facts for the proposed fields
```
