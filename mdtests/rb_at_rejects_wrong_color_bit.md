# a model with the wrong color bit cannot be folded

`rb_set_parent_color(node, parent, RB_BLACK)` leaves bit 0 of the parent word
set, so the only `RbTree::Node` model the node can carry is the one whose color
is `Black`. Proposing `Red` makes `(p->__rb_parent_color & 1) == color_bit(color)`
false, and the fold is refused rather than the color being taken on trust.

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

static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int32 color) {
    rb->__rb_parent_color = (unsigned long)p | color;
}
#endif
```

```c filename=rb_at_wrong_color.c
#include "rbtree.h"

void set_parent_black(struct rb_node *node, struct rb_node *old_parent, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_BLACK);
}
```

```click
verifying "rb_at_wrong_color.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
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
        },
    }
}

void set_parent_black(struct rb_node* node, struct rb_node* old_parent, struct rb_node* parent) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have color_bit(Color::Red) == 0 by {
                unfold(color_bit(Color::Red));
                normalize();
            }
            execute();
            let u = fold(rb_at(node), {
                model: RbTree::Node(identity, parent, Color::Red, left_model, right_model)
            }, { left: l, right: r });
            simp();
        },
    }
}
```

```expect
fail: fold requires the instance body facts for the proposed fields
```
