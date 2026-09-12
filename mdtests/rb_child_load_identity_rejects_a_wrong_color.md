# Naming the unfolded child's cells does not make the fold vacuous

The negative beside `mdtests/rb_child_load_identity_across_unfold.md`. The same
C rewrites the child's packed word, but the refold proposes `Color::Black` for
a child whose arm bound an arbitrary color. The exact body-fact check still has
to discharge `(((old & 1) | address(new_node)) & 1) == color_bit(Color::Black)`
and the premise says only that the word's bit is `color_bit(lc)`, so the fold
is refused. Naming the cells one `unfold` exposes settles *which* value the two
sides talk about; it proves nothing about that value.

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

```c filename=rb_child_wrong_color.c
#include "rbtree.h"

void reparent_left_child(struct rb_node *victim, struct rb_node *new_node,
                         struct rb_node *parent) {
    *new_node = *victim;
    rb_set_parent(victim->rb_left, new_node);
}
```

```click
verifying "rb_child_wrong_color.c";

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

void reparent_left_child(struct rb_node* victim, struct rb_node* new_node,
                         struct rb_node* parent) {
    consumes t: rb_at(victim, parent);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires t.model != RbTree::Empty;
    requires victim->rb_left != 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces l2: rb_at(new_node->rb_left, new_node);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            match l.model {
                RbTree::Empty => { contradiction(l.model == RbTree::Empty); },
                RbTree::Node(lid, lc, ll, lr) => {
                    unfold(l) as { left: lleft, right: lright };
                    execute();
                    let l2 = fold(rb_at(new_node->rb_left, new_node), {
                        model: RbTree::Node(lid, Color::Black, ll, lr)
                    }, { left: lleft, right: lright });
                    simp();
                },
            }
        },
    }
}
```

```expect
fail: `reparent_left_child.contract` proof step checked step 2: fold requires the instance body facts for the proposed fields
```
