# Naming the unfolded child's cells does not make the fold vacuous

`rb_set_parent(victim->rb_left, new_node)` rewrites the unfolded child's packed
word, and an `unfold` names the child's cells so that the C's read of that
word is the load its arm spoke about (the positive refold of rewritten child
words is `mdtests/rb_replace_node_with_children.md`). Here the refold
proposes `Color::Black` for a child whose arm bound an arbitrary color. The
exact body-fact check still has to discharge `(((old & 1) | address(new_node)) & 1) == color_bit(Color::Black)`
and the premise says only that the word's bit is `color_bit(lc)`, so the fold
is refused. The proof preserves the original child pointer across the three
field stores of the record assignment before opening the child for reparenting.

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
            let { left: l, right: r } = unfold(t);
            match l.model {
                RbTree::Empty => { contradiction(l.model == RbTree::Empty); },
                RbTree::Node(lid, lc, ll, lr) => {
                    have separate(memory((new_node as (int32 *))[0..2]), memory(victim->rb_left)) by close();
                    have separate(memory((new_node as (int32 *))[2..4]), memory(victim->rb_left)) by close();
                    have separate(memory((new_node as (int32 *))[4..6]), memory(victim->rb_left)) by close();
                    step();
                    have separate(statement(0).region(0).footprint, memory(victim->rb_left)) by close();
                    have victim->rb_left == at(statement(0).region(0).entry, victim->rb_left) by {
                        preserve(memory(victim->rb_left), statement(0).region(0));
                    }
                    step();
                    have separate(statement(0).region(1).footprint, memory(victim->rb_left)) by close();
                    have victim->rb_left == at(statement(0).region(1).entry, victim->rb_left) by {
                        preserve(memory(victim->rb_left), statement(0).region(1));
                    }
                    step();
                    have separate(statement(0).region(2).footprint, memory(victim->rb_left)) by close();
                    have victim->rb_left == at(statement(0).region(2).entry, victim->rb_left) by {
                        preserve(memory(victim->rb_left), statement(0).region(2));
                    }
                    let { left: lleft, right: lright } = unfold(l);
                    step_until(function.exit);
                    let l2 = fold(rb_at(lid, new_node), {
                        model: RbTree::Node(lid, Color::Black, ll, lr),
                        left: lleft, right: lright
                    }) {
                        requires (lid->__rb_parent_color & 1) == color_bit(Color::Black) by {
                            have (lid->__rb_parent_color & 1) == color_bit(Color::Black) by close();
                            close();
                        }
                    }
                    close();
                },
            }
        },
    }
}
```

```expect
fail: `have` failed for `(lid->__rb_parent_color & 1) == color_bit(Color::Black())`
```
