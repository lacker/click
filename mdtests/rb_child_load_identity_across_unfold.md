# A child's word keeps one load identity across an unfold

`rb_set_parent(victim->rb_left, new)` reads the child's packed word, ors the
replacement address into it, and writes it back. Refolding that child as
`rb_at(new_node->rb_left, new_node)` then needs the arm fact

```text
(((old & 1) | address(new_node)) & 1) == color_bit(lc)
```

and a `fold` discharges its body facts exactly. The premise that makes it true
is the fact the child's own arm stated before the write,
`(child->__rb_parent_color & 1) == color_bit(lc)`.

The two are the same cell in the same epoch, so they must be the same load
variable. They were not: the unfolded child's cells were named through the
pointer `rb_at`'s argument evaluated to, and the C's own read of
`victim->rb_left` minted a second identity for one value, related only by a
pointer equality. Naming is atomic across producers — the same rule
`docs/internals/canonicalization.md` states for contract lowering and
execution — so the second producer adopts the name the first one gave the
cell.

The victim's child is a full `RbTree::Node` here, which is what distinguishes
this fixture from `mdtests/rb_replace_node.md`'s childless victim, and the
child is reachable only as `victim->rb_left`: no wrapper parameter names it.

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

```c filename=rb_child_load_identity.c
#include "rbtree.h"

void reparent_left_child(struct rb_node *victim, struct rb_node *new_node,
                         struct rb_node *parent) {
    *new_node = *victim;
    rb_set_parent(victim->rb_left, new_node);
}
```

```click
verifying "rb_child_load_identity.c";

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
                        model: RbTree::Node(lid, lc, ll, lr)
                    }, { left: lleft, right: lright });
                    simp();
                },
            }
        },
    }
}
```

```expect
pass
```
