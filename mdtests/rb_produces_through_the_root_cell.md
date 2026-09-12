# a void function names its produced tree through the root cell

A `produces` clause is the caller's view of what it gets back, so its arguments
are read on the return side, and a parameter there means the value the caller
passed rather than one the body reassigned
([`loop_ascending_produces_wrong_arguments.md`](loop_ascending_produces_wrong_arguments.md)).
`result` is the other thing a produced clause can name — and a `void` function
has no `result`.

`__rb_insert` is exactly that shape: it returns nothing, it reassigns `node` as
the fixup climbs, and the tree it leaves behind hangs at the root
([`rb_insert_color.md`](rb_insert_color.md)). Neither `result` nor the
reassigned parameter names the whole tree at the exit. The root cell does:
when the contract owns `root->rb_node`, `produces u: rb_at(root->rb_node)`
reads that cell in the exit state, which is the position the body linked, and
the caller reading the same owned cell after the call sees the same object.
This fixture is the smallest version of that spelling: the body links `node` as
the root, and the produced whole tree is named through the cell rather than
through the parameter that happens to equal it here.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

struct rb_root {
    struct rb_node *rb_node;
};
#endif
```

```c filename=rb_produces_through_the_root_cell.c
#include "rbtree.h"

void rb_set_root(struct rb_node *node, struct rb_root *root) {
    root->rb_node = node;
}
```

```click
verifying "rb_produces_through_the_root_cell.c";

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

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
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
            fact rb_parent_is(left_model, p) == 1;
            fact rb_parent_is(right_model, p) == 1;
        },
    }
}

void rb_set_root(struct rb_node* node, struct rb_root* root) {
    requires root != 0;
    owns root->rb_node;
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    produces u: rb_at(root->rb_node);
    ensures u.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            execute();
            let u = fold(rb_at(root->rb_node), { model: old(t.model) },
                         { left: l, right: r });
            simp();
        },
    }
}
```

```expect
pass
```
