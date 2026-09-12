# only `0` is a null pointer constant at a pure pointer parameter

The positive is
[`rb_pure_null_pointer_argument.md`](rb_pure_null_pointer_argument.md): `0`
types as any pointer, in a pure function's body as in a resource argument.
Nothing else does. `rb_parent_consistent(t, 1)` names no object, and the C
null-pointer-constant rule does not reach it, so the type error stands.

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
#endif
```

```c filename=rb_pure_null_pointer_argument_rejects_nonzero.c
#include "rbtree.h"

struct rb_node *rb_left_of(struct rb_node *node) {
    return node->rb_left;
}
```

```click
verifying "rb_pure_null_pointer_argument_rejects_nonzero.c";

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

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
}

function ctx_holds(ctx: Context, sub: RbTree) -> int32 {
    match ctx {
        Context::Top => rb_parent_is(sub, 0),
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            rb_parent_is(sub, identity),
    }
}

function rb_parent_consistent(t: RbTree, p: struct rb_node*) -> int32
    decreases t
{
    match t {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if rb_parent_consistent(left, node) == 1 {
                if rb_parent_consistent(right, node) == 1 {
                    rb_parent_is(t, p)
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function rb_tree_parent_consistent(t: RbTree) -> int32 {
    rb_parent_consistent(t, 1)
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

struct rb_node* rb_left_of(struct rb_node* node) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_parent_is(t.model, 0) == 1;
    produces sub: rb_at(node);
    ensures rb_parent_is(sub.model, 0) == 1;
    ensures ctx_holds(Context::Top, sub.model) == 1;
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, node_parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            execute();
            let sub = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            have rb_parent_is(sub.model, 0) == 1 by {
                rewrite(sub.model == old(t.model));
                assumption();
            }
            have rb_tree_parent_consistent(sub.model)
                == rb_parent_consistent(sub.model, 0) by {
                unfold(rb_tree_parent_consistent(sub.model));
                normalize();
            }
            have ctx_holds(Context::Top, sub.model) == 1 by {
                unfold(ctx_holds(Context::Top, sub.model));
                assumption();
            }
            simp();
        },
    }
}
```

```expect
fail: function `rb_parent_consistent` argument 1 expects int32*, got int32
```
