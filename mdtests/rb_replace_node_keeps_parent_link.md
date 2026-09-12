# A replacement that leaves the parent link at the victim fails

`__rb_change_child` is the last thing `rb_replace_node` does, and it is what
makes the frame focus `new` instead of `victim`. A contract that produces the
frame still focused at `victim` is claiming the root cell — or the parent's
child link — was not updated. The exit fold of `ctx_at(victim, parent, root)`
then cannot restate `root->rb_node == child`, which the write has just made
false. This is the negative for [`rb_replace_node.md`](rb_replace_node.md)'s
frame clause.

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

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}

static inline unsigned long rb_color(struct rb_node *rb) {
    return rb->__rb_parent_color & 1;
}

static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
    rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;
}

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

static inline void rb_replace_node(struct rb_node *victim, struct rb_node *new,
                                   struct rb_root *root)
{
    struct rb_node *parent = rb_parent(victim);

    /* Copy the pointers/colour from the victim to the replacement */
    *new = *victim;

    /* Set the surrounding nodes to point to the replacement */
    if (victim->rb_left)
        rb_set_parent(victim->rb_left, new);
    if (victim->rb_right)
        rb_set_parent(victim->rb_right, new);
    __rb_change_child(victim, new, parent, root);
}
#endif
```

```c filename=rb_replace_node_keeps_parent_link.c
#include "rbtree.h"

void replace_root_node(struct rb_node *victim, struct rb_node *new_node,
                       struct rb_node *parent, struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}
```

```click
verifying "rb_replace_node_keeps_parent_link.c";

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

function rb_substitute(tree: RbTree, replacement: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, color, left, right) =>
            RbTree::Node(replacement, color, left, right),
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

void replace_root_node(struct rb_node* victim, struct rb_node* new_node,
                       struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(victim, parent, root);
    consumes t: rb_at(victim, parent);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires t.model != RbTree::Empty;
    requires c.model == Context::Top;
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(victim, parent, root);
    produces u: rb_at(new_node, parent);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            unfold(c);
            unfold(l);
            unfold(r);
            execute();
            let l2 = fold(rb_at(new_node->rb_left, new_node), { model: left_model }, {});
            let r2 = fold(rb_at(new_node->rb_right, new_node), { model: right_model }, {});
            let u = fold(rb_at(new_node, parent), {
                model: RbTree::Node(new_node, color, left_model, right_model)
            }, { left: l2, right: r2 });
            have u.model == rb_substitute(old(t.model), new_node) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_substitute(
                    RbTree::Node(identity, color, left_model, right_model), new_node));
                normalize();
            }
            let d = fold(ctx_at(victim, parent, root), { model: old(c.model) }, {});
            simp();
        },
    }
}
```

```expect
fail: fold requires the instance body facts for the proposed fields
```
