# an rbtree ascent whose guard is a conjunction

This is the ascent of [`rb_ascending_walk_to_root.md`](rb_ascending_walk_to_root.md)
with the short-circuit guard `rb_next` climbs with. Every iteration consumes
one frame — unfold the frame, take the C step that moves the cursor up, fold
the node the frame owned into a larger subtree — and the measure is the
context, `decreases c;`. What is new is the guard: it leaves the loop by two
paths, `parent == 0` and `parent != 0` with the second conjunct false, and the
loop rule certifies both and exports their join. Before that the `loop` tactic
refused the whole loop with "requires exactly one statement successor, got 2".

The C is a minimal translation of the Linux guard. `rb_next` writes
`while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;`,
and an assignment is not an expression in the supported C0 subset, so the
assignment moves into the body exactly as `rb_ascending_walk_to_root.md`
already writes it. That is the whole translation.

The second conjunct is the focused node's own link rather than
`node == parent->rb_right`. It reads memory either way, which is the point
here, but the parent's link cells belong to the frame `c`, and at a loop head
no arm of a three-constructor frame is selected, so `parent->rb_right` cannot
be read there at all and the guard is refused as undecided. The guard's own
first conjunct `parent != 0` refutes the `Top` arm, and both remaining arms own
`parent->rb_right`, so the read authority is there to be published — but
publishing what the arms a guard prefix leaves possible agree on is an
extension of arm selection (D7), not part of certifying several exits.

The contract consumes the walk's instances and produces none. The ascent stops
either at the root or at the first node with a right child, and no contract can
name the second position: `ctx_at(child, parent, root)` and `rb_at(p, parent)`
take the focused node's parent, and a produced instance's arguments are the
entry-time ones. That is gap 35, which package C1b re-keys the model to fix.
What this fixture states at the exit is what the loop proved on the way:
`plug(c.model, t.model)` is unchanged from the entry model at every iteration,
and the focused node is not null.

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

struct rb_root {
    struct rb_node *rb_node;
};

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}
#endif
```

```c filename=rb_ascent_conjunctive_guard.c
#include "rbtree.h"

struct rb_node *rb_up_while_no_right_child(struct rb_node *node,
                                           struct rb_node *parent,
                                           struct rb_root *root) {
    while (parent != 0 && node->rb_right == 0) {
        node = parent;
        parent = rb_parent(node);
    }

    return node;
}
```

```click
verifying "rb_ascent_conjunctive_guard.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, struct rb_node*, Color, RbTree, Context),
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
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_right, parent);
            owns up: ctx_at(parent, grandparent, root);
            fact parent != 0;
            fact parent == identity;
            fact aligned(parent, 8);
            fact aligned(grandparent, 8);
            fact parent->rb_left == child;
            fact parent->__rb_parent_color
                == address(grandparent) + (parent->__rb_parent_color & 1);
            fact (parent->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_left, parent);
            owns up: ctx_at(parent, grandparent, root);
            fact parent != 0;
            fact parent == identity;
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

function plug(ctx: Context, sub: RbTree) -> RbTree
    decreases ctx
{
    match ctx {
        Context::Top => sub,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, color, sub, sibling_model)),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, color, sibling_model, sub)),
    }
}

struct rb_node* rb_up_while_no_right_child(struct rb_node* node, struct rb_node* parent,
                           struct rb_root* root) {
    consumes c: ctx_at(node, parent, root);
    consumes t: rb_at(node, parent);
    requires t.model != RbTree::Empty;
    ensures result != 0;
} by {
    loop {
        decreases c;
        owns c: ctx_at(node, parent, root);
        owns t: rb_at(node, parent);
        invariant t.model != RbTree::Empty;
        invariant plug(c.model, t.model) == plug(old(c.model), old(t.model));

        initialize by simp;
        preserve by {
            match c.model {
                Context::Top => { contradiction(c.model == Context::Top); },
                Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                    have plug(up_model,
                              RbTree::Node(identity, color, t.model, sibling_model))
                        == plug(old(c.model), old(t.model)) by {
                        unfold(plug(Context::Left(identity, grandparent, color,
                                                  sibling_model, up_model), t.model));
                        rewrite(plug(up_model,
                                     RbTree::Node(identity, color, t.model, sibling_model))
                            == plug(Context::Left(identity, grandparent, color,
                                                  sibling_model, up_model), t.model));
                        rewrite(Context::Left(identity, grandparent, color,
                                              sibling_model, up_model) == c.model);
                        assumption();
                    }
                    unfold(c) as { sibling: s, up: u };
                    step();
                    step();
                    let lifted = fold(rb_at(node, parent), {
                        model: RbTree::Node(identity, color, t.model, sibling_model)
                    }, { left: t, right: s });
                    close_invariants();
                },
                Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                    have plug(up_model,
                              RbTree::Node(identity, color, sibling_model, t.model))
                        == plug(old(c.model), old(t.model)) by {
                        unfold(plug(Context::Right(identity, grandparent, color,
                                                   sibling_model, up_model), t.model));
                        rewrite(plug(up_model,
                                     RbTree::Node(identity, color, sibling_model, t.model))
                            == plug(Context::Right(identity, grandparent, color,
                                                   sibling_model, up_model), t.model));
                        rewrite(Context::Right(identity, grandparent, color,
                                               sibling_model, up_model) == c.model);
                        assumption();
                    }
                    unfold(c) as { sibling: s, up: u };
                    step();
                    step();
                    let lifted = fold(rb_at(node, parent), {
                        model: RbTree::Node(identity, color, sibling_model, t.model)
                    }, { left: s, right: t });
                    close_invariants();
                },
            }
        }
    }
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            step();
            simp();
        },
    }
}
```

```expect
pass
```
