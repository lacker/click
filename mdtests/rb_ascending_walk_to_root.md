# an ascending walk on the rbtree shapes

This is the ascent of
[`loop_ascending_walk_to_root.md`](loop_ascending_walk_to_root.md) on the
shapes package C1 landed: `rb_at(p, parent)`, whose `Node` arm owns the packed
parent word and states it as the parent's address plus the color bit, and
`ctx_at(child, parent, root)`, whose `Top` frame owns `root->rb_node` and says
the root struct points at the focused node. Every rbtree fixup loop climbs
this way, so the boundary the walk ends at is the one `rb_insert_color`,
`rb_next` and `__rb_erase_color` need.

The loop body reads the parent through the unchanged Linux `rb_parent`, so
each iteration clears the color tag out of the packed word and recovers the
parent's provenance from the frame's own facts. The frames carry the node they
own as the payload `identity`, because the frame above is keyed by
`(parent, grandparent)` and `plug` still has to know which node each frame
rebuilds.

The exit is the root: the failed guard `parent != 0` refutes the `Left` and
`Right` arms' `fact parent != 0`, the exit learns `c.model == Context::Top`,
and the produced instances name that position with the null pointer constant,
`ctx_at(result, 0, root)` and `rb_at(result, 0)`.

Two limits are deliberate here, and both are verifier gaps rather than
modeling choices.

`rb_next`'s own ascent is
`while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;`.
Its C0 form is refused twice over: an assignment is not an expression in the
supported subset, and a short-circuit guard whose second conjunct reads memory
leaves the `loop` tactic two statement successors. That
guard also stops at the first left frame, a position no contract can name,
which is why package C4 owns `rb_next` in full.

The loop carries the same structural measure the scaffold ascent does,
`decreases c;`, even though its body calls the contract-less inline
`rb_parent`. An inline body has no contract boundary: it executes at the call
site, so termination reads it as a call-graph node of its own rather than as
an opaque callee needing a verified rule. `rb_parent`'s body is one return of
a masked load, with no loop, no recursion, and no further call, so it
terminates by construction and the ascent's own ranking is the whole of the
obligation.

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

```c filename=rb_ascending_walk_to_root.c
#include "rbtree.h"

struct rb_node *rb_root_of(struct rb_node *node, struct rb_node *parent, struct rb_root *root) {
    while (parent != 0) {
        node = parent;
        parent = rb_parent(node);
    }

    return node;
}
```

```click
verifying "rb_ascending_walk_to_root.c";

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

struct rb_node* rb_root_of(struct rb_node* node, struct rb_node* parent,
                           struct rb_root* root) {
    consumes c: ctx_at(node, parent, root);
    consumes t: rb_at(node, parent);
    requires t.model != RbTree::Empty;
    produces ctx: ctx_at(result, 0, root);
    produces sub: rb_at(result, 0);
    ensures sub.model == plug(old(c.model), old(t.model));
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
    have plug(c.model, t.model) == t.model by {
        rewrite(c.model == Context::Top);
        unfold(plug(Context::Top, t.model));
        normalize();
    }
    have t.model == plug(old(c.model), old(t.model)) by {
        rewrite(t.model == plug(c.model, t.model));
        assumption();
    }
    unfold(c);
    let ctx = fold(ctx_at(node, parent, root), { model: Context::Top });
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            have RbTree::Node(identity, color, left_model, right_model)
                == plug(old(c.model), old(t.model)) by {
                rewrite(RbTree::Node(identity, color, left_model, right_model) == t.model);
                assumption();
            }
            unfold(t) as { left: l, right: r };
            let sub = fold(rb_at(node, parent), {
                model: RbTree::Node(identity, color, left_model, right_model)
            }, { left: l, right: r });
            have sub.model == plug(old(c.model), old(t.model)) by {
                rewrite(sub.model == RbTree::Node(identity, color, left_model, right_model));
                assumption();
            }
            step();
            simp();
        },
    }
}
```

```expect
pass
```
