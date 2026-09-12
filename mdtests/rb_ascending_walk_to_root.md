# an ascending walk on the node-keyed rbtree shapes

This is the ascent of
[`loop_ascending_walk_to_root.md`](loop_ascending_walk_to_root.md) on the
node-keyed rbtree shapes, `rb_at(p)` and `ctx_at(child, root)`, the model
package C1b re-keyed so that the top-level traversals in
[`rb_first_last.md`](rb_first_last.md) could name their instances at all. Every
rbtree fixup loop climbs this way, so the boundary the walk ends at is the one
`rb_insert_color`, `rb_next` and `__rb_erase_color` need.

The parent is a *payload*, not a resource parameter: `rb_at`'s `Node` arm owns
the packed parent word and states it as the payload's address plus the color
bit, and `ctx_at`'s `Left` frame owns the cells of the node its own
`identity` payload carries. Nothing in the C program is written through
`identity`. The loop's own C local `parent` is the pointer the statements read,
and the two are tied together by the loop's invariants: `ctx_node_is(c.model,
parent) == 1` says the frame's node is that local, and `c.model ==
ctx_reroot(c.model, parent)` says the same thing in a form `extract` can take a
field equality out of, by constructor injectivity. That gives `identity ==
parent` inside each framed arm.

Three verifier rules meet here, and each was a gap.

The head refutes `Context::Top`. The failed-guard fact `parent != 0` decides
`ctx_node_is`'s declared body at `Top`, `if parent == 0 { 1 } else { 0 }`, to
be `0` where the invariant says `1` (package A21;
[`loop_head_predicate_refutes_an_arm.md`](loop_head_predicate_refutes_an_arm.md)).

The exit refutes `Left` and `Right`. There the body at
`Context::Left(identity, ..)` is `if identity == parent { 1 } else { 0 }`, and
the arm's own `fact identity != 0` decides it against the exit's `parent == 0`,
so the walk learns what its frame *is*, `c.model == Context::Top`, and can fold
the root frame (package A21;
[`contract_predicate_refutes_a_framed_arm.md`](contract_predicate_refutes_a_framed_arm.md)).

The body reads the frame through the C local. `unfold(c)` owns, names, and
states the arm's cells at the pointer the proved equality identifies the
payload with, so `node = parent; parent = rb_parent(node);` reads the frame's
own parent word, the refold of the lifted node requires that word at the same
spelling, and the back edge hands `up` on as the next frame (package A22;
[`binding_cell_read_through_equal_local.md`](binding_cell_read_through_equal_local.md)
is the reduction). Without it the read is refused with `missing resource fact
views symbolic-pointer:…` while ownership of that very cell is held one
provable equality away.

The frames carry the node they own as the payload `identity` because the frame
above is keyed by that node, and `plug` still has to know which node each frame
rebuilds. Parent/child consistency travels with them: `rb_parent_is(sibling_model,
identity) == 1` is what lets the lifted node be refolded with the old subtree
and the sibling as its children, and `ctx_node_is(up_model, grandparent) == 1`
with `up_model == ctx_reroot(up_model, grandparent)` is what re-establishes the
walk's own invariants one frame higher, where `rb_parent` has just put the
grandparent into `parent`.

The loop body reads the parent through the unchanged Linux `rb_parent`, so each
iteration clears the color tag out of the packed word and recovers the parent's
provenance from the frame's own facts. The exit is the root: the produced
instances name that position with `ctx_at(result, root)` and `rb_at(result)`,
and neither clause needs a pointer the C has no name for.

Two limits are deliberate here, and both are verifier gaps rather than modeling
choices.

`rb_next`'s own ascent is
`while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;`.
Its C0 form is refused twice over: an assignment is not an expression in the
supported subset, and a short-circuit guard whose second conjunct reads memory
leaves the `loop` tactic two statement successors. That guard also stops at the
first left frame, a position no contract can name, which is why package C4 owns
`rb_next` in full; see
[`rb_next_conjunctive_guard.md`](rb_next_conjunctive_guard.md).

The loop carries the same structural measure the scaffold ascent does,
`decreases c;`, even though its body calls the contract-less inline
`rb_parent`. An inline body has no contract boundary: it executes at the call
site, so termination reads it as a call-graph node of its own rather than as an
opaque callee needing a verified rule. `rb_parent`'s body is one return of a
masked load, with no loop, no recursion, and no further call, so it terminates
by construction and the ascent's own ranking is the whole of the obligation.

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
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
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

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
    }
}

function ctx_node_is(ctx: Context, p: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => if p == 0 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
    }
}

function ctx_reroot(ctx: Context, p: struct rb_node*) -> Context {
    match ctx {
        Context::Top => Context::Top,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            Context::Left(p, grandparent, color, sibling_model, up_model),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            Context::Right(p, grandparent, color, sibling_model, up_model),
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

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => {
            owns root->rb_node;
            fact root != 0;
            fact root->rb_node == child;
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_left);
            owns up: ctx_at(identity, root);
            fact identity != 0;
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_right == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact (identity->__rb_parent_color & 1) == color_bit(color);
            fact sibling.model == sibling_model;
            fact up.model == up_model;
            fact rb_parent_is(sibling_model, identity) == 1;
            fact ctx_node_is(up_model, grandparent) == 1;
            fact up_model == ctx_reroot(up_model, grandparent);
        },
    }
}

function plug(ctx: Context, sub: RbTree) -> RbTree
    decreases ctx
{
    match ctx {
        Context::Top => sub,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model)),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub)),
    }
}

struct rb_node* rb_root_of(struct rb_node* node, struct rb_node* parent,
                           struct rb_root* root) {
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_parent_is(t.model, parent) == 1;
    requires ctx_node_is(c.model, parent) == 1;
    requires c.model == ctx_reroot(c.model, parent);
    produces ctx: ctx_at(result, root);
    produces sub: rb_at(result);
    ensures sub.model == plug(old(c.model), old(t.model));
} by {
    loop {
        decreases c;
        owns c: ctx_at(node, root);
        owns t: rb_at(node);
        invariant t.model != RbTree::Empty;
        invariant rb_parent_is(t.model, parent) == 1;
        invariant ctx_node_is(c.model, parent) == 1;
        invariant c.model == ctx_reroot(c.model, parent);
        invariant plug(c.model, t.model) == plug(old(c.model), old(t.model));

        initialize by simp;
        preserve by {
            match c.model {
                Context::Top => { contradiction(c.model == Context::Top); },
                Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                    have ctx_reroot(Context::Left(identity, grandparent, color,
                                                  sibling_model, up_model), parent)
                        == Context::Left(parent, grandparent, color,
                                         sibling_model, up_model) by {
                        unfold(ctx_reroot(Context::Left(identity, grandparent, color,
                                                        sibling_model, up_model), parent));
                        normalize();
                    }
                    have Context::Left(identity, grandparent, color, sibling_model, up_model)
                        == Context::Left(parent, grandparent, color,
                                         sibling_model, up_model) by {
                        rewrite(Context::Left(identity, grandparent, color,
                                              sibling_model, up_model) == c.model);
                        rewrite(c.model == ctx_reroot(c.model, parent));
                        rewrite(c.model == Context::Left(identity, grandparent, color,
                                                         sibling_model, up_model));
                        rewrite(ctx_reroot(Context::Left(identity, grandparent, color,
                                                         sibling_model, up_model), parent)
                            == Context::Left(parent, grandparent, color,
                                             sibling_model, up_model));
                        normalize();
                    }
                    have identity == parent by {
                        extract(identity == parent);
                    }
                    have plug(up_model,
                              RbTree::Node(identity, grandparent, color,
                                           t.model, sibling_model))
                        == plug(old(c.model), old(t.model)) by {
                        unfold(plug(Context::Left(identity, grandparent, color,
                                                  sibling_model, up_model), t.model));
                        rewrite(plug(up_model,
                                     RbTree::Node(identity, grandparent, color,
                                                  t.model, sibling_model))
                            == plug(Context::Left(identity, grandparent, color,
                                                  sibling_model, up_model), t.model));
                        rewrite(Context::Left(identity, grandparent, color,
                                              sibling_model, up_model) == c.model);
                        assumption();
                    }
                    unfold(c) as { sibling: s, up: u };
                    step();
                    step();
                    have rb_parent_is(RbTree::Node(identity, grandparent, color,
                                                   t.model, sibling_model),
                                      grandparent) == 1 by {
                        unfold(rb_parent_is(RbTree::Node(identity, grandparent, color,
                                                         t.model, sibling_model),
                                            grandparent));
                        normalize();
                    }
                    let lifted = fold(rb_at(node), {
                        model: RbTree::Node(identity, grandparent, color,
                                            t.model, sibling_model)
                    }, { left: t, right: s });
                    close_invariants();
                },
                Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                    have ctx_reroot(Context::Right(identity, grandparent, color,
                                                   sibling_model, up_model), parent)
                        == Context::Right(parent, grandparent, color,
                                          sibling_model, up_model) by {
                        unfold(ctx_reroot(Context::Right(identity, grandparent, color,
                                                         sibling_model, up_model), parent));
                        normalize();
                    }
                    have Context::Right(identity, grandparent, color, sibling_model, up_model)
                        == Context::Right(parent, grandparent, color,
                                          sibling_model, up_model) by {
                        rewrite(Context::Right(identity, grandparent, color,
                                               sibling_model, up_model) == c.model);
                        rewrite(c.model == ctx_reroot(c.model, parent));
                        rewrite(c.model == Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model));
                        rewrite(ctx_reroot(Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model), parent)
                            == Context::Right(parent, grandparent, color,
                                              sibling_model, up_model));
                        normalize();
                    }
                    have identity == parent by {
                        extract(identity == parent);
                    }
                    have plug(up_model,
                              RbTree::Node(identity, grandparent, color,
                                           sibling_model, t.model))
                        == plug(old(c.model), old(t.model)) by {
                        unfold(plug(Context::Right(identity, grandparent, color,
                                                   sibling_model, up_model), t.model));
                        rewrite(plug(up_model,
                                     RbTree::Node(identity, grandparent, color,
                                                  sibling_model, t.model))
                            == plug(Context::Right(identity, grandparent, color,
                                                   sibling_model, up_model), t.model));
                        rewrite(Context::Right(identity, grandparent, color,
                                               sibling_model, up_model) == c.model);
                        assumption();
                    }
                    unfold(c) as { sibling: s, up: u };
                    step();
                    step();
                    have rb_parent_is(RbTree::Node(identity, grandparent, color,
                                                   sibling_model, t.model),
                                      grandparent) == 1 by {
                        unfold(rb_parent_is(RbTree::Node(identity, grandparent, color,
                                                         sibling_model, t.model),
                                            grandparent));
                        normalize();
                    }
                    let lifted = fold(rb_at(node), {
                        model: RbTree::Node(identity, grandparent, color,
                                            sibling_model, t.model)
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
    let ctx = fold(ctx_at(node, root), { model: Context::Top });
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent_model, color, left_model, right_model) => {
            have RbTree::Node(identity, parent_model, color, left_model, right_model)
                == plug(old(c.model), old(t.model)) by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model)
                    == t.model);
                assumption();
            }
            unfold(t) as { left: l, right: r };
            let sub = fold(rb_at(node), {
                model: RbTree::Node(identity, parent_model, color, left_model, right_model)
            }, { left: l, right: r });
            have sub.model == plug(old(c.model), old(t.model)) by {
                rewrite(sub.model
                    == RbTree::Node(identity, parent_model, color, left_model, right_model));
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
