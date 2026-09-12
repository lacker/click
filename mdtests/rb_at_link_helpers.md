# rbtree link helpers over a modeled `rb_at(p)`

`rb_at(p)` folds one `rb_node` subtree into an `RbTree` model that carries the
node's own address, **its parent's address**, its color, and both submodels.
The parent is a model *payload*, not a resource parameter: the top-level Linux
traversals (`rb_first`, `rb_next`) keep no C local naming the focused node's
parent, so a parameter spelling has nothing to put in a loop binder or a
`produces` clause. This is gap 35 and its decision in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md).

With the parent inside the model, the node's own arm still owns
`p->__rb_parent_color` and still states what that word holds — the payload
parent's address with the color in bit 0. Nothing is owned through a payload:
`parent` is compared and its address is taken, never dereferenced.

Parent/child consistency *is* a body fact here, as D2 intends:
`rb_parent_is(left_model, p) == 1` says the left submodel's own parent payload
is this node, and the mirror says it of the right. Every constructor `fold`
discharges both exactly, from the facts the matching `unfold` published.

This is what package A20 unblocked. Until then every such fold refused with
`fold requires the instance body facts for the proposed fields` while the
identical proposition was an available checked fact immediately before it. The
deciding feature was the *pointer* argument: a pure function's pointer
parameter is an array-ref argument carrying the ambient memory snapshot, so
`rb_parent_is(left_model, node)` proved before `execute()` and the same
proposition demanded by a fold after it were two different terms. A function
that reads no memory is now anchored to one canonical snapshot, so the two are
one term; see [`docs/concepts/resources.md`](../docs/concepts/resources.md).

The tagged word is stated as two facts rather than the single
`p->__rb_parent_color == address(parent) + color_bit(color)`. Their conjunction
says exactly that, but the split form keeps the tag structurally below 4, which
is what the kernel's tagged-pointer step needs to clear the tag bits and
recover the parent's provenance; `color_bit(color)` is opaque until it is
unfolded at a concrete color, so the single fact leaves the tag unbounded and
`rb_parent`'s `& ~3` cannot be justified. `color_bit_is_a_bit` records that the
two forms agree on a range: a color bit is 0 or 1.

`rb_parent` and `rb_red_parent` no longer have a resource argument to name their
answer, so they state it on the model: `rb_parent_is(old(t.model), result) == 1`.
The C result is bridged to the payload by the arm's own word fact, and the pure
step that evaluates `rb_parent_is` at the constructor runs before `execute()` —
a pure `have` over a payload `if` does not close at a post-execution frontier.

`rb_set_black` and `rb_red_parent` are only correct on a red node — one adds
`RB_BLACK` to the word, the other casts the whole word — so both are contracted
under `rb_color_bit(t.model) == 0`, which is the model saying the same thing.

The C is the unchanged Linux helper set: `rb_parent`, `rb_color`,
`rb_set_parent`, `rb_set_parent_color`, `rb_set_black`, `rb_red_parent`, and
`rb_link_node`, with the header of `mdtests/rb_parent_family.md` extended by
the remaining ones. Each contracted caller is a thin wrapper, so the helpers
themselves are never edited; a wrapper keeps a parameter only when the helper
it calls takes one.

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

static inline struct rb_node *rb_parent(struct rb_node *r) {
    return (struct rb_node *)(r->__rb_parent_color & ~3);
}

static inline unsigned long rb_color(struct rb_node *rb) {
    return rb->__rb_parent_color & 1;
}

static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
    rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;
}

static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int32 color) {
    rb->__rb_parent_color = (unsigned long)p | color;
}

static inline void rb_set_black(struct rb_node *rb) {
    rb->__rb_parent_color += RB_BLACK;
}

static inline struct rb_node *rb_red_parent(struct rb_node *red) {
    return (struct rb_node *)red->__rb_parent_color;
}

static inline void rb_link_node(struct rb_node *node, struct rb_node *parent,
                                struct rb_node **rb_link) {
    node->__rb_parent_color = (unsigned long)parent;
    node->rb_left = NULL;
    node->rb_right = NULL;
    *rb_link = node;
}
#endif
```

```c filename=rb_at_link_helpers.c
#include "rbtree.h"

struct rb_node *node_parent(struct rb_node *node) {
    return rb_parent(node);
}

unsigned long node_color(struct rb_node *node) {
    return rb_color(node);
}

void set_parent(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent(node, parent);
}

void set_parent_black(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_BLACK);
}

void set_parent_red(struct rb_node *node, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_RED);
}

void set_black(struct rb_node *node) {
    rb_set_black(node);
}

struct rb_node *red_parent_of(struct rb_node *node) {
    return rb_red_parent(node);
}

void link_node(struct rb_node *node, struct rb_node *parent, struct rb_node **rb_link) {
    rb_link_node(node, parent, rb_link);
}
```

```click
verifying "rb_at_link_helpers.c";

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

function rb_color_bit(tree: RbTree) -> int {
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(identity, parent, color, left, right) => color_bit(color),
    }
}

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(identity, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
    }
}

function rb_with_color(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, old_color, left, right) =>
            RbTree::Node(identity, parent, color, left, right),
    }
}

function rb_reparent(tree: RbTree, new_parent: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) =>
            RbTree::Node(identity, new_parent, color, left, right),
    }
}

function rb_reparent_color(tree: RbTree, new_parent: struct rb_node*, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, old_color, left, right) =>
            RbTree::Node(identity, new_parent, color, left, right),
    }
}

theorem color_bit_is_a_bit(color: Color) {
    ensures color_bit(color) >= 0 by {
        induct(color) as ih {
            Color::Red => {
                unfold(color_bit(Color::Red));
                simp();
            }
            Color::Black => {
                unfold(color_bit(Color::Black));
                simp();
            }
        }
    }
    ensures color_bit(color) <= 1 by {
        induct(color) as ih {
            Color::Red => {
                unfold(color_bit(Color::Red));
                simp();
            }
            Color::Black => {
                unfold(color_bit(Color::Black));
                simp();
            }
        }
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

struct rb_node* node_parent(struct rb_node* node) {
    owns t: rb_at(node);
    requires t.model != RbTree::Empty;
    ensures rb_parent_is(old(t.model), result) == 1;
    ensures t.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have rb_parent_is(old(t.model), parent) == 1 by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_parent_is(
                    RbTree::Node(identity, parent, color, left_model, right_model), parent));
                normalize();
            }
            execute();
            have result == parent by { simp(); }
            have rb_parent_is(old(t.model), result) == 1 by {
                rewrite(result == parent);
                assumption();
            }
            let t = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}

unsigned long node_color(struct rb_node* node) {
    owns t: rb_at(node);
    requires t.model != RbTree::Empty;
    ensures result == rb_color_bit(old(t.model));
    ensures t.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, parent, color, left_model, right_model)));
                assumption();
            }
            execute();
            let t = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}

void set_parent(struct rb_node* node, struct rb_node* parent) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node);
    ensures u.model == rb_reparent(old(t.model), parent);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, old_parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have rb_reparent(
                    RbTree::Node(identity, old_parent, color, left_model, right_model), parent)
                == RbTree::Node(identity, parent, color, left_model, right_model) by {
                unfold(rb_reparent(
                    RbTree::Node(identity, old_parent, color, left_model, right_model), parent));
                normalize();
            }
            execute();
            let u = fold(rb_at(node), {
                model: RbTree::Node(identity, parent, color, left_model, right_model)
            }, { left: l, right: r });
            have u.model == rb_reparent(old(t.model), parent) by {
                rewrite(u.model
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                rewrite(old(t.model)
                    == RbTree::Node(identity, old_parent, color, left_model, right_model));
                unfold(rb_reparent(
                    RbTree::Node(identity, old_parent, color, left_model, right_model), parent));
                simp();
            }
            simp();
        },
    }
}

void set_parent_black(struct rb_node* node, struct rb_node* parent) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node);
    ensures u.model == rb_reparent_color(old(t.model), parent, Color::Black);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, old_parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have color_bit(Color::Black) == 1 by {
                unfold(color_bit(Color::Black));
                normalize();
            }
            execute();
            let u = fold(rb_at(node), {
                model: RbTree::Node(identity, parent, Color::Black, left_model, right_model)
            }, { left: l, right: r });
            have u.model == rb_reparent_color(old(t.model), parent, Color::Black) by {
                rewrite(u.model
                    == RbTree::Node(identity, parent, Color::Black, left_model, right_model));
                rewrite(old(t.model)
                    == RbTree::Node(identity, old_parent, color, left_model, right_model));
                unfold(rb_reparent_color(
                    RbTree::Node(identity, old_parent, color, left_model, right_model),
                    parent, Color::Black));
                simp();
            }
            simp();
        },
    }
}

void set_parent_red(struct rb_node* node, struct rb_node* parent) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node);
    ensures u.model == rb_reparent_color(old(t.model), parent, Color::Red);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, old_parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have color_bit(Color::Red) == 0 by {
                unfold(color_bit(Color::Red));
                normalize();
            }
            execute();
            let u = fold(rb_at(node), {
                model: RbTree::Node(identity, parent, Color::Red, left_model, right_model)
            }, { left: l, right: r });
            have u.model == rb_reparent_color(old(t.model), parent, Color::Red) by {
                rewrite(u.model
                    == RbTree::Node(identity, parent, Color::Red, left_model, right_model));
                rewrite(old(t.model)
                    == RbTree::Node(identity, old_parent, color, left_model, right_model));
                unfold(rb_reparent_color(
                    RbTree::Node(identity, old_parent, color, left_model, right_model),
                    parent, Color::Red));
                simp();
            }
            simp();
        },
    }
}

void set_black(struct rb_node* node) {
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    produces u: rb_at(node);
    ensures u.model == rb_with_color(old(t.model), Color::Black);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, parent, color, left_model, right_model)));
                assumption();
            }
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == rb_color_bit(old(t.model)));
                simp();
            }
            have node->__rb_parent_color == address(parent) by {
                rewrite(node->__rb_parent_color
                    == address(parent) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0);
                normalize();
            }
            have color_bit(Color::Black) == 1 by {
                unfold(color_bit(Color::Black));
                normalize();
            }
            execute();
            let u = fold(rb_at(node), {
                model: RbTree::Node(identity, parent, Color::Black, left_model, right_model)
            }, { left: l, right: r });
            have u.model == rb_with_color(old(t.model), Color::Black) by {
                rewrite(u.model
                    == RbTree::Node(identity, parent, Color::Black, left_model, right_model));
                rewrite(old(t.model)
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_with_color(
                    RbTree::Node(identity, parent, color, left_model, right_model), Color::Black));
                simp();
            }
            simp();
        },
    }
}

struct rb_node* red_parent_of(struct rb_node* node) {
    owns t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    ensures rb_parent_is(old(t.model), result) == 1;
    ensures t.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, parent, color, left_model, right_model)));
                assumption();
            }
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == rb_color_bit(old(t.model)));
                simp();
            }
            have node->__rb_parent_color == address(parent) by {
                rewrite(node->__rb_parent_color
                    == address(parent) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0);
                normalize();
            }
            have rb_parent_is(old(t.model), parent) == 1 by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_parent_is(
                    RbTree::Node(identity, parent, color, left_model, right_model), parent));
                normalize();
            }
            execute();
            have result == parent by { simp(); }
            have rb_parent_is(old(t.model), result) == 1 by {
                rewrite(result == parent);
                assumption();
            }
            let t = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}

void link_node(struct rb_node* node, struct rb_node* parent, struct rb_node** rb_link) {
    consumes node->__rb_parent_color;
    consumes node->rb_left;
    consumes node->rb_right;
    owns rb_link[0..1];
    requires node != 0;
    requires aligned(node, 8);
    requires aligned(parent, 8);
    produces t: rb_at(node);
    ensures t.model
        == RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty);
    ensures rb_link[0] == node;
} by {
    have color_bit(Color::Red) == 0 by {
        unfold(color_bit(Color::Red));
        normalize();
    }
    have rb_parent_is(RbTree::Empty, node) == 1 by {
        unfold(rb_parent_is(RbTree::Empty, node));
        normalize();
    }
    execute();
    let l = fold(rb_at(node->rb_left), { model: RbTree::Empty });
    let r = fold(rb_at(node->rb_right), { model: RbTree::Empty });
    let t = fold(rb_at(node), {
        model: RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)
    }, { left: l, right: r });
    simp();
}
```

```expect
pass
```
