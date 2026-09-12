# rbtree link helpers over a modeled `rb_at(p, parent)`

`rb_at(p, parent)` folds one `rb_node` subtree into an `RbTree` model that
carries the node's own address, its color, and both submodels. The parent
pointer is a resource *parameter*, so the node's own arm owns
`p->__rb_parent_color` and states what that word holds: the parent's address
with the color in bit 0. Parent/child consistency is therefore a body fact —
the children are `rb_at(p->rb_left, p)` and `rb_at(p->rb_right, p)` — and no
separate witness is needed.

The tagged word is stated as two facts rather than the single
`p->__rb_parent_color == address(parent) + color_bit(color)`. Their conjunction
says exactly that, but the split form keeps the tag structurally below 4, which
is what the kernel's tagged-pointer step needs to clear the tag bits and
recover the parent's provenance; `color_bit(color)` is opaque until it is
unfolded at a concrete color, so the single fact leaves the tag unbounded and
`rb_parent`'s `& ~3` cannot be justified. `color_bit_is_a_bit` records that the
two forms agree on a range: a color bit is 0 or 1.

`rb_set_black` and `rb_red_parent` are only correct on a red node — one adds
`RB_BLACK` to the word, the other casts the whole word — so both are contracted
under `rb_color_bit(t.model) == 0`, which is the model saying the same thing.

The C is the unchanged Linux helper set: `rb_parent`, `rb_color`,
`rb_set_parent`, `rb_set_parent_color`, `rb_set_black`, `rb_red_parent`, and
`rb_link_node`, with the header of `mdtests/rb_parent_family.md` extended by
the remaining ones. Each contracted caller is a thin wrapper, so the helpers
themselves are never edited; the extra `old_parent` parameter on a wrapper
names the resource argument the helper is about to change.

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

struct rb_node *node_parent(struct rb_node *node, struct rb_node *parent) {
    return rb_parent(node);
}

unsigned long node_color(struct rb_node *node, struct rb_node *parent) {
    return rb_color(node);
}

void set_parent(struct rb_node *node, struct rb_node *old_parent, struct rb_node *parent) {
    rb_set_parent(node, parent);
}

void set_parent_black(struct rb_node *node, struct rb_node *old_parent, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_BLACK);
}

void set_parent_red(struct rb_node *node, struct rb_node *old_parent, struct rb_node *parent) {
    rb_set_parent_color(node, parent, RB_RED);
}

void set_black(struct rb_node *node, struct rb_node *parent) {
    rb_set_black(node);
}

struct rb_node *red_parent_of(struct rb_node *node, struct rb_node *parent) {
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
    Node(struct rb_node*, Color, RbTree, RbTree),
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
        RbTree::Node(identity, color, left, right) => color_bit(color),
    }
}

function rb_with_color(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, old_color, left, right) =>
            RbTree::Node(identity, color, left, right),
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

struct rb_node* node_parent(struct rb_node* node, struct rb_node* parent) {
    owns t: rb_at(node, parent);
    requires t.model != RbTree::Empty;
    ensures result == parent;
    ensures t.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            execute();
            let t = fold(rb_at(node, parent), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}

unsigned long node_color(struct rb_node* node, struct rb_node* parent) {
    owns t: rb_at(node, parent);
    requires t.model != RbTree::Empty;
    ensures result == rb_color_bit(old(t.model));
    ensures t.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_color_bit(RbTree::Node(identity, color, left_model, right_model)));
                assumption();
            }
            execute();
            let t = fold(rb_at(node, parent), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}

void set_parent(struct rb_node* node, struct rb_node* old_parent, struct rb_node* parent) {
    consumes t: rb_at(node, old_parent);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node, parent);
    ensures u.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            execute();
            let u = fold(rb_at(node, parent), { model: old(t.model) }, { left: l, right: r });
            simp();
        },
    }
}

void set_parent_black(struct rb_node* node, struct rb_node* old_parent, struct rb_node* parent) {
    consumes t: rb_at(node, old_parent);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node, parent);
    ensures u.model == rb_with_color(old(t.model), Color::Black);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have color_bit(Color::Black) == 1 by {
                unfold(color_bit(Color::Black));
                normalize();
            }
            execute();
            let u = fold(rb_at(node, parent), {
                model: RbTree::Node(identity, Color::Black, left_model, right_model)
            }, { left: l, right: r });
            simp();
        },
    }
}

void set_parent_red(struct rb_node* node, struct rb_node* old_parent, struct rb_node* parent) {
    consumes t: rb_at(node, old_parent);
    requires t.model != RbTree::Empty;
    requires aligned(parent, 8);
    produces u: rb_at(node, parent);
    ensures u.model == rb_with_color(old(t.model), Color::Red);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have color_bit(Color::Red) == 0 by {
                unfold(color_bit(Color::Red));
                normalize();
            }
            execute();
            let u = fold(rb_at(node, parent), {
                model: RbTree::Node(identity, Color::Red, left_model, right_model)
            }, { left: l, right: r });
            have u.model == rb_with_color(old(t.model), Color::Red) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_with_color(RbTree::Node(identity, color, left_model, right_model),
                    Color::Red));
                normalize();
            }
            simp();
        },
    }
}

void set_black(struct rb_node* node, struct rb_node* parent) {
    consumes t: rb_at(node, parent);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    produces u: rb_at(node, parent);
    ensures u.model == rb_with_color(old(t.model), Color::Black);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_color_bit(RbTree::Node(identity, color, left_model, right_model)));
                assumption();
            }
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == rb_color_bit(old(t.model)));
                simp();
            }
            have node->__rb_parent_color == address(parent) by {
                rewrite(node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0);
                normalize();
            }
            have color_bit(Color::Black) == 1 by {
                unfold(color_bit(Color::Black));
                normalize();
            }
            execute();
            let u = fold(rb_at(node, parent), {
                model: RbTree::Node(identity, Color::Black, left_model, right_model)
            }, { left: l, right: r });
            have u.model == rb_with_color(old(t.model), Color::Black) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_with_color(RbTree::Node(identity, color, left_model, right_model),
                    Color::Black));
                normalize();
            }
            simp();
        },
    }
}

struct rb_node* red_parent_of(struct rb_node* node, struct rb_node* parent) {
    owns t: rb_at(node, parent);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    ensures result == parent;
    ensures t.model == old(t.model);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_color_bit(RbTree::Node(identity, color, left_model, right_model)));
                assumption();
            }
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == rb_color_bit(old(t.model)));
                simp();
            }
            have node->__rb_parent_color == address(parent) by {
                rewrite(node->__rb_parent_color == address(parent) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == 0);
                normalize();
            }
            execute();
            let t = fold(rb_at(node, parent), { model: old(t.model) }, { left: l, right: r });
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
    produces t: rb_at(node, parent);
    ensures t.model == RbTree::Node(node, Color::Red, RbTree::Empty, RbTree::Empty);
    ensures rb_link[0] == node;
} by {
    have color_bit(Color::Red) == 0 by {
        unfold(color_bit(Color::Red));
        normalize();
    }
    execute();
    let l = fold(rb_at(node->rb_left, node), { model: RbTree::Empty });
    let r = fold(rb_at(node->rb_right, node), { model: RbTree::Empty });
    let t = fold(rb_at(node, parent), {
        model: RbTree::Node(node, Color::Red, RbTree::Empty, RbTree::Empty)
    }, { left: l, right: r });
    simp();
}
```

```expect
pass
```
