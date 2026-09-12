# `rb_replace_node` substitutes one identity in the model

The unchanged Linux `rb_replace_node` splices `new` into `victim`'s place: it
copies the packed parent word and both links with a whole-struct assignment,
retargets each existing child's parent word at `new`, and points the parent —
or the root cell — at `new`. Its model effect is exactly the identity
substitution at the focused node: `RbTree::Node(victim, parent, color, l, r)`
becomes `RbTree::Node(new, parent, color, l, r)`, with the parent payload, both
subtrees and the frame unchanged. That is `rb_substitute`.

The model is keyed by node with the parent in the payload (gap 35 in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md)):
`rb_at(p)` and `ctx_at(child, root)`. The wrapper pins the victim's model with
the C parameter `parent` in the payload slot, which is how `rb_parent(victim)`
and the frame are related here: with the parent inside the model rather than a
resource argument, nothing else ties the pointer the helper recomputes to the
node the frame owns.

The victim here has no children. That is what lets both `if (victim->rb_left)`
guards be decided from the requirements, and what lets the two child instances
be refolded at the new parent for free: an `RbTree::Empty` arm owns nothing and
states only `p == 0`.

Only the root frame is contracted. The left-child frame is blocked by the
re-keying, not by the helper: see the note at the end of this file.

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

```c filename=rb_replace_node.c
#include "rbtree.h"

void replace_root_node(struct rb_node *victim, struct rb_node *new_node,
                       struct rb_node *parent, struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}
```

```click
verifying "rb_replace_node.c";

spec enum Color { Red, Black }

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
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
        RbTree::Node(identity, parent, color, left, right) =>
            RbTree::Node(replacement, parent, color, left, right),
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
        },
    }
}

void replace_root_node(struct rb_node* victim, struct rb_node* new_node,
                       struct rb_node* parent, struct rb_root* root) {
    consumes c: ctx_at(victim, root);
    consumes t: rb_at(victim);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires parent == 0;
    requires c.model == Context::Top;
    requires t.model
        == RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty);
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(new_node, root);
    produces u: rb_at(new_node);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    unfold(t) as { left: l, right: r };
    unfold(c);
    unfold(l);
    unfold(r);
    have color_bit(Color::Black) == 1 by {
        unfold(color_bit(Color::Black));
        normalize();
    }
    execute();
    let l2 = fold(rb_at(new_node->rb_left), { model: RbTree::Empty }, {});
    let r2 = fold(rb_at(new_node->rb_right), { model: RbTree::Empty }, {});
    let u = fold(rb_at(new_node), {
        model: RbTree::Node(new_node, parent, Color::Black, RbTree::Empty, RbTree::Empty)
    }, { left: l2, right: r2 });
    let d = fold(ctx_at(new_node, root), { model: old(c.model) }, {});
    have u.model == rb_substitute(old(t.model), new_node) by {
        rewrite(old(t.model)
            == RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty));
        unfold(rb_substitute(
            RbTree::Node(victim, parent, Color::Black, RbTree::Empty, RbTree::Empty),
            new_node));
        normalize();
    }
    simp();
}

```

```expect
pass
```

## Why the victim has no children here

With a child present, `rb_set_parent(victim->rb_left, new)` rewrites that
child's packed word, and the child's instance has to be refolded as
`rb_at(victim->rb_left)` with `new` as its parent payload. That fold needs the
arm fact `(p->__rb_parent_color & 1) == color_bit(color)` for the rewritten
word, which instantiates to

```text
(((old & 1) | address(new)) & 1) == color_bit(color)
```

and the fold refuses with `fold requires the instance body facts for the
proposed fields`, because a fold discharges its body facts exactly rather than
proving them. `mdtests/rb_at_link_helpers.md`'s `set_parent` performs the same
rewrite and the same refold successfully, and the difference is that there the
retargeted node is a named C parameter. Here it is only reachable as
`victim->rb_left`, and a `have` over that chained place does not lower (`the
kernel lowering produced 3 paths, not one`). This is package A17's third item.

## Why only the root frame

`replace_left_child` is not here, and the reason is the node-keyed frame rather
than the helper. `ctx_at(child, root)`'s `Left` arm owns `identity`'s cells
through its own payload, and `unfold` binds that payload to a fresh value that
is equal to the wrapper's `parent` only through the model equation the
requirement states. The inlined `__rb_change_child` then reads `parent->rb_left`
while the frame owns `identity->rb_left`, so its inner test is undecided and
`execute()` refuses with `step() requires exactly one statement successor …,
got 2`. Pinning the frame with `requires c.model == Context::Left(parent,
grandparent, Color::Black, RbTree::Empty, Context::Top)` does not help, and
neither does adding the victim's word as a requirement: what is missing is a
bridge from a C pointer to a frame payload that survives `unfold`.

The bridge itself exists and is worth recording. An equational requirement
`t.model == rb_reparent(t.model, parent)` and `extract` of a field equality of
a same-constructor equality yield `payload == parent` inside a proof `match`
arm; what is not available is that equality applying to the *unfolded* frame's
owned cells. The old `ctx_at(child, parent, root)` spelling had it for free and
cannot be used for `rb_first`/`rb_next` (gap 35), so this is the cost of the
re-key and the next thing a frame-owning proof needs.
