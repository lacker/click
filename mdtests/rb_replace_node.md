# `rb_replace_node` substitutes one identity in the model

The unchanged Linux `rb_replace_node` splices `new` into `victim`'s place: it
copies the packed parent word and both links with a whole-struct assignment,
retargets each existing child's parent word at `new`, and points the parent —
or the root cell — at `new`. Its model effect is exactly the identity
substitution at the focused node: `RbTree::Node(victim, color, l, r)` becomes
`RbTree::Node(new, color, l, r)`, with both subtrees and the frame unchanged.
That is `rb_substitute`.

The frame is keyed by the focused child's parent, `ctx_at(child, parent,
root)`, per the D3 amendment in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md),
and the wrapper's extra `parent` parameter names that resource argument the way
`mdtests/rb_at_link_helpers.md`'s `old_parent` does. `rb_replace_node`
recomputes the same pointer into a local with `rb_parent(victim)`; the frame's
own arm is what proves the two agree, so `__rb_change_child` is decided before
it runs and writes exactly the cell the frame owns.

The victim here has no children. That is what lets both `if (victim->rb_left)`
guards be decided from the requirements, and what lets the two child instances
be refolded at the new parent for free: an `RbTree::Empty` arm owns nothing and
states only `p == 0`, and the refuted-arm rule turns `victim->rb_left == 0`
into the model fact that lets `unfold` select that arm with no proof `match` at
all. A victim with a child cannot be contracted here yet; the reason is the
note at the end of this file.

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

void replace_left_child(struct rb_node *victim, struct rb_node *new_node,
                        struct rb_node *parent, struct rb_node *grandparent,
                        struct rb_root *root) {
    rb_replace_node(victim, new_node, root);
}
```

```click
verifying "rb_replace_node.c";

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
    produces d: ctx_at(new_node, parent, root);
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
            let d = fold(ctx_at(new_node, parent, root), { model: old(c.model) }, {});
            have u.model == rb_substitute(old(t.model), new_node) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_substitute(
                    RbTree::Node(identity, color, left_model, right_model), new_node));
                normalize();
            }
            simp();
        },
    }
}

void replace_left_child(struct rb_node* victim, struct rb_node* new_node,
                        struct rb_node* parent, struct rb_node* grandparent,
                        struct rb_root* root) {
    consumes c: ctx_at(victim, parent, root);
    consumes t: rb_at(victim, parent);
    consumes new_node->__rb_parent_color;
    consumes new_node->rb_left;
    consumes new_node->rb_right;
    requires t.model != RbTree::Empty;
    requires c.model
        == Context::Left(grandparent, Color::Black, RbTree::Empty, Context::Top);
    requires victim->rb_left == 0;
    requires victim->rb_right == 0;
    requires new_node != 0;
    requires aligned(new_node, 8);
    produces d: ctx_at(new_node, parent, root);
    produces u: rb_at(new_node, parent);
    ensures d.model == old(c.model);
    ensures u.model == rb_substitute(old(t.model), new_node);
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, color, left_model, right_model) => {
            unfold(t) as { left: l, right: r };
            unfold(c) as { sibling: sib, up: above };
            unfold(l);
            unfold(r);
            execute();
            let l2 = fold(rb_at(new_node->rb_left, new_node), { model: left_model }, {});
            let r2 = fold(rb_at(new_node->rb_right, new_node), { model: right_model }, {});
            let u = fold(rb_at(new_node, parent), {
                model: RbTree::Node(new_node, color, left_model, right_model)
            }, { left: l2, right: r2 });
            let d = fold(ctx_at(new_node, parent, root), { model: old(c.model) },
                         { sibling: sib, up: above });
            have u.model == rb_substitute(old(t.model), new_node) by {
                rewrite(old(t.model) == RbTree::Node(identity, color, left_model, right_model));
                unfold(rb_substitute(
                    RbTree::Node(identity, color, left_model, right_model), new_node));
                normalize();
            }
            simp();
        },
    }
}
```

```expect
pass
```

## Why the victim has no children here

With a child present, `rb_set_parent(victim->rb_left, new)` rewrites that
child's packed word, and the child's instance has to be refolded as
`rb_at(victim->rb_left, new)`. That fold needs the arm fact
`(p->__rb_parent_color & 1) == color_bit(color)` for the rewritten word,
which instantiates to

```text
(((old & 1) | address(new)) & 1) == color_bit(color)
```

and the fold refuses with `fold requires the instance body facts for the
proposed fields`, because a fold discharges its body facts exactly rather
than proving them. `mdtests/rb_at_link_helpers.md`'s `set_parent` performs
the same rewrite and the same refold successfully, and the difference is
that there the retargeted node is a named C parameter. Here it is only
reachable as `victim->rb_left`, and a `have` over that chained place does
not lower (`the kernel lowering produced 3 paths, not one`). Naming the
child with an extra wrapper parameter makes the `have` lower but leaves it
unproved by `simp`, and discharging it through `color_bit_is_a_bit` fails
because a match-arm binding may not be a theorem argument inside a `have`.

A second limit shows up in the same place: four nested proof `match`
scrutinees — the subtree, both children, and the frame — are refused with
`the grouped contract proof driver declined the supplied tactic sequence`,
so even with the fold repaired the general case needs the frame pinned by a
requirement, as it is here.

## The traversal half of C4, and what blocks it

`rb_first`, `rb_last`, `rb_next` and `rb_prev` are not contracted here. Two
things stop them, both at the contract boundary rather than inside a proof.

First, their loops cannot be reached from a contracted wrapper. A `static
inline` helper is inlined into its caller as a single statement, so `step()`
executes the whole callee and `loop { ... }` reports `loop requires the
execution frontier to be at a loop; current frontier is statement(0)`. The four
functions therefore have to be contracted as top-level functions with their own
parameter lists.

Second, those parameter lists cannot name the pointers the resources need.
`rb_at(p, parent)` (D2) and `ctx_at(child, parent, root)` (D3) both take the
focused node's parent as an argument, and the Linux traversals keep no parent
local while they descend:

```text
struct rb_node *rb_first(const struct rb_root *root)
{
	struct rb_node	*n;

	n = root->rb_node;
	if (!n)
		return NULL;
	while (n->rb_left)
		n = n->rb_left;
	return n;
}
```

`n` is the only node name in scope, so neither the descent's loop binders nor
the exit clauses have a spelling for the focused node's parent. The intended
contract, ready for the package that supplies one, is:

```text
struct rb_node* rb_first(const struct rb_root* root) {
    consumes w: rb_tree_at(root);
    requires w.model != RbTree::Empty;
    produces ctx: ctx_at(result, <parent of result>, root);
    produces sub: rb_at(result, <parent of result>);
    ensures plug(ctx.model, sub.model) == old(w.model);
    ensures rb_left(sub.model) == RbTree::Empty;
    ensures exists (rest: List<struct rb_node*>) {
        rb_inorder(old(w.model)) == List<struct rb_node*>::Cons(result, rest)
    };
} by {
    step();
    loop {
        owns ctx: ctx_at(n, <parent of n>, root);
        owns t: rb_at(n, <parent of n>);
        decreases t;
        invariant t.model != RbTree::Empty;
        invariant plug(ctx.model, t.model) == old(w.model);
    }
    step();
    simp();
}
```

with `rb_last` the mirror through `rb_right` and the last element of
`rb_inorder`. A pure function cannot return a pointer (gap 8), `exists` cannot
bind a `produces` argument, and a wrapper parameter standing for the result's
parent is unconstrained at entry, so no proof can establish the clause for it.
A13 met the same shape on the scaffold and keyed `ctx_at` by the child alone;
that works there because the scaffold's `tree_at(p)` takes no parent, and
`rb_at(p, parent)` does.

`rb_next(const struct rb_node *node)` is harder still: neither `parent` nor
`root` is a parameter, so even its entry frame cannot be written. Its intended
contract, over the frame its caller already holds, is:

```text
struct rb_node* rb_next(const struct rb_node* node) {
    consumes c: ctx_at(node, <parent of node>, <the root>);
    consumes t: rb_at(node, <parent of node>);
    requires t.model != RbTree::Empty;
    produces ctx: ctx_at(result, <parent of result>, <the root>);
    produces sub: rb_at(result, <parent of result>);
    ensures plug(ctx.model, sub.model) == plug(old(c.model), old(t.model));
    ensures exists (before: List<struct rb_node*>, after: List<struct rb_node*>) {
        rb_inorder(plug(old(c.model), old(t.model)))
            == list_append(before,
                   List<struct rb_node*>::Cons(node,
                       List<struct rb_node*>::Cons(result, after)))
    };
}
```

The descending case — `node->rb_right` non-empty, then leftmost — is the
`rb_first` loop above and blocks the same way. The ascending case,
`while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;`,
does keep a `parent` local, so its binders are spellable; it needs package A14
(gap 29) for the produced binder at the loop exit, and it was not attempted
because its entry frame cannot be named either.
