# `rb_first` and `rb_last` on the node-keyed model

The unchanged Linux `rb_first` and `rb_last` descend from the root to the
leftmost or rightmost node. They are the reason the rbtree model is keyed by
node with the parent in the payload (gap 35 in
[`issues/rbtree-example.md`](../issues/rbtree-example.md)):
`n` is the only node name in scope, so a `rb_at(p, parent)` binder or a
`produces ctx: ctx_at(result, parent, root)` clause would have nothing to put
in the parent position. With `rb_at(p)` and `ctx_at(child, root)` every clause
these functions need names `n` or `result` alone.

The contract is the rbtree form of the scaffold's `tree_leftmost`: the frame and
the focused subtree at the result rebuild the entry tree through `plug`, and the
result has no left child. The empty tree is the same contract, not a second one:
`rb_first` returns null, `Context::Top` still owns `root->rb_node` and states it
points at the result, `rb_at(0)` is `RbTree::Empty`, and `plug(Top, Empty)` is
`Empty`.

`rb_at`'s `Node` arm carries parent/child consistency as a body fact,
`rb_parent_is(left_model, p) == 1` and its mirror: each submodel's own parent
payload is this node. That is D2's intent, and it is dischargeable at `fold`
only because a pure function that reads no memory now anchors its pointer
arguments to one canonical snapshot rather than the ambient one (package A20;
see [`docs/concepts/resources.md`](../docs/concepts/resources.md) and
[`rb_at_link_helpers.md`](rb_at_link_helpers.md)). The descent folds the frame
and the focused subtree on every iteration, so both facts are re-established
each time round the loop.

`rb_first` also states its result's *position*: on a non-empty tree the result
is the head of `rb_inorder`. `exists` cannot quantify a `List`-typed variable,
so the `Cons(result, rest)` form is not spellable; `rb_list_starts_with` says
the same thing without a witness. Proving it needs the descent's own extra
invariant — every frame the loop pushes is a `Left` frame, `ctx_all_left` — and
two pure theorems: a list that starts with a value still starts with it after an
append, and plugging an all-left context preserves the head of `rb_inorder`.

`rb_last` states the mirrored position guarantee: on a non-empty entry tree its
result is the final element of `rb_inorder`, expressed by
`rb_list_ends_with`. Three small list theorems establish that `ends_with`
implies non-emptiness, that adding a head preserves the last element of a
non-empty tail, and that appending a list on the left preserves the last element
of its right operand. `rb_inorder_last_at_rightmost` applies those facts to the
focused node with an empty right subtree. The loop's `ctx_all_right` invariant
records that every pushed frame is a `Right` frame, and `plug_keeps_last` lifts
the focused result through those frames to the entry tree. The empty-tree path
still returns null with the same `Top` context, empty subtree, and structural
guarantees; the positional postcondition is guarded by entry non-emptiness.

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
#endif
```

```c filename=rb_first_last.c
#include "rbtree.h"

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

struct rb_node *rb_last(const struct rb_root *root)
{
	struct rb_node	*n;

	n = root->rb_node;
	if (!n)
		return NULL;
	while (n->rb_right)
		n = n->rb_right;
	return n;
}
```

```click
verifying "rb_first_last.c";

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

function rb_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) => left,
    }
}

function rb_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) => right,
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
        },
    }
}

function rb_inorder(tree: RbTree) -> List<struct rb_node*>
    decreases tree
{
    match tree {
        RbTree::Empty => List<struct rb_node*>::Nil,
        RbTree::Node(identity, parent, color, left, right) =>
            list_append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))),
    }
}

function rb_list_starts_with(xs: List<struct rb_node*>, value: struct rb_node*) -> int32 {
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) => if value == head { 1 } else { 0 },
    }
}

function rb_list_ends_with(xs: List<struct rb_node*>, value: struct rb_node*) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) =>
            if tail == List<struct rb_node*>::Nil {
                if value == head { 1 } else { 0 }
            } else {
                rb_list_ends_with(tail, value)
            },
    }
}

function rb_identity_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(identity, parent, color, left, right) =>
            if p == identity { 1 } else { 0 },
    }
}

function ctx_all_left(ctx: Context) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => 1,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            ctx_all_left(up_model),
        Context::Right(identity, grandparent, color, sibling_model, up_model) => 0,
    }
}

function ctx_all_right(ctx: Context) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => 1,
        Context::Left(identity, grandparent, color, sibling_model, up_model) => 0,
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            ctx_all_right(up_model),
    }
}

theorem list_starts_with_append(xs: List<struct rb_node*>, ys: List<struct rb_node*>,
                                value: struct rb_node*) {
    requires rb_list_starts_with(xs, value) != 0;
    ensures rb_list_starts_with(list_append(xs, ys), value) == 1 by {
        induct(xs) as ih {
            List::Nil => {
                have rb_list_starts_with(List<struct rb_node*>::Nil, value) == 0 by {
                    unfold(rb_list_starts_with(List<struct rb_node*>::Nil, value));
                    normalize();
                }
                contradiction(rb_list_starts_with(List<struct rb_node*>::Nil, value) == 0);
            }
            List::Cons(head, tail) => {
                have rb_list_starts_with(List<struct rb_node*>::Cons(head, tail), value)
                    == if value == head { 1 } else { 0 } by {
                    unfold(rb_list_starts_with(List<struct rb_node*>::Cons(head, tail), value));
                    normalize();
                }
                if value == head {
                    have list_append(List<struct rb_node*>::Cons(head, tail), ys)
                        == List<struct rb_node*>::Cons(head, list_append(tail, ys)) by {
                        unfold(list_append(List<struct rb_node*>::Cons(head, tail), ys));
                        normalize();
                    }
                    have rb_list_starts_with(
                            List<struct rb_node*>::Cons(head, list_append(tail, ys)),
                            value) == 1 by {
                        unfold(rb_list_starts_with(
                            List<struct rb_node*>::Cons(head, list_append(tail, ys)), value));
                        normalize() using { value == head; }
                    }
                    rewrite(list_append(List<struct rb_node*>::Cons(head, tail), ys)
                        == List<struct rb_node*>::Cons(head, list_append(tail, ys)));
                    assumption();
                } else {
                    have rb_list_starts_with(List<struct rb_node*>::Cons(head, tail),
                                             value) == 0 by {
                        rewrite(rb_list_starts_with(List<struct rb_node*>::Cons(head, tail), value)
                            == if value == head { 1 } else { 0 });
                        normalize() using { not(value == head); }
                    }
                    contradiction(rb_list_starts_with(
                        List<struct rb_node*>::Cons(head, tail), value) == 0);
                }
            }
        }
    }
}

theorem list_ends_with_is_nonempty(xs: List<struct rb_node*>, value: struct rb_node*) {
    requires rb_list_ends_with(xs, value) != 0;
    ensures xs != List<struct rb_node*>::Nil by {
        induct(xs) as ih {
            List::Nil => {
                have rb_list_ends_with(List<struct rb_node*>::Nil, value) == 0 by {
                    unfold(rb_list_ends_with(List<struct rb_node*>::Nil, value));
                    normalize();
                }
                contradiction(rb_list_ends_with(List<struct rb_node*>::Nil, value) == 0);
            }
            List::Cons(head, tail) => {
                normalize();
            }
        }
    }
}

theorem list_ends_with_cons_nonempty(head: struct rb_node*,
                                     tail: List<struct rb_node*>,
                                     value: struct rb_node*) {
    requires tail != List<struct rb_node*>::Nil;
    ensures rb_list_ends_with(List<struct rb_node*>::Cons(head, tail), value)
        == rb_list_ends_with(tail, value) by {
        unfold(rb_list_ends_with(List<struct rb_node*>::Cons(head, tail), value));
        normalize() using { tail != List<struct rb_node*>::Nil; }
    }
}

theorem list_ends_with_append(xs: List<struct rb_node*>, ys: List<struct rb_node*>,
                              value: struct rb_node*) {
    requires rb_list_ends_with(ys, value) == 1;
    ensures rb_list_ends_with(list_append(xs, ys), value) == 1 by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<struct rb_node*>::Nil, ys));
                assumption();
            }
            List::Cons(head, tail) => {
                apply(ih(tail, ys, value));
                have rb_list_ends_with(list_append(tail, ys), value) != 0 by {
                    rewrite(rb_list_ends_with(list_append(tail, ys), value) == 1);
                    normalize();
                }
                apply(list_ends_with_is_nonempty(list_append(tail, ys), value));
                apply(list_ends_with_cons_nonempty(head, list_append(tail, ys), value));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<struct rb_node*>::Cons(head, tail), ys)
                    == List<struct rb_node*>::Cons(head, list_append(tail, ys)));
                rewrite(rb_list_ends_with(
                        List<struct rb_node*>::Cons(head, list_append(tail, ys)), value)
                    == rb_list_ends_with(list_append(tail, ys), value));
                assumption();
            }
        }
    }
}

theorem rb_inorder_first_at_leftmost(tree: RbTree, node: struct rb_node*) {
    requires rb_left(tree) == RbTree::Empty;
    requires rb_identity_is(tree, node) == 1;
    ensures rb_list_starts_with(rb_inorder(tree), node) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                have rb_identity_is(RbTree::Empty, node) != 0 by {
                    rewrite(rb_identity_is(RbTree::Empty, node) == 1);
                    normalize();
                }
                have rb_identity_is(RbTree::Empty, node) == 0 by {
                    unfold(rb_identity_is(RbTree::Empty, node));
                    normalize();
                }
                contradiction(rb_identity_is(RbTree::Empty, node) == 0);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                have rb_left(RbTree::Node(identity, parent, color, left, right)) == left by {
                    unfold(rb_left(RbTree::Node(identity, parent, color, left, right)));
                    normalize();
                }
                have left == RbTree::Empty by {
                    rewrite(left == rb_left(RbTree::Node(identity, parent, color, left, right)));
                    assumption();
                }

                have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                    == if node == identity { 1 } else { 0 } by {
                    unfold(rb_identity_is(
                        RbTree::Node(identity, parent, color, left, right), node));
                    normalize();
                }
                if node == identity {
                    have rb_inorder(RbTree::Node(identity, parent, color, RbTree::Empty, right))
                        == list_append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))) by {
                        unfold(rb_inorder(
                            RbTree::Node(identity, parent, color, RbTree::Empty, right)));
                        unfold(rb_inorder(RbTree::Empty));
                        normalize();
                    }
                    have list_append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)))
                        == List<struct rb_node*>::Cons(identity, rb_inorder(right)) by {
                        unfold(list_append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))));
                        normalize();
                    }
                    have rb_list_starts_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)),
                            node) == 1 by {
                        unfold(rb_list_starts_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)), node));
                        normalize() using { node == identity; }
                    }
                    rewrite(left == RbTree::Empty);
                    rewrite(rb_inorder(RbTree::Node(identity, parent, color, RbTree::Empty, right))
                        == list_append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))));
                    rewrite(list_append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)))
                        == List<struct rb_node*>::Cons(identity, rb_inorder(right)));
                    assumption();
                } else {
                    have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                        == 0 by {
                        rewrite(rb_identity_is(
                                RbTree::Node(identity, parent, color, left, right), node)
                            == if node == identity { 1 } else { 0 });
                        normalize() using { not(node == identity); }
                    }
                    have rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node) != 0 by {
                        rewrite(rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node) == 1);
                        normalize();
                    }
                    contradiction(rb_identity_is(
                        RbTree::Node(identity, parent, color, left, right), node) == 0);
                }
            }
        }
    }
}

theorem rb_inorder_last_at_rightmost(tree: RbTree, node: struct rb_node*) {
    requires rb_right(tree) == RbTree::Empty;
    requires rb_identity_is(tree, node) == 1;
    ensures rb_list_ends_with(rb_inorder(tree), node) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                have rb_identity_is(RbTree::Empty, node) != 0 by {
                    rewrite(rb_identity_is(RbTree::Empty, node) == 1);
                    normalize();
                }
                have rb_identity_is(RbTree::Empty, node) == 0 by {
                    unfold(rb_identity_is(RbTree::Empty, node));
                    normalize();
                }
                contradiction(rb_identity_is(RbTree::Empty, node) == 0);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                have rb_right(RbTree::Node(identity, parent, color, left, right)) == right by {
                    unfold(rb_right(RbTree::Node(identity, parent, color, left, right)));
                    normalize();
                }
                have right == RbTree::Empty by {
                    rewrite(right == rb_right(
                        RbTree::Node(identity, parent, color, left, right)));
                    assumption();
                }

                have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                    == if node == identity { 1 } else { 0 } by {
                    unfold(rb_identity_is(
                        RbTree::Node(identity, parent, color, left, right), node));
                    normalize();
                }
                if node == identity {
                    have rb_inorder(RbTree::Node(identity, parent, color, left, RbTree::Empty))
                        == list_append(rb_inorder(left),
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil)) by {
                        unfold(rb_inorder(
                            RbTree::Node(identity, parent, color, left, RbTree::Empty)));
                        unfold(rb_inorder(RbTree::Empty));
                        normalize();
                    }
                    have rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil), node) == 1 by {
                        unfold(rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil), node));
                        normalize() using { node == identity; }
                    }
                    have rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil), node) != 0 by {
                        rewrite(rb_list_ends_with(
                                List<struct rb_node*>::Cons(identity,
                                    List<struct rb_node*>::Nil), node) == 1);
                        normalize();
                    }
                    apply(list_ends_with_append(rb_inorder(left),
                        List<struct rb_node*>::Cons(identity,
                            List<struct rb_node*>::Nil), node));
                    rewrite(right == RbTree::Empty);
                    rewrite(rb_inorder(
                            RbTree::Node(identity, parent, color, left, RbTree::Empty))
                        == list_append(rb_inorder(left),
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil)));
                    assumption();
                } else {
                    have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                        == 0 by {
                        rewrite(rb_identity_is(
                                RbTree::Node(identity, parent, color, left, right), node)
                            == if node == identity { 1 } else { 0 });
                        normalize() using { not(node == identity); }
                    }
                    have rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node) != 0 by {
                        rewrite(rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node) == 1);
                        normalize();
                    }
                    contradiction(rb_identity_is(
                        RbTree::Node(identity, parent, color, left, right), node) == 0);
                }
            }
        }
    }
}

theorem plug_keeps_first(ctx: Context, sub: RbTree, node: struct rb_node*) {
    requires ctx_all_left(ctx) == 1;
    requires rb_list_starts_with(rb_inorder(sub), node) == 1;
    ensures rb_list_starts_with(rb_inorder(plug(ctx, sub)), node) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_left(Context::Left(identity, grandparent, color, sibling_model,
                                                up_model)) == ctx_all_left(up_model) by {
                    unfold(ctx_all_left(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model)));
                    normalize();
                }
                have ctx_all_left(up_model) == 1 by {
                    rewrite(ctx_all_left(up_model)
                        == ctx_all_left(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model)));
                    assumption();
                }
                have rb_inorder(RbTree::Node(identity, grandparent, color, sub, sibling_model))
                    == list_append(rb_inorder(sub),
                        List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sub, sibling_model)));
                    normalize();
                }
                have rb_list_starts_with(rb_inorder(sub), node) != 0 by {
                    rewrite(rb_list_starts_with(rb_inorder(sub), node) == 1);
                    normalize();
                }
                apply(list_starts_with_append(rb_inorder(sub),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model)), node));
                have rb_list_starts_with(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sub,
                                                sibling_model)), node) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sub, sibling_model))
                        == list_append(rb_inorder(sub),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))));
                    assumption();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sub, sibling_model), node));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                            sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_left(Context::Right(identity, grandparent, color, sibling_model,
                                                 up_model)) != 0 by {
                    rewrite(ctx_all_left(Context::Right(identity, grandparent, color,
                                                        sibling_model, up_model)) == 1);
                    normalize();
                }
                have ctx_all_left(Context::Right(identity, grandparent, color, sibling_model,
                                                 up_model)) == 0 by {
                    unfold(ctx_all_left(Context::Right(identity, grandparent, color,
                                                       sibling_model, up_model)));
                    normalize();
                }
                contradiction(ctx_all_left(Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model)) == 0);
            }
        }
    }
}

theorem plug_keeps_last(ctx: Context, sub: RbTree, node: struct rb_node*) {
    requires ctx_all_right(ctx) == 1;
    requires rb_list_ends_with(rb_inorder(sub), node) == 1;
    ensures rb_list_ends_with(rb_inorder(plug(ctx, sub)), node) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_right(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model)) != 0 by {
                    rewrite(ctx_all_right(Context::Left(identity, grandparent, color,
                                                        sibling_model, up_model)) == 1);
                    normalize();
                }
                have ctx_all_right(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model)) == 0 by {
                    unfold(ctx_all_right(Context::Left(identity, grandparent, color,
                                                       sibling_model, up_model)));
                    normalize();
                }
                contradiction(ctx_all_right(Context::Left(identity, grandparent, color,
                                                          sibling_model, up_model)) == 0);
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_right(Context::Right(identity, grandparent, color, sibling_model,
                                                  up_model)) == ctx_all_right(up_model) by {
                    unfold(ctx_all_right(Context::Right(identity, grandparent, color,
                                                        sibling_model, up_model)));
                    normalize();
                }
                have ctx_all_right(up_model) == 1 by {
                    rewrite(ctx_all_right(up_model)
                        == ctx_all_right(Context::Right(identity, grandparent, color,
                                                        sibling_model, up_model)));
                    assumption();
                }
                have rb_list_ends_with(rb_inorder(sub), node) != 0 by {
                    rewrite(rb_list_ends_with(rb_inorder(sub), node) == 1);
                    normalize();
                }
                apply(list_ends_with_is_nonempty(rb_inorder(sub), node));
                apply(list_ends_with_cons_nonempty(identity, rb_inorder(sub), node));
                have rb_list_ends_with(
                        List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node) == 1 by {
                    rewrite(rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node)
                        == rb_list_ends_with(rb_inorder(sub), node));
                    assumption();
                }
                have rb_list_ends_with(
                        List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node) != 0 by {
                    rewrite(rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node) == 1);
                    normalize();
                }
                apply(list_ends_with_append(rb_inorder(sibling_model),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node));
                have rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, sub))
                    == list_append(rb_inorder(sibling_model),
                        List<struct rb_node*>::Cons(identity, rb_inorder(sub))) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sibling_model, sub)));
                    normalize();
                }
                have rb_list_ends_with(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, sub)),
                        node) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sibling_model, sub))
                        == list_append(rb_inorder(sibling_model),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub))));
                    assumption();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sibling_model, sub), node));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                            sub));
                assumption();
            }
        }
    }
}

struct rb_node* rb_first(const struct rb_root* root) {
    consumes root->rb_node;
    consumes t: rb_at(root->rb_node);
    requires root != 0;
    produces ctx: ctx_at(result, root);
    produces sub: rb_at(result);
    ensures plug(ctx.model, sub.model) == old(t.model);
    ensures rb_left(sub.model) == RbTree::Empty;
    ensures old(t.model) != RbTree::Empty implies
        rb_list_starts_with(rb_inorder(old(t.model)), result) == 1;
} by {
    step();
    step();
    match t.model {
        RbTree::Empty => {
            unfold(t);
            let sub = fold(rb_at(n), { model: RbTree::Empty });
            let ctx = fold(ctx_at(n, root), { model: Context::Top });
            have rb_left(sub.model) == RbTree::Empty by {
                rewrite(sub.model == RbTree::Empty);
                unfold(rb_left(RbTree::Empty));
                normalize();
            }
            have plug(ctx.model, sub.model) == old(t.model) by {
                rewrite(ctx.model == Context::Top);
                unfold(plug(Context::Top, sub.model));
                rewrite(sub.model == RbTree::Empty);
                simp();
            }
            execute();
            simp();
        },
        RbTree::Node(entry_identity, entry_parent, entry_color,
                     entry_left, entry_right) => {
            let { left: entry_l, right: entry_r } = unfold(t);
            have root->rb_node != 0 by { simp(); }
            let t = fold(rb_at(n), { model: old(t.model) },
                         { left: entry_l, right: entry_r });
            let ctx = fold(ctx_at(n, root), { model: Context::Top });
            have ctx_all_left(ctx.model) == 1 by {
                rewrite(ctx.model == Context::Top);
                unfold(ctx_all_left(Context::Top));
                normalize();
            }
            have plug(ctx.model, t.model) == old(t.model) by {
                rewrite(ctx.model == Context::Top);
                unfold(plug(Context::Top, t.model));
                normalize();
            }
            have t.model != RbTree::Empty by { simp(); }
            have n != 0 by { simp(); }
            branch {
                then { contradiction(n == 0); }
                else {}
            }
            loop {
                owns ctx: ctx_at(n, root);
                owns t: rb_at(n);
                decreases t;
                invariant t.model != RbTree::Empty;
                invariant ctx_all_left(ctx.model) == 1;
                invariant plug(ctx.model, t.model) == old(t.model);

                initialize by simp;
                preserve by {
                    match t.model {
                        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                        RbTree::Node(identity, parent, color, left_model, right_model) => {
                            have plug(Context::Left(identity, parent, color, right_model,
                                                  ctx.model), left_model)
                                == old(t.model) by {
                                unfold(plug(Context::Left(identity, parent, color,
                                                        right_model, ctx.model), left_model));
                                rewrite(RbTree::Node(identity, parent, color, left_model,
                                                     right_model) == t.model);
                                assumption();
                            }
                            let { left: l, right: rt } = unfold(t);
                            have plug(Context::Left(n, parent, color, right_model, ctx.model),
                                      left_model)
                                == old(t.model) by {
                                rewrite(n == identity);
                                assumption();
                            }
                            have ctx_all_left(Context::Left(n, parent, color, right_model,
                                                            ctx.model)) == 1 by {
                                unfold(ctx_all_left(Context::Left(n, parent, color, right_model,
                                                                  ctx.model)));
                                assumption();
                            }
                            let frame = fold(ctx_at(n->rb_left, root), {
                                model: Context::Left(n, parent, color, right_model, ctx.model)
                            }, { sibling: rt, up: ctx });
                            step();
                            close_invariants();
                        }
                    }
                }
            }
            match t.model {
                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                RbTree::Node(identity, parent, color, left_model, right_model) => {
                    have plug(ctx.model,
                              RbTree::Node(identity, parent, color, left_model, right_model))
                        == old(t.model) by {
                        rewrite(RbTree::Node(identity, parent, color, left_model, right_model)
                            == t.model);
                        assumption();
                    }
                    let { left: l, right: rt } = unfold(t);
                    have rb_left(RbTree::Node(identity, parent, color, left_model, right_model))
                        == left_model by {
                        unfold(rb_left(RbTree::Node(identity, parent, color, left_model,
                                                 right_model)));
                        normalize();
                    }
                    let sub = fold(rb_at(n), {
                        model: RbTree::Node(identity, parent, color, left_model, right_model)
                    }, { left: l, right: rt });
                    have rb_left(sub.model) == RbTree::Empty by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        rewrite(rb_left(RbTree::Node(identity, parent, color, left_model,
                                                  right_model))
                            == left_model);
                        assumption();
                    }
                    have plug(ctx.model, sub.model) == old(t.model) by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        assumption();
                    }
                    have rb_identity_is(sub.model, identity) == 1 by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        unfold(rb_identity_is(
                            RbTree::Node(identity, parent, color, left_model, right_model),
                            identity));
                        normalize();
                    }
                    have rb_identity_is(sub.model, n) == 1 by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        unfold(rb_identity_is(
                            RbTree::Node(identity, parent, color, left_model, right_model), n));
                        normalize() using { n == identity; }
                    }
                    have rb_list_starts_with(rb_inorder(sub.model), n) == 1 by {
                        apply(rb_inorder_first_at_leftmost(sub.model, n));
                        assumption();
                    }
                    have rb_list_starts_with(rb_inorder(plug(ctx.model, sub.model)), n) == 1 by {
                        apply(plug_keeps_first(ctx.model, sub.model, n));
                        assumption();
                    }
                    have old(t.model) == plug(ctx.model, sub.model) by { simp(); }
                    have rb_list_starts_with(rb_inorder(old(t.model)), n) == 1 by {
                        rewrite(old(t.model) == plug(ctx.model, sub.model));
                        assumption();
                    }
                    step();
                    simp();
                },
            }
        },
    }
}

struct rb_node* rb_last(const struct rb_root* root) {
    consumes root->rb_node;
    consumes t: rb_at(root->rb_node);
    requires root != 0;
    produces ctx: ctx_at(result, root);
    produces sub: rb_at(result);
    ensures plug(ctx.model, sub.model) == old(t.model);
    ensures rb_right(sub.model) == RbTree::Empty;
    ensures old(t.model) != RbTree::Empty implies
        rb_list_ends_with(rb_inorder(old(t.model)), result) == 1;
} by {
    step();
    step();
    match t.model {
        RbTree::Empty => {
            unfold(t);
            let sub = fold(rb_at(n), { model: RbTree::Empty });
            let ctx = fold(ctx_at(n, root), { model: Context::Top });
            have rb_right(sub.model) == RbTree::Empty by {
                rewrite(sub.model == RbTree::Empty);
                unfold(rb_right(RbTree::Empty));
                normalize();
            }
            have plug(ctx.model, sub.model) == old(t.model) by {
                rewrite(ctx.model == Context::Top);
                unfold(plug(Context::Top, sub.model));
                rewrite(sub.model == RbTree::Empty);
                simp();
            }
            execute();
            simp();
        },
        RbTree::Node(entry_identity, entry_parent, entry_color,
                     entry_left, entry_right) => {
            let { left: entry_l, right: entry_r } = unfold(t);
            have root->rb_node != 0 by { simp(); }
            let t = fold(rb_at(n), { model: old(t.model) },
                         { left: entry_l, right: entry_r });
            let ctx = fold(ctx_at(n, root), { model: Context::Top });
            have ctx_all_right(ctx.model) == 1 by {
                rewrite(ctx.model == Context::Top);
                unfold(ctx_all_right(Context::Top));
                normalize();
            }
            have plug(ctx.model, t.model) == old(t.model) by {
                rewrite(ctx.model == Context::Top);
                unfold(plug(Context::Top, t.model));
                normalize();
            }
            have t.model != RbTree::Empty by { simp(); }
            have n != 0 by { simp(); }
            branch {
                then { contradiction(n == 0); }
                else {}
            }
            loop {
                owns ctx: ctx_at(n, root);
                owns t: rb_at(n);
                decreases t;
                invariant t.model != RbTree::Empty;
                invariant ctx_all_right(ctx.model) == 1;
                invariant plug(ctx.model, t.model) == old(t.model);

                initialize by simp;
                preserve by {
                    match t.model {
                        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                        RbTree::Node(identity, parent, color, left_model, right_model) => {
                            have plug(Context::Right(identity, parent, color, left_model,
                                                  ctx.model), right_model)
                                == old(t.model) by {
                                unfold(plug(Context::Right(identity, parent, color,
                                                        left_model, ctx.model), right_model));
                                rewrite(RbTree::Node(identity, parent, color, left_model,
                                                     right_model) == t.model);
                                assumption();
                            }
                            let { left: l, right: rt } = unfold(t);
                            have plug(Context::Right(n, parent, color, left_model, ctx.model),
                                      right_model)
                                == old(t.model) by {
                                rewrite(n == identity);
                                assumption();
                            }
                            have ctx_all_right(Context::Right(n, parent, color, left_model,
                                                             ctx.model)) == 1 by {
                                unfold(ctx_all_right(Context::Right(n, parent, color, left_model,
                                                                    ctx.model)));
                                assumption();
                            }
                            let frame = fold(ctx_at(n->rb_right, root), {
                                model: Context::Right(n, parent, color, left_model, ctx.model)
                            }, { sibling: l, up: ctx });
                            step();
                            close_invariants();
                        }
                    }
                }
            }
            match t.model {
                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                RbTree::Node(identity, parent, color, left_model, right_model) => {
                    have plug(ctx.model,
                              RbTree::Node(identity, parent, color, left_model, right_model))
                        == old(t.model) by {
                        rewrite(RbTree::Node(identity, parent, color, left_model, right_model)
                            == t.model);
                        assumption();
                    }
                    let { left: l, right: rt } = unfold(t);
                    have rb_right(RbTree::Node(identity, parent, color, left_model, right_model))
                        == right_model by {
                        unfold(rb_right(RbTree::Node(identity, parent, color, left_model,
                                                 right_model)));
                        normalize();
                    }
                    let sub = fold(rb_at(n), {
                        model: RbTree::Node(identity, parent, color, left_model, right_model)
                    }, { left: l, right: rt });
                    have rb_right(sub.model) == RbTree::Empty by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        rewrite(rb_right(RbTree::Node(identity, parent, color, left_model,
                                                  right_model))
                            == right_model);
                        assumption();
                    }
                    have plug(ctx.model, sub.model) == old(t.model) by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        assumption();
                    }
                    have rb_identity_is(sub.model, identity) == 1 by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        unfold(rb_identity_is(
                            RbTree::Node(identity, parent, color, left_model, right_model),
                            identity));
                        normalize();
                    }
                    have rb_identity_is(sub.model, n) == 1 by {
                        rewrite(sub.model
                            == RbTree::Node(identity, parent, color, left_model, right_model));
                        unfold(rb_identity_is(
                            RbTree::Node(identity, parent, color, left_model, right_model), n));
                        normalize() using { n == identity; }
                    }
                    have rb_list_ends_with(rb_inorder(sub.model), n) == 1 by {
                        apply(rb_inorder_last_at_rightmost(sub.model, n));
                        assumption();
                    }
                    have rb_list_ends_with(rb_inorder(plug(ctx.model, sub.model)), n) == 1 by {
                        apply(plug_keeps_last(ctx.model, sub.model, n));
                        assumption();
                    }
                    have old(t.model) == plug(ctx.model, sub.model) by { simp(); }
                    have rb_list_ends_with(rb_inorder(old(t.model)), n) == 1 by {
                        rewrite(old(t.model) == plug(ctx.model, sub.model));
                        assumption();
                    }
                    step();
                    simp();
                },
            }
        },
    }
}

```

```expect
pass
```
