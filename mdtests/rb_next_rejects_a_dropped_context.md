# `rb_next` does not hand back the entry subtree alone

This is [`rb_next.md`](rb_next.md) with one clause changed. The contract claims
that the frame and the subtree produced at the result rebuild `old(t.model)`,
the subtree under the entry node, rather than
`plug(old(c.model), old(t.model))`, the whole entry tree.

That is the wrong result. On the descent the first frame is folded over the
entry context, so `plug(ctx.model, sub.model)` puts the entry subtree back
under every frame the caller handed in; it equals the bare subtree only when
the entry context is `Top`. The proof is unchanged and proves what it proved
before, and the changed clause is refused at the descent's `return`.

```c filename=rbtree.h
#ifndef RBTREE_H
#define RBTREE_H
#define NULL 0

struct rb_node {
    unsigned long __rb_parent_color;
    struct rb_node *rb_right;
    struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));

#define rb_parent(r)   ((struct rb_node *)((r)->__rb_parent_color & ~3))

#define RB_EMPTY_NODE(node)  \
	((node)->__rb_parent_color == (unsigned long)(node))
#endif
```

```c filename=rb_next.c
#include "rbtree.h"

struct rb_node *rb_next(struct rb_node *node)
{
	struct rb_node *parent;

	if (RB_EMPTY_NODE(node))
		return NULL;

	/*
	 * If we have a right-hand child, go down and then left as far
	 * as we can.
	 */
	if (node->rb_right) {
		node = node->rb_right;
		while (node->rb_left)
			node = node->rb_left;
		return (struct rb_node *)node;
	}

	/*
	 * No right-hand children. Everything down and left is smaller than us,
	 * so any 'next' node must be in the general direction of our parent.
	 * Go up the tree; any time the ancestor is a right-hand child of its
	 * parent, keep going up. First time it's a left-hand child of its
	 * parent, said parent is our 'next' node.
	 */
	while ((parent = rb_parent(node)) && node == parent->rb_right)
		node = parent;

	return parent;
}
```

```click
verifying "rb_next.c";

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

function ctx_node_is(ctx: Context, p: struct rb_node*) -> int32 {
    match ctx {
        Context::Top => if p == 0 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if identity == p { 1 } else { 0 },
    }
}

function rb_ctx_linked(tree: RbTree, ctx: Context) -> int32 {
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(identity, parent, color, left, right) => ctx_node_is(ctx, parent),
    }
}

function ctx_descends_from(ctx: Context, node: struct rb_node*) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            ctx_descends_from(up_model, node),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if identity == node { 1 } else { 0 },
    }
}

function rb_list_pair_at(head: struct rb_node*, tail: List<struct rb_node*>,
                         first: struct rb_node*, second: struct rb_node*) -> int32 {
    if rb_list_starts_with(tail, second) == 1 {
        if first == head { 1 } else { 0 }
    } else {
        0
    }
}

function rb_list_adjacent(xs: List<struct rb_node*>, first: struct rb_node*,
                          second: struct rb_node*) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) =>
            if rb_list_pair_at(head, tail, first, second) == 1 {
                1
            } else {
                rb_list_adjacent(tail, first, second)
            },
    }
}

theorem list_adjacent_here(head: struct rb_node*, tail: List<struct rb_node*>,
                           first: struct rb_node*, second: struct rb_node*) {
    requires first == head;
    requires rb_list_starts_with(tail, second) == 1;
    ensures rb_list_adjacent(List<struct rb_node*>::Cons(head, tail), first, second) == 1 by {
        have rb_list_pair_at(head, tail, first, second) == 1 by {
            unfold(rb_list_pair_at(head, tail, first, second));
            normalize() using {
                rb_list_starts_with(tail, second) == 1;
                first == head;
            }
        }
        unfold(rb_list_adjacent(List<struct rb_node*>::Cons(head, tail), first, second));
        normalize() using { rb_list_pair_at(head, tail, first, second) == 1; }
    }
}

theorem list_adjacent_cons(head: struct rb_node*, tail: List<struct rb_node*>,
                           first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_adjacent(tail, first, second) == 1;
    ensures rb_list_adjacent(List<struct rb_node*>::Cons(head, tail), first, second) == 1 by {
        unfold(rb_list_adjacent(List<struct rb_node*>::Cons(head, tail), first, second));
        if rb_list_pair_at(head, tail, first, second) == 1 {
            normalize() using { rb_list_pair_at(head, tail, first, second) == 1; }
        } else {
            normalize() using {
                not(rb_list_pair_at(head, tail, first, second) == 1);
                rb_list_adjacent(tail, first, second) == 1;
            }
        }
    }
}

theorem list_adjacent_append_left(xs: List<struct rb_node*>, ys: List<struct rb_node*>,
                                  first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_adjacent(ys, first, second) == 1;
    ensures rb_list_adjacent(list_append(xs, ys), first, second) == 1 by {
        induct(xs) as ih {
            List::Nil => {
                unfold(list_append(List<struct rb_node*>::Nil, ys));
                assumption();
            }
            List::Cons(head, tail) => {
                apply(ih(tail, ys, first, second));
                apply(list_adjacent_cons(head, list_append(tail, ys), first, second));
                apply(list_append_cons(head, tail, ys));
                rewrite(list_append(List<struct rb_node*>::Cons(head, tail), ys)
                    == List<struct rb_node*>::Cons(head, list_append(tail, ys)));
                assumption();
            }
        }
    }
}

theorem list_pair_at_parts(head: struct rb_node*, tail: List<struct rb_node*>,
                           first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_pair_at(head, tail, first, second) == 1;
    ensures rb_list_starts_with(tail, second) == 1 by {
        if rb_list_starts_with(tail, second) == 1 {
            assumption();
        } else {
            have rb_list_pair_at(head, tail, first, second) == 0 by {
                unfold(rb_list_pair_at(head, tail, first, second));
                normalize() using { not(rb_list_starts_with(tail, second) == 1); }
            }
            have rb_list_pair_at(head, tail, first, second) != 0 by {
                rewrite(rb_list_pair_at(head, tail, first, second) == 1);
                normalize();
            }
            contradiction(rb_list_pair_at(head, tail, first, second) == 0);
        }
    }
    ensures first == head by {
        if first == head {
            assumption();
        } else {
            have rb_list_pair_at(head, tail, first, second) == 0 by {
                unfold(rb_list_pair_at(head, tail, first, second));
                normalize() using { not(first == head); }
            }
            have rb_list_pair_at(head, tail, first, second) != 0 by {
                rewrite(rb_list_pair_at(head, tail, first, second) == 1);
                normalize();
            }
            contradiction(rb_list_pair_at(head, tail, first, second) == 0);
        }
    }
}

theorem list_adjacent_append_right(xs: List<struct rb_node*>, ys: List<struct rb_node*>,
                                   first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_adjacent(xs, first, second) == 1;
    ensures rb_list_adjacent(list_append(xs, ys), first, second) == 1 by {
        induct(xs) as ih {
            List::Nil => {
                have rb_list_adjacent(List<struct rb_node*>::Nil, first, second) == 0 by {
                    unfold(rb_list_adjacent(List<struct rb_node*>::Nil, first, second));
                    normalize();
                }
                have rb_list_adjacent(List<struct rb_node*>::Nil, first, second) != 0 by {
                    rewrite(rb_list_adjacent(List<struct rb_node*>::Nil, first, second) == 1);
                    normalize();
                }
                contradiction(rb_list_adjacent(List<struct rb_node*>::Nil, first, second) == 0);
            }
            List::Cons(head, tail) => {
                apply(list_append_cons(head, tail, ys));
                if rb_list_pair_at(head, tail, first, second) == 1 {
                    apply(list_pair_at_parts(head, tail, first, second));
                    have rb_list_starts_with(tail, second) != 0 by {
                        rewrite(rb_list_starts_with(tail, second) == 1);
                        normalize();
                    }
                    apply(list_starts_with_append(tail, ys, second));
                    apply(list_adjacent_here(head, list_append(tail, ys), first, second));
                    rewrite(list_append(List<struct rb_node*>::Cons(head, tail), ys)
                        == List<struct rb_node*>::Cons(head, list_append(tail, ys)));
                    assumption();
                } else {
                    have rb_list_adjacent(tail, first, second) == 1 by {
                        have rb_list_adjacent(List<struct rb_node*>::Cons(head, tail), first, second)
                            == rb_list_adjacent(tail, first, second) by {
                            unfold(rb_list_adjacent(List<struct rb_node*>::Cons(head, tail),
                                                    first, second));
                            normalize() using {
                                not(rb_list_pair_at(head, tail, first, second) == 1);
                            }
                        }
                        rewrite(rb_list_adjacent(tail, first, second)
                            == rb_list_adjacent(List<struct rb_node*>::Cons(head, tail),
                                                first, second));
                        assumption();
                    }
                    apply(ih(tail, ys, first, second));
                    apply(list_adjacent_cons(head, list_append(tail, ys), first, second));
                    rewrite(list_append(List<struct rb_node*>::Cons(head, tail), ys)
                        == List<struct rb_node*>::Cons(head, list_append(tail, ys)));
                    assumption();
                }
            }
        }
    }
}

theorem list_ends_then_adjacent(xs: List<struct rb_node*>, head: struct rb_node*,
                                ys: List<struct rb_node*>,
                                first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_ends_with(xs, first) == 1;
    requires second == head;
    ensures rb_list_adjacent(
        list_append(xs, List<struct rb_node*>::Cons(head, ys)), first, second) == 1 by {
        induct(xs) as ih {
            List::Nil => {
                have rb_list_ends_with(List<struct rb_node*>::Nil, first) == 0 by {
                    unfold(rb_list_ends_with(List<struct rb_node*>::Nil, first));
                    normalize();
                }
                have rb_list_ends_with(List<struct rb_node*>::Nil, first) != 0 by {
                    rewrite(rb_list_ends_with(List<struct rb_node*>::Nil, first) == 1);
                    normalize();
                }
                contradiction(rb_list_ends_with(List<struct rb_node*>::Nil, first) == 0);
            }
            List::Cons(front, tail) => {
                apply(list_append_cons(front, tail, List<struct rb_node*>::Cons(head, ys)));
                if tail == List<struct rb_node*>::Nil {
                    have rb_list_ends_with(List<struct rb_node*>::Cons(front, tail), first)
                        == if first == front { 1 } else { 0 } by {
                        unfold(rb_list_ends_with(List<struct rb_node*>::Cons(front, tail), first));
                        normalize() using { tail == List<struct rb_node*>::Nil; }
                    }
                    if first == front {
                        have rb_list_starts_with(
                                List<struct rb_node*>::Cons(head, ys), second) == 1 by {
                            unfold(rb_list_starts_with(
                                List<struct rb_node*>::Cons(head, ys), second));
                            normalize() using { second == head; }
                        }
                        apply(list_adjacent_here(front,
                            List<struct rb_node*>::Cons(head, ys), first, second));
                        have list_append(List<struct rb_node*>::Nil,
                                List<struct rb_node*>::Cons(head, ys))
                            == List<struct rb_node*>::Cons(head, ys) by {
                            unfold(list_append(List<struct rb_node*>::Nil,
                                List<struct rb_node*>::Cons(head, ys)));
                            normalize();
                        }
                        rewrite(list_append(List<struct rb_node*>::Cons(front, tail),
                                List<struct rb_node*>::Cons(head, ys))
                            == List<struct rb_node*>::Cons(front, list_append(tail,
                                List<struct rb_node*>::Cons(head, ys))));
                        rewrite(tail == List<struct rb_node*>::Nil);
                        rewrite(list_append(List<struct rb_node*>::Nil,
                                List<struct rb_node*>::Cons(head, ys))
                            == List<struct rb_node*>::Cons(head, ys));
                        assumption();
                    } else {
                        have rb_list_ends_with(List<struct rb_node*>::Cons(front, tail), first)
                            == 0 by {
                            rewrite(rb_list_ends_with(
                                    List<struct rb_node*>::Cons(front, tail), first)
                                == if first == front { 1 } else { 0 });
                            normalize() using { not(first == front); }
                        }
                        have rb_list_ends_with(List<struct rb_node*>::Cons(front, tail), first)
                            != 0 by {
                            rewrite(rb_list_ends_with(
                                List<struct rb_node*>::Cons(front, tail), first) == 1);
                            normalize();
                        }
                        contradiction(rb_list_ends_with(
                            List<struct rb_node*>::Cons(front, tail), first) == 0);
                    }
                } else {
                    apply(list_ends_with_cons_nonempty(front, tail, first));
                    have rb_list_ends_with(tail, first) == 1 by {
                        rewrite(rb_list_ends_with(tail, first)
                            == rb_list_ends_with(List<struct rb_node*>::Cons(front, tail), first));
                        assumption();
                    }
                    apply(ih(tail, head, ys, first, second));
                    apply(list_adjacent_cons(front,
                        list_append(tail, List<struct rb_node*>::Cons(head, ys)),
                        first, second));
                    rewrite(list_append(List<struct rb_node*>::Cons(front, tail),
                            List<struct rb_node*>::Cons(head, ys))
                        == List<struct rb_node*>::Cons(front, list_append(tail,
                            List<struct rb_node*>::Cons(head, ys))));
                    assumption();
                }
            }
        }
    }
}

theorem rb_inorder_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                        left: RbTree, right: RbTree) {
    ensures rb_inorder(RbTree::Node(identity, parent, color, left, right))
        == list_append(rb_inorder(left),
            List<struct rb_node*>::Cons(identity, rb_inorder(right))) by {
        unfold(rb_inorder(RbTree::Node(identity, parent, color, left, right)));
        normalize();
    }
}

theorem rb_inorder_adjacent_below(identity: struct rb_node*, parent: struct rb_node*,
                                  color: Color, left: RbTree, right: RbTree,
                                  node: struct rb_node*, next: struct rb_node*) {
    requires node == identity;
    requires rb_list_starts_with(rb_inorder(right), next) == 1;
    ensures rb_list_adjacent(
        rb_inorder(RbTree::Node(identity, parent, color, left, right)), node, next) == 1 by {
        apply(rb_inorder_node(identity, parent, color, left, right));
        apply(list_adjacent_here(identity, rb_inorder(right), node, next));
        apply(list_adjacent_append_left(rb_inorder(left),
            List<struct rb_node*>::Cons(identity, rb_inorder(right)), node, next));
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right))
            == list_append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        assumption();
    }
}

theorem rb_inorder_adjacent_above(identity: struct rb_node*, parent: struct rb_node*,
                                  color: Color, left: RbTree, right: RbTree,
                                  node: struct rb_node*, next: struct rb_node*) {
    requires rb_list_ends_with(rb_inorder(left), node) == 1;
    requires next == identity;
    ensures rb_list_adjacent(
        rb_inorder(RbTree::Node(identity, parent, color, left, right)), node, next) == 1 by {
        apply(rb_inorder_node(identity, parent, color, left, right));
        apply(list_ends_then_adjacent(rb_inorder(left), identity, rb_inorder(right),
                                      node, next));
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right))
            == list_append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        assumption();
    }
}

theorem rb_inorder_last_through_right(identity: struct rb_node*, parent: struct rb_node*,
                                      color: Color, left: RbTree, right: RbTree,
                                      node: struct rb_node*) {
    requires rb_list_ends_with(rb_inorder(right), node) == 1;
    ensures rb_list_ends_with(
        rb_inorder(RbTree::Node(identity, parent, color, left, right)), node) == 1 by {
        apply(rb_inorder_node(identity, parent, color, left, right));
        have rb_list_ends_with(rb_inorder(right), node) != 0 by {
            rewrite(rb_list_ends_with(rb_inorder(right), node) == 1);
            normalize();
        }
        apply(list_ends_with_is_nonempty(rb_inorder(right), node));
        apply(list_ends_with_cons_nonempty(identity, rb_inorder(right), node));
        have rb_list_ends_with(
                List<struct rb_node*>::Cons(identity, rb_inorder(right)), node) == 1 by {
            rewrite(rb_list_ends_with(
                    List<struct rb_node*>::Cons(identity, rb_inorder(right)), node)
                == rb_list_ends_with(rb_inorder(right), node));
            assumption();
        }
        apply(list_ends_with_append(rb_inorder(left),
            List<struct rb_node*>::Cons(identity, rb_inorder(right)), node));
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right))
            == list_append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        assumption();
    }
}

theorem plug_keeps_adjacent(ctx: Context, sub: RbTree,
                            first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_adjacent(rb_inorder(sub), first, second) == 1;
    ensures rb_list_adjacent(rb_inorder(plug(ctx, sub)), first, second) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(rb_inorder_node(identity, grandparent, color, sub, sibling_model));
                apply(list_adjacent_append_right(rb_inorder(sub),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model)),
                    first, second));
                have rb_list_adjacent(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sub,
                                                sibling_model)), first, second) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sub, sibling_model))
                        == list_append(rb_inorder(sub),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))));
                    assumption();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sub, sibling_model),
                         first, second));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                            sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(rb_inorder_node(identity, grandparent, color, sibling_model, sub));
                apply(list_adjacent_cons(identity, rb_inorder(sub), first, second));
                apply(list_adjacent_append_left(rb_inorder(sibling_model),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sub)), first, second));
                have rb_list_adjacent(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model,
                                                sub)), first, second) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sibling_model, sub))
                        == list_append(rb_inorder(sibling_model),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub))));
                    assumption();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sibling_model, sub),
                         first, second));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                            sub));
                assumption();
            }
        }
    }
}

theorem plug_successor(ctx: Context, sub: RbTree,
                       node: struct rb_node*, next: struct rb_node*) {
    requires ctx_descends_from(ctx, node) == 1;
    requires rb_list_starts_with(rb_inorder(sub), next) == 1;
    ensures rb_list_adjacent(rb_inorder(plug(ctx, sub)), node, next) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                have ctx_descends_from(Context::Top, node) == 0 by {
                    unfold(ctx_descends_from(Context::Top, node));
                    normalize();
                }
                have ctx_descends_from(Context::Top, node) != 0 by {
                    rewrite(ctx_descends_from(Context::Top, node) == 1);
                    normalize();
                }
                contradiction(ctx_descends_from(Context::Top, node) == 0);
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_descends_from(Context::Left(identity, grandparent, color,
                                                     sibling_model, up_model), node)
                    == ctx_descends_from(up_model, node) by {
                    unfold(ctx_descends_from(Context::Left(identity, grandparent, color,
                                                           sibling_model, up_model), node));
                    normalize();
                }
                have ctx_descends_from(up_model, node) == 1 by {
                    rewrite(ctx_descends_from(up_model, node)
                        == ctx_descends_from(Context::Left(identity, grandparent, color,
                                                           sibling_model, up_model), node));
                    assumption();
                }
                apply(rb_inorder_node(identity, grandparent, color, sub, sibling_model));
                have rb_list_starts_with(rb_inorder(sub), next) != 0 by {
                    rewrite(rb_list_starts_with(rb_inorder(sub), next) == 1);
                    normalize();
                }
                apply(list_starts_with_append(rb_inorder(sub),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model)), next));
                have rb_list_starts_with(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sub,
                                                sibling_model)), next) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sub, sibling_model))
                        == list_append(rb_inorder(sub),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))));
                    assumption();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sub, sibling_model),
                         node, next));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                            sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_descends_from(Context::Right(identity, grandparent, color,
                                                      sibling_model, up_model), node)
                    == if identity == node { 1 } else { 0 } by {
                    unfold(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                            sibling_model, up_model), node));
                    normalize();
                }
                if identity == node {
                    have node == identity by {
                        rewrite(identity == node);
                        normalize();
                    }
                    apply(rb_inorder_adjacent_below(identity, grandparent, color,
                        sibling_model, sub, node, next));
                    apply(plug_keeps_adjacent(up_model,
                        RbTree::Node(identity, grandparent, color, sibling_model, sub),
                        node, next));
                    unfold(plug(Context::Right(identity, grandparent, color, sibling_model,
                                               up_model), sub));
                    assumption();
                } else {
                    have ctx_descends_from(Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model), node)
                        == 0 by {
                        rewrite(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                                 sibling_model, up_model), node)
                            == if identity == node { 1 } else { 0 });
                        normalize() using { not(identity == node); }
                    }
                    have ctx_descends_from(Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model), node)
                        != 0 by {
                        rewrite(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                                 sibling_model, up_model), node)
                            == 1);
                        normalize();
                    }
                    contradiction(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                                   sibling_model, up_model), node)
                        == 0);
                }
            }
        }
    }
}

theorem ctx_node_is_top(p: struct rb_node*) {
    requires ctx_node_is(Context::Top, p) == 1;
    ensures p == 0 by {
        if p == 0 {
            assumption();
        } else {
            have ctx_node_is(Context::Top, p) == 0 by {
                unfold(ctx_node_is(Context::Top, p));
                normalize() using { not(p == 0); }
            }
            have ctx_node_is(Context::Top, p) != 0 by {
                rewrite(ctx_node_is(Context::Top, p) == 1);
                normalize();
            }
            contradiction(ctx_node_is(Context::Top, p) == 0);
        }
    }
}

theorem ctx_node_is_left(identity: struct rb_node*, grandparent: struct rb_node*, color: Color,
                         sibling_model: RbTree, up_model: Context, p: struct rb_node*) {
    requires ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, up_model), p)
        == 1;
    ensures identity == p by {
        if identity == p {
            assumption();
        } else {
            have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                           up_model), p) == 0 by {
                unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model), p));
                normalize() using { not(identity == p); }
            }
            have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                           up_model), p) != 0 by {
                rewrite(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                  up_model), p) == 1);
                normalize();
            }
            contradiction(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                    up_model), p) == 0);
        }
    }
}

theorem ctx_node_is_right(identity: struct rb_node*, grandparent: struct rb_node*, color: Color,
                          sibling_model: RbTree, up_model: Context, p: struct rb_node*) {
    requires ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, up_model), p)
        == 1;
    ensures identity == p by {
        if identity == p {
            assumption();
        } else {
            have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                            up_model), p) == 0 by {
                unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                  up_model), p));
                normalize() using { not(identity == p); }
            }
            have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                            up_model), p) != 0 by {
                rewrite(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                   up_model), p) == 1);
                normalize();
            }
            contradiction(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                     up_model), p) == 0);
        }
    }
}

theorem rb_ctx_linked_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                           left: RbTree, right: RbTree, ctx: Context) {
    ensures rb_ctx_linked(RbTree::Node(identity, parent, color, left, right), ctx)
        == ctx_node_is(ctx, parent) by {
        unfold(rb_ctx_linked(RbTree::Node(identity, parent, color, left, right), ctx));
        normalize();
    }
}

theorem rb_parent_is_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                          left: RbTree, right: RbTree, p: struct rb_node*) {
    requires rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) == 1;
    ensures parent == p by {
        if parent == p {
            assumption();
        } else {
            have rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) == 0 by {
                unfold(rb_parent_is(RbTree::Node(identity, parent, color, left, right), p));
                normalize() using { not(parent == p); }
            }
            have rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) != 0 by {
                rewrite(rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) == 1);
                normalize();
            }
            contradiction(rb_parent_is(RbTree::Node(identity, parent, color, left, right), p)
                == 0);
        }
    }
}

theorem rb_parent_is_same(tree: RbTree, a: struct rb_node*, b: struct rb_node*) {
    requires rb_parent_is(tree, a) == 1;
    requires a == b;
    ensures rb_parent_is(tree, b) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, b));
                normalize();
            }
            RbTree::Node(identity, parent, color, left, right) => {
                apply(rb_parent_is_node(identity, parent, color, left, right, a));
                have parent == b by {
                    rewrite(b == a);
                    assumption();
                }
                unfold(rb_parent_is(RbTree::Node(identity, parent, color, left, right), b));
                normalize() using { parent == b; }
            }
        }
    }
}

theorem ctx_node_is_same(ctx: Context, a: struct rb_node*, b: struct rb_node*) {
    requires ctx_node_is(ctx, a) == 1;
    requires a == b;
    ensures ctx_node_is(ctx, b) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_node_is_top(a));
                have b == 0 by {
                    rewrite(b == a);
                    assumption();
                }
                unfold(ctx_node_is(Context::Top, b));
                normalize() using { b == 0; }
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_node_is_left(identity, grandparent, color, sibling_model, up_model, a));
                have identity == b by {
                    rewrite(b == a);
                    assumption();
                }
                unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model), b));
                normalize() using { identity == b; }
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_node_is_right(identity, grandparent, color, sibling_model, up_model,
                                        a));
                have identity == b by {
                    rewrite(b == a);
                    assumption();
                }
                unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                  up_model), b));
                normalize() using { identity == b; }
            }
        }
    }
}

theorem rb_ctx_linked_from_parent(identity: struct rb_node*, parent: struct rb_node*,
                                  color: Color, left: RbTree, right: RbTree,
                                  ctx: Context, p: struct rb_node*) {
    requires rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) == 1;
    requires ctx_node_is(ctx, p) == 1;
    ensures rb_ctx_linked(RbTree::Node(identity, parent, color, left, right), ctx) == 1 by {
        apply(rb_parent_is_node(identity, parent, color, left, right, p));
        have p == parent by {
            rewrite(parent == p);
            normalize();
        }
        apply(ctx_node_is_same(ctx, p, parent));
        unfold(rb_ctx_linked(RbTree::Node(identity, parent, color, left, right), ctx));
        assumption();
    }
}

function ctx_is_right(ctx: Context) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) => 0,
        Context::Right(identity, grandparent, color, sibling_model, up_model) => 1,
    }
}

theorem rb_ctx_linked_is_nonempty(tree: RbTree, ctx: Context) {
    requires rb_ctx_linked(tree, ctx) == 1;
    ensures tree != RbTree::Empty by {
        induct(tree) as ih {
            RbTree::Empty => {
                have rb_ctx_linked(RbTree::Empty, ctx) == 0 by {
                    unfold(rb_ctx_linked(RbTree::Empty, ctx));
                    normalize();
                }
                have rb_ctx_linked(RbTree::Empty, ctx) != 0 by {
                    rewrite(rb_ctx_linked(RbTree::Empty, ctx) == 1);
                    normalize();
                }
                contradiction(rb_ctx_linked(RbTree::Empty, ctx) == 0);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                normalize();
            }
        }
    }
}

theorem rb_ctx_linked_left_parent(tree: RbTree, identity: struct rb_node*,
                                  grandparent: struct rb_node*, color: Color,
                                  sibling_model: RbTree, up_model: Context) {
    requires rb_ctx_linked(tree,
        Context::Left(identity, grandparent, color, sibling_model, up_model)) == 1;
    ensures rb_parent_is(tree, identity) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, identity));
                normalize();
            }
            RbTree::Node(node, parent, node_color, left, right) => {
                apply(rb_ctx_linked_node(node, parent, node_color, left, right,
                    Context::Left(identity, grandparent, color, sibling_model, up_model)));
                have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                               up_model), parent) == 1 by {
                    rewrite(ctx_node_is(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model), parent)
                        == rb_ctx_linked(RbTree::Node(node, parent, node_color, left, right),
                            Context::Left(identity, grandparent, color, sibling_model,
                                          up_model)));
                    assumption();
                }
                apply(ctx_node_is_left(identity, grandparent, color, sibling_model, up_model,
                                       parent));
                have parent == identity by {
                    rewrite(identity == parent);
                    normalize();
                }
                unfold(rb_parent_is(RbTree::Node(node, parent, node_color, left, right),
                                    identity));
                normalize() using { parent == identity; }
            }
        }
    }
}

theorem rb_ctx_linked_right_parent(tree: RbTree, identity: struct rb_node*,
                                   grandparent: struct rb_node*, color: Color,
                                   sibling_model: RbTree, up_model: Context) {
    requires rb_ctx_linked(tree,
        Context::Right(identity, grandparent, color, sibling_model, up_model)) == 1;
    ensures rb_parent_is(tree, identity) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, identity));
                normalize();
            }
            RbTree::Node(node, parent, node_color, left, right) => {
                apply(rb_ctx_linked_node(node, parent, node_color, left, right,
                    Context::Right(identity, grandparent, color, sibling_model, up_model)));
                have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                up_model), parent) == 1 by {
                    rewrite(ctx_node_is(Context::Right(identity, grandparent, color,
                                                       sibling_model, up_model), parent)
                        == rb_ctx_linked(RbTree::Node(node, parent, node_color, left, right),
                            Context::Right(identity, grandparent, color, sibling_model,
                                           up_model)));
                    assumption();
                }
                apply(ctx_node_is_right(identity, grandparent, color, sibling_model, up_model,
                                        parent));
                have parent == identity by {
                    rewrite(identity == parent);
                    normalize();
                }
                unfold(rb_parent_is(RbTree::Node(node, parent, node_color, left, right),
                                    identity));
                normalize() using { parent == identity; }
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
            fact parent != p;
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

resource ctx_at(child: struct rb_node*) {
    field model: Context;
    match model {
        Context::Top => { },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_right);
            owns up: ctx_at(identity);
            fact identity != 0;
            fact grandparent != identity;
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
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            owns identity->__rb_parent_color;
            owns identity->rb_left;
            owns identity->rb_right;
            owns sibling: rb_at(identity->rb_left);
            owns up: ctx_at(identity);
            fact identity != 0;
            fact grandparent != identity;
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
        },
    }
}

spec enum Remainder {
    More,
    Whole(struct rb_node*, RbTree),
}

function rb_remainder_tree(remainder: Remainder) -> RbTree {
    match remainder {
        Remainder::More => RbTree::Empty,
        Remainder::Whole(top, whole_model) => whole_model,
    }
}

resource rb_remainder_at(result: struct rb_node*) {
    field model: Remainder;
    match model {
        Remainder::More => { fact result != 0; },
        Remainder::Whole(top, whole_model) => {
            owns whole: rb_at(top);
            fact result == 0;
            fact whole.model == whole_model;
        },
    }
}
struct rb_node* rb_next(struct rb_node* node) {
    consumes c: ctx_at(node);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_ctx_linked(t.model, c.model) == 1;
    produces ctx: ctx_at(result);
    produces sub: rb_at(result);
    produces rest: rb_remainder_at(result);
    ensures result != 0 implies plug(ctx.model, sub.model) == old(t.model);
    ensures result != 0 implies rb_ctx_linked(sub.model, ctx.model) == 1;
    ensures result != 0 implies
        rb_list_adjacent(rb_inorder(plug(old(c.model), old(t.model))), node, result) == 1;
    ensures result == 0 implies
        rb_remainder_tree(rest.model) == plug(old(c.model), old(t.model));
    ensures result == 0 implies
        rb_list_ends_with(rb_inorder(plug(old(c.model), old(t.model))), node) == 1;
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(entry_identity, entry_parent, entry_color, entry_left, entry_right) => {
            have ctx_node_is(old(c.model), entry_parent) == 1 by {
                apply(rb_ctx_linked_node(entry_identity, entry_parent, entry_color, entry_left,
                        entry_right, old(c.model)));
                rewrite(ctx_node_is(old(c.model),
                        entry_parent) == rb_ctx_linked(RbTree::Node(entry_identity,
                            entry_parent, entry_color, entry_left, entry_right), old(c.model)));
                rewrite(RbTree::Node(entry_identity, entry_parent, entry_color, entry_left,
                        entry_right) == t.model);
                assumption();
            }
            have plug(Context::Right(entry_identity, entry_parent, entry_color, entry_left,
                    old(c.model)), entry_right) == plug(old(c.model), old(t.model)) by {
                unfold(plug(Context::Right(entry_identity, entry_parent, entry_color,
                            entry_left, old(c.model)), entry_right));
                rewrite(RbTree::Node(entry_identity, entry_parent, entry_color, entry_left,
                        entry_right) == t.model);
                normalize();
            }
            let { left: entry_l, right: entry_r } = unfold(t);
            step();
            step();
            match entry_r.model {
                RbTree::Node(right_identity, right_parent, right_color, right_left,
                    right_right) => {
                    have RbTree::Node(right_identity, right_parent, right_color, right_left,
                        right_right) == entry_right by { simp(); }
                    have rb_parent_is(RbTree::Node(right_identity, right_parent, right_color,
                            right_left, right_right), node) == 1 by {
                        rewrite(RbTree::Node(right_identity, right_parent, right_color,
                                right_left, right_right) == entry_right);
                        assumption();
                    }
                    have ctx_node_is(Context::Right(node, entry_parent, entry_color, entry_left,
                            old(c.model)), node) == 1 by {
                        unfold(ctx_node_is(Context::Right(node, entry_parent, entry_color,
                                    entry_left, old(c.model)), node));
                        normalize();
                    }
                    have rb_ctx_linked(RbTree::Node(right_identity, right_parent, right_color,
                            right_left, right_right), Context::Right(node, entry_parent,
                            entry_color, entry_left, old(c.model))) == 1 by {
                        apply(rb_ctx_linked_from_parent(right_identity, right_parent,
                                right_color, right_left, right_right, Context::Right(node,
                                    entry_parent, entry_color, entry_left, old(c.model)),
                                node)) using {
                            rb_parent_is(RbTree::Node(right_identity, right_parent, right_color,
                                    right_left, right_right), node) == 1;
                            ctx_node_is(Context::Right(node, entry_parent, entry_color,
                                    entry_left, old(c.model)), node) == 1;
                        }
                        assumption();
                    }
                    have plug(Context::Right(node, entry_parent, entry_color, entry_left,
                            old(c.model)), entry_right) == plug(old(c.model), old(t.model)) by {
                        rewrite(node == entry_identity);
                        assumption();
                    }
                    have ctx_descends_from(Context::Right(node, entry_parent, entry_color,
                            entry_left, old(c.model)), node) == 1 by {
                        unfold(ctx_descends_from(Context::Right(node, entry_parent, entry_color,
                                    entry_left, old(c.model)), node));
                        normalize();
                    }
                    let { left: right_l, right: right_r } = unfold(entry_r);
                    have node->rb_right != 0;
                    let t = fold(rb_at(node->rb_right), { model: entry_right }, { left: right_l,
                            right: right_r });
                    step();
                    step();
                    let ctx = fold(ctx_at(node->rb_right), { model: Context::Right(node,
                                entry_parent, entry_color, entry_left, old(c.model)) },
                        { sibling: entry_l, up: c });
                    have ctx.model == Context::Right(node, entry_parent, entry_color,
                        entry_left, old(c.model)) by { simp(); }
                    match ctx.model {
                        Context::Top => { contradiction(ctx.model == Context::Top); },
                        Context::Left(first_identity, first_parent, first_color, first_right,
                            above) => { contradiction(ctx.model == Context::Left(first_identity,
                                    first_parent, first_color, first_right, above)); },
                        Context::Right(first_identity, first_parent, first_color, first_left,
                            above) => {
                            have Context::Right(first_identity, first_parent, first_color,
                                first_left, above) == Context::Right(node, entry_parent,
                                entry_color, entry_left, old(c.model)) by {
                                rewrite(Context::Right(first_identity, first_parent,
                                        first_color, first_left, above) == ctx.model);
                                rewrite(Context::Right(node, entry_parent, entry_color,
                                        entry_left, old(c.model)) == ctx.model);
                                normalize();
                            }
                            have above == old(c.model) by extract(above == old(c.model));
                            have plug(above, RbTree::Node(entry_identity, entry_parent,
                                    entry_color, entry_left, entry_right)) == plug(old(c.model),
                                old(t.model)) by {
                                rewrite(above == old(c.model));
                                rewrite(RbTree::Node(entry_identity, entry_parent, entry_color,
                                        entry_left, entry_right) == old(t.model));
                                normalize();
                            }
                            have t.model == entry_right;
                            have plug(ctx.model, t.model) == plug(old(c.model),
                                old(t.model)) by {
                                rewrite(ctx.model == Context::Right(node, entry_parent,
                                        entry_color, entry_left, old(c.model)));
                                rewrite(t.model == entry_right);
                                assumption();
                            }
                            have plug(ctx.model, t.model) == plug(above,
                                RbTree::Node(entry_identity, entry_parent, entry_color,
                                    entry_left, entry_right)) by {
                                rewrite(plug(above, RbTree::Node(entry_identity, entry_parent,
                                            entry_color, entry_left,
                                            entry_right)) == plug(old(c.model), old(t.model)));
                                assumption();
                            }
                            have rb_ctx_linked(t.model, ctx.model) == 1 by {
                                rewrite(ctx.model == Context::Right(node, entry_parent,
                                        entry_color, entry_left, old(c.model)));
                                rewrite(t.model == entry_right);
                                rewrite(entry_right == RbTree::Node(right_identity,
                                        right_parent, right_color, right_left, right_right));
                                assumption();
                            }
                            have ctx_descends_from(ctx.model, old(node)) == 1 by {
                                rewrite(ctx.model == Context::Right(node, entry_parent,
                                        entry_color, entry_left, old(c.model)));
                                assumption();
                            }
                            step();
                            loop {
                                owns ctx: ctx_at(node);
                                owns t: rb_at(node);
                                decreases t;
                                invariant t.model != RbTree::Empty;
                                invariant rb_ctx_linked(t.model, ctx.model) == 1;
                                invariant ctx_descends_from(ctx.model, old(node)) == 1;
                                invariant plug(ctx.model, t.model) == plug(above,
                                    RbTree::Node(entry_identity, entry_parent, entry_color,
                                        entry_left, entry_right));

                                initialize by simp;
                                preserve by {
                                    match t.model {
                                        RbTree::Empty => { contradiction(t.model
                                                == RbTree::Empty); },
                                        RbTree::Node(identity, par, color, left_model,
                                            right_model) => {
                                            have ctx_node_is(ctx.model, par) == 1 by {
                                                apply(rb_ctx_linked_node(identity, par, color,
                                                        left_model, right_model, ctx.model));
                                                rewrite(ctx_node_is(ctx.model,
                                                        par)
                                                    == rb_ctx_linked(RbTree::Node(identity, par,
                                                            color, left_model, right_model),
                                                        ctx.model));
                                                rewrite(RbTree::Node(identity, par, color,
                                                        left_model, right_model) == t.model);
                                                assumption();
                                            }
                                            have plug(Context::Left(identity, par, color,
                                                    right_model, ctx.model),
                                                left_model) == plug(above,
                                                RbTree::Node(entry_identity, entry_parent,
                                                    entry_color, entry_left, entry_right)) by {
                                                unfold(plug(Context::Left(identity, par, color,
                                                            right_model, ctx.model),
                                                        left_model));
                                                rewrite(RbTree::Node(identity, par, color,
                                                        left_model, right_model) == t.model);
                                                assumption();
                                            }
                                            let { left: l, right: rt } = unfold(t);
                                            have plug(Context::Left(node, par, color,
                                                    right_model, ctx.model),
                                                left_model) == plug(above,
                                                RbTree::Node(entry_identity, entry_parent,
                                                    entry_color, entry_left, entry_right)) by {
                                                rewrite(node == identity);
                                                assumption();
                                            }
                                            have ctx_descends_from(Context::Left(node, par,
                                                    color, right_model, ctx.model),
                                                old(node)) == 1 by {
                                                unfold(ctx_descends_from(Context::Left(node,
                                                            par, color, right_model, ctx.model),
                                                        old(node)));
                                                assumption();
                                            }
                                            have ctx_node_is(Context::Left(node, par, color,
                                                    right_model, ctx.model), node) == 1 by {
                                                unfold(ctx_node_is(Context::Left(node, par,
                                                            color, right_model, ctx.model),
                                                        node));
                                                normalize();
                                            }
                                            match l.model {
                                                RbTree::Empty => { contradiction(l.model
                                                        == RbTree::Empty); },
                                                RbTree::Node(left_identity, left_parent,
                                                    left_color, left_left, left_right) => {
                                                    have left_model
                                                        == RbTree::Node(left_identity,
                                                        left_parent, left_color, left_left,
                                                        left_right) by { simp(); }
                                                    have rb_parent_is(RbTree::Node(left_identity,
                                                            left_parent, left_color, left_left,
                                                            left_right), node) == 1 by {
                                                        rewrite(RbTree::Node(left_identity,
                                                                left_parent, left_color,
                                                                left_left,
                                                                left_right) == left_model);
                                                        assumption();
                                                    }
                                                    have rb_ctx_linked(RbTree::Node(left_identity,
                                                            left_parent, left_color, left_left,
                                                            left_right), Context::Left(node,
                                                            par, color, right_model,
                                                            ctx.model)) == 1 by {
                                                        apply(rb_ctx_linked_from_parent(left_identity,
                                                                left_parent, left_color,
                                                                left_left, left_right,
                                                                Context::Left(node, par, color,
                                                                    right_model, ctx.model),
                                                                node)) using {
                                                            rb_parent_is(RbTree::Node(left_identity,
                                                                    left_parent, left_color,
                                                                    left_left, left_right),
                                                                node) == 1;
                                                            ctx_node_is(Context::Left(node, par,
                                                                    color, right_model,
                                                                    ctx.model), node) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have rb_ctx_linked(left_model,
                                                        Context::Left(node, par, color,
                                                            right_model, ctx.model)) == 1 by {
                                                        rewrite(left_model
                                                            == RbTree::Node(left_identity,
                                                                left_parent, left_color,
                                                                left_left, left_right));
                                                        assumption();
                                                    }
                                                    let frame = fold(ctx_at(node->rb_left),
                                                        { model: Context::Left(node, par, color,
                                                                right_model, ctx.model) },
                                                        { sibling: rt, up: ctx });
                                                    step();
                                                    close_invariants();
                                                },
                                            }
                                        },
                                    }
                                }
                            }
                            match t.model {
                                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                                RbTree::Node(identity, par, color, left_model, right_model) => {
                                    have plug(ctx.model, RbTree::Node(identity, par, color,
                                            left_model, right_model)) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(RbTree::Node(identity, par, color, left_model,
                                                right_model) == t.model);
                                        rewrite(plug(ctx.model, t.model) == plug(above,
                                                RbTree::Node(entry_identity, entry_parent,
                                                    entry_color, entry_left, entry_right)));
                                        assumption();
                                    }
                                    have rb_ctx_linked(RbTree::Node(identity, par, color,
                                            left_model, right_model), ctx.model) == 1 by {
                                        rewrite(RbTree::Node(identity, par, color, left_model,
                                                right_model) == t.model);
                                        assumption();
                                    }
                                    let { left: l, right: rt } = unfold(t);
                                    have rb_left(RbTree::Node(identity, par, color, left_model,
                                            right_model)) == left_model by {
                                        unfold(rb_left(RbTree::Node(identity, par, color,
                                                    left_model, right_model)));
                                        normalize();
                                    }
                                    have node != 0;
                                    let sub = fold(rb_at(node), { model: RbTree::Node(identity,
                                                par, color, left_model, right_model) },
                                        { left: l, right: rt });
                                    have rb_left(sub.model) == RbTree::Empty by {
                                        rewrite(sub.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        rewrite(rb_left(RbTree::Node(identity, par, color,
                                                    left_model, right_model)) == left_model);
                                        assumption();
                                    }
                                    have rb_identity_is(sub.model, node) == 1 by {
                                        rewrite(sub.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        unfold(rb_identity_is(RbTree::Node(identity, par, color,
                                                    left_model, right_model), node));
                                        normalize() using { node == identity; }
                                    }
                                    have rb_list_starts_with(rb_inorder(sub.model),
                                        node) == 1 by {
                                        apply(rb_inorder_first_at_leftmost(sub.model,
                                                node)) using {
                                            rb_left(sub.model) == RbTree::Empty;
                                            rb_identity_is(sub.model, node) == 1;
                                        }
                                        assumption();
                                    }
                                    have rb_list_adjacent(rb_inorder(plug(ctx.model,
                                                sub.model)), old(node), node) == 1 by {
                                        apply(plug_successor(ctx.model, sub.model, old(node),
                                                node)) using {
                                            ctx_descends_from(ctx.model, old(node)) == 1;
                                            rb_list_starts_with(rb_inorder(sub.model),
                                                node) == 1;
                                        }
                                        assumption();
                                    }
                                    have plug(ctx.model, sub.model) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(sub.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        assumption();
                                    }
                                    have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                        rewrite(sub.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        assumption();
                                    }
                                    have rb_list_adjacent(rb_inorder(plug(old(c.model),
                                                old(t.model))), old(node), node) == 1 by {
                                        rewrite(plug(old(c.model),
                                                old(t.model)) == plug(ctx.model, sub.model));
                                        assumption();
                                    }
                                    let rest = fold(rb_remainder_at(node),
                                        { model: Remainder::More });
                                    step();
                                    simp();
                                },
                            }
                        },
                    }
                },
                RbTree::Empty => {
                    have entry_right == RbTree::Empty;
                    have rb_right(RbTree::Node(entry_identity, entry_parent, entry_color,
                            entry_left, entry_right)) == RbTree::Empty by {
                        unfold(rb_right(RbTree::Node(entry_identity, entry_parent, entry_color,
                                    entry_left, entry_right)));
                        assumption();
                    }
                    have rb_identity_is(RbTree::Node(entry_identity, entry_parent, entry_color,
                            entry_left, entry_right), node) == 1 by {
                        unfold(rb_identity_is(RbTree::Node(entry_identity, entry_parent,
                                    entry_color, entry_left, entry_right), node));
                        normalize() using { node == entry_identity; }
                    }
                    have rb_list_ends_with(rb_inorder(RbTree::Node(entry_identity, entry_parent,
                                entry_color, entry_left, entry_right)), node) == 1 by {
                        apply(rb_inorder_last_at_rightmost(RbTree::Node(entry_identity,
                                    entry_parent, entry_color, entry_left, entry_right),
                                node)) using {
                            rb_right(RbTree::Node(entry_identity, entry_parent, entry_color,
                                    entry_left, entry_right)) == RbTree::Empty;
                            rb_identity_is(RbTree::Node(entry_identity, entry_parent,
                                    entry_color, entry_left, entry_right), node) == 1;
                        }
                        assumption();
                    }
                    unfold(entry_r);
                    have node->rb_right == 0;
                    let entry_r = fold(rb_at(node->rb_right), { model: RbTree::Empty });
                    step();
                    step();
                    step();
                    let t = fold(rb_at(node), { model: old(t.model) }, { left: entry_l,
                            right: entry_r });
                    have rb_list_ends_with(rb_inorder(t.model), old(node)) == 1 by {
                        rewrite(t.model == RbTree::Node(entry_identity, entry_parent,
                                entry_color, entry_left, entry_right));
                        assumption();
                    }
                    loop {
                        owns c: ctx_at(node);
                        owns t: rb_at(node);
                        decreases c;
                        invariant t.model != RbTree::Empty;
                        invariant rb_ctx_linked(t.model, c.model) == 1;
                        invariant rb_list_ends_with(rb_inorder(t.model), old(node)) == 1;
                        invariant plug(c.model, t.model) == plug(old(c.model), old(t.model));

                        initialize by simp;
                        preserve by {
                            match t.model {
                                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                                RbTree::Node(identity, par, color, left_model, right_model) => {
                                    have ctx_node_is(c.model, par) == 1 by {
                                        apply(rb_ctx_linked_node(identity, par, color,
                                                left_model, right_model, c.model));
                                        rewrite(ctx_node_is(c.model,
                                                par) == rb_ctx_linked(RbTree::Node(identity,
                                                    par, color, left_model, right_model),
                                                c.model));
                                        rewrite(RbTree::Node(identity, par, color, left_model,
                                                right_model) == t.model);
                                        assumption();
                                    }
                                    have rb_list_ends_with(rb_inorder(RbTree::Node(identity,
                                                par, color, left_model, right_model)),
                                        old(node)) == 1 by {
                                        rewrite(RbTree::Node(identity, par, color, left_model,
                                                right_model) == t.model);
                                        assumption();
                                    }
                                    have plug(c.model, RbTree::Node(identity, par, color,
                                            left_model, right_model)) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(RbTree::Node(identity, par, color, left_model,
                                                right_model) == t.model);
                                        assumption();
                                    }
                                    have rb_ctx_linked(RbTree::Node(identity, par, color,
                                            left_model, right_model), c.model) == 1 by {
                                        rewrite(RbTree::Node(identity, par, color, left_model,
                                                right_model) == t.model);
                                        assumption();
                                    }
                                    let { left: l, right: r } = unfold(t);
                                    step();
                                    step();
                                    step();
                                    have parent == par;
                                    have par == parent by {
                                        rewrite(parent == par);
                                        normalize();
                                    }
                                    let t = fold(rb_at(node), { model: RbTree::Node(identity,
                                                par, color, left_model, right_model) },
                                        { left: l, right: r });
                                    have rb_list_ends_with(rb_inorder(t.model),
                                        old(node)) == 1 by {
                                        rewrite(t.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        assumption();
                                    }
                                    have plug(c.model, t.model) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(t.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        assumption();
                                    }
                                    have rb_ctx_linked(t.model, c.model) == 1 by {
                                        rewrite(t.model == RbTree::Node(identity, par, color,
                                                left_model, right_model));
                                        assumption();
                                    }
                                    have ctx_node_is(c.model, parent) == 1 by {
                                        apply(ctx_node_is_same(c.model, par, parent)) using {
                                            ctx_node_is(c.model, par) == 1;
                                            par == parent;
                                        }
                                        assumption();
                                    }
                                    match c.model {
                                        Context::Top => {
                                            have ctx_is_right(c.model) == 0 by {
                                                rewrite(c.model == Context::Top);
                                                unfold(ctx_is_right(Context::Top));
                                                normalize();
                                            }
                                            have ctx_node_is(Context::Top, parent) == 1 by {
                                                rewrite(Context::Top == c.model);
                                                assumption();
                                            }
                                            have parent == 0 by {
                                                apply(ctx_node_is_top(parent)) using {
                                                    ctx_node_is(Context::Top, parent) == 1;
                                                }
                                                assumption();
                                            }
                                            step();
                                            step();
                                        },
                                        Context::Left(frame_identity, frame_parent, frame_color,
                                            frame_right, above) => {
                                            have ctx_node_is(Context::Left(frame_identity,
                                                    frame_parent, frame_color, frame_right,
                                                    above), parent) == 1 by {
                                                rewrite(Context::Left(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above) == c.model);
                                                assumption();
                                            }
                                            have frame_identity == parent by {
                                                apply(ctx_node_is_left(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above, parent)) using {
                                                    ctx_node_is(Context::Left(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_right, above), parent) == 1;
                                                }
                                                assumption();
                                            }
                                            have ctx_is_right(Context::Left(frame_identity,
                                                    frame_parent, frame_color, frame_right,
                                                    above)) == 0 by {
                                                unfold(ctx_is_right(Context::Left(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_right, above)));
                                                normalize();
                                            }
                                            have plug(Context::Left(frame_identity,
                                                    frame_parent, frame_color, frame_right,
                                                    above), t.model) == plug(old(c.model),
                                                old(t.model)) by {
                                                rewrite(Context::Left(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above) == c.model);
                                                assumption();
                                            }
                                            have rb_ctx_linked(t.model,
                                                Context::Left(frame_identity, frame_parent,
                                                    frame_color, frame_right, above)) == 1 by {
                                                rewrite(Context::Left(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above) == c.model);
                                                assumption();
                                            }
                                            let { sibling: s, up: u } = unfold(c);
                                            match s.model {
                                                RbTree::Empty => {
                                                    unfold(s);
                                                    have parent->rb_right == 0;
                                                    have node != parent->rb_right;
                                                    let s = fold(rb_at(parent->rb_right),
                                                        { model: RbTree::Empty });
                                                    step();
                                                    let c = fold(ctx_at(node),
                                                        { model: Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above) },
                                                        { sibling: s, up: u });
                                                    have ctx_node_is(c.model, parent) == 1 by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    have ctx_is_right(c.model) == 0 by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    have plug(c.model,
                                                        t.model) == plug(old(c.model),
                                                        old(t.model)) by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    have rb_ctx_linked(t.model,
                                                        c.model) == 1 by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    step();
                                                },
                                                RbTree::Node(sibling_identity, sibling_parent,
                                                    sibling_color, sibling_left,
                                                    sibling_right) => {
                                                    let { left: node_l,
                                                            right: node_r } = unfold(t);
                                                    let { left: sibling_l,
                                                            right: sibling_r } = unfold(s);
                                                    step();
                                                    let s = fold(rb_at(parent->rb_right),
                                                        { model: frame_right },
                                                        { left: sibling_l, right: sibling_r });
                                                    let t = fold(rb_at(node),
                                                        { model: RbTree::Node(identity, par,
                                                                color, left_model,
                                                                right_model) }, { left: node_l,
                                                            right: node_r });
                                                    let c = fold(ctx_at(node),
                                                        { model: Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above) },
                                                        { sibling: s, up: u });
                                                    have ctx_node_is(c.model, parent) == 1 by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    have ctx_is_right(c.model) == 0 by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    have plug(c.model,
                                                        t.model) == plug(old(c.model),
                                                        old(t.model)) by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    have rb_ctx_linked(t.model,
                                                        c.model) == 1 by {
                                                        rewrite(c.model
                                                            == Context::Left(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        assumption();
                                                    }
                                                    step();
                                                },
                                            }
                                        },
                                        Context::Right(frame_identity, frame_parent,
                                            frame_color, frame_left, above) => {
                                            have ctx_node_is(Context::Right(frame_identity,
                                                    frame_parent, frame_color, frame_left,
                                                    above), parent) == 1 by {
                                                rewrite(Context::Right(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above) == c.model);
                                                assumption();
                                            }
                                            have frame_identity == parent by {
                                                apply(ctx_node_is_right(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above, parent)) using {
                                                    ctx_node_is(Context::Right(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, above), parent) == 1;
                                                }
                                                assumption();
                                            }
                                            have rb_ctx_linked(RbTree::Node(identity, par,
                                                    color, left_model, right_model),
                                                Context::Right(frame_identity, frame_parent,
                                                    frame_color, frame_left, above)) == 1 by {
                                                rewrite(Context::Right(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above) == c.model);
                                                assumption();
                                            }
                                            have rb_parent_is(RbTree::Node(identity, par, color,
                                                    left_model, right_model),
                                                frame_identity) == 1 by {
                                                apply(rb_ctx_linked_right_parent(RbTree::Node(identity,
                                                            par, color, left_model,
                                                            right_model), frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above)) using {
                                                    rb_ctx_linked(RbTree::Node(identity, par,
                                                            color, left_model, right_model),
                                                        Context::Right(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, above)) == 1;
                                                }
                                                assumption();
                                            }
                                            have rb_parent_is(RbTree::Node(identity, par, color,
                                                    left_model, right_model), parent) == 1 by {
                                                apply(rb_parent_is_same(RbTree::Node(identity,
                                                            par, color, left_model,
                                                            right_model), frame_identity,
                                                        parent)) using {
                                                    rb_parent_is(RbTree::Node(identity, par,
                                                            color, left_model, right_model),
                                                        frame_identity) == 1;
                                                    frame_identity == parent;
                                                }
                                                assumption();
                                            }
                                            have rb_list_ends_with(rb_inorder(RbTree::Node(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        RbTree::Node(identity, par, color,
                                                            left_model, right_model))),
                                                old(node)) == 1 by {
                                                apply(rb_inorder_last_through_right(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        RbTree::Node(identity, par, color,
                                                            left_model, right_model),
                                                        old(node))) using {
                                                    rb_list_ends_with(rb_inorder(RbTree::Node(identity,
                                                                par, color, left_model,
                                                                right_model)), old(node)) == 1;
                                                }
                                                assumption();
                                            }
                                            have plug(above, RbTree::Node(frame_identity,
                                                    frame_parent, frame_color, frame_left,
                                                    RbTree::Node(identity, par, color,
                                                        left_model,
                                                        right_model))) == plug(old(c.model),
                                                old(t.model)) by {
                                                unfold(plug(Context::Right(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, above),
                                                        RbTree::Node(identity, par, color,
                                                            left_model, right_model)));
                                                rewrite(plug(above, RbTree::Node(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, RbTree::Node(identity,
                                                                par, color, left_model,
                                                                right_model)))
                                                    == plug(Context::Right(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, above),
                                                        RbTree::Node(identity, par, color,
                                                            left_model, right_model)));
                                                rewrite(Context::Right(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above) == c.model);
                                                assumption();
                                            }
                                            let { sibling: s, up: u } = unfold(c);
                                            have rb_ctx_linked(RbTree::Node(frame_identity,
                                                    frame_parent, frame_color, frame_left,
                                                    RbTree::Node(identity, par, color,
                                                        left_model, right_model)),
                                                above) == 1 by {
                                                unfold(rb_ctx_linked(RbTree::Node(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, RbTree::Node(identity,
                                                                par, color, left_model,
                                                                right_model)), above));
                                                assumption();
                                            }
                                            step();
                                            step();
                                            step();
                                            let lifted = fold(rb_at(node),
                                                { model: RbTree::Node(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        RbTree::Node(identity, par, color,
                                                            left_model, right_model)) },
                                                { left: s, right: t });
                                            close_invariants();
                                        },
                                    }
                                },
                            }
                        }
                    }
                    match c.model {
                        Context::Top => {
                            have ctx_node_is(Context::Top, parent) == 1 by {
                                rewrite(Context::Top == c.model);
                                assumption();
                            }
                            have parent == 0 by {
                                apply(ctx_node_is_top(parent)) using {
                                    ctx_node_is(Context::Top, parent) == 1;
                                }
                                assumption();
                            }
                            have plug(Context::Top, t.model) == plug(old(c.model),
                                old(t.model)) by {
                                rewrite(Context::Top == c.model);
                                assumption();
                            }
                            have plug(Context::Top, t.model) == t.model by {
                                unfold(plug(Context::Top, t.model));
                                normalize();
                            }
                            have t.model == plug(old(c.model), old(t.model)) by {
                                rewrite(t.model == plug(Context::Top, t.model));
                                assumption();
                            }
                            have rb_remainder_tree(Remainder::Whole(node, t.model)) == t.model by {
                                unfold(rb_remainder_tree(Remainder::Whole(node, t.model)));
                                normalize();
                            }
                            have rb_remainder_tree(Remainder::Whole(node, t.model))
                                == plug(old(c.model), old(t.model)) by {
                                rewrite(rb_remainder_tree(Remainder::Whole(node, t.model))
                                    == t.model);
                                assumption();
                            }
                            have rb_list_ends_with(rb_inorder(plug(old(c.model), old(t.model))),
                                old(node)) == 1 by {
                                rewrite(plug(old(c.model), old(t.model)) == t.model);
                                assumption();
                            }
                            unfold(c);
                            let ctx = fold(ctx_at(parent), { model: Context::Top });
                            let sub = fold(rb_at(parent), { model: RbTree::Empty });
                            let rest = fold(rb_remainder_at(parent),
                                { model: Remainder::Whole(node, t.model) }, { whole: t });
                            step();
                            simp();
                        },
                        Context::Left(frame_identity, frame_parent, frame_color, frame_right,
                            above) => {
                            have ctx_node_is(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above), parent) == 1 by {
                                rewrite(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above) == c.model);
                                assumption();
                            }
                            have frame_identity == parent by {
                                apply(ctx_node_is_left(frame_identity, frame_parent, frame_color,
                                        frame_right, above, parent)) using {
                                    ctx_node_is(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above), parent) == 1;
                                }
                                assumption();
                            }
                            have rb_ctx_linked(t.model, Context::Left(frame_identity, frame_parent, frame_color, frame_right, above)) == 1 by {
                                rewrite(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above) == c.model);
                                assumption();
                            }
                            have rb_parent_is(t.model, frame_identity) == 1 by {
                                apply(rb_ctx_linked_left_parent(t.model, frame_identity,
                                        frame_parent, frame_color, frame_right, above)) using {
                                    rb_ctx_linked(t.model, Context::Left(frame_identity, frame_parent, frame_color, frame_right, above)) == 1;
                                }
                                assumption();
                            }
                            have rb_parent_is(t.model, parent) == 1 by {
                                apply(rb_parent_is_same(t.model, frame_identity, parent)) using {
                                    rb_parent_is(t.model, frame_identity) == 1;
                                    frame_identity == parent;
                                }
                                assumption();
                            }
                            have plug(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above), t.model) == plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right)) by {
                                unfold(plug(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above), t.model));
                                normalize();
                            }
                            have plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right)) == plug(old(c.model), old(t.model)) by {
                                rewrite(plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right)) == plug(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above), t.model));
                                rewrite(Context::Left(frame_identity, frame_parent, frame_color, frame_right, above) == c.model);
                                assumption();
                            }
                            have rb_list_adjacent(rb_inorder(RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right)), old(node), parent) == 1 by {
                                apply(rb_inorder_adjacent_above(frame_identity, frame_parent,
                                        frame_color, t.model, frame_right, old(node), parent)) using {
                                    rb_list_ends_with(rb_inorder(t.model), old(node)) == 1;
                                    parent == frame_identity;
                                }
                                assumption();
                            }
                            have rb_list_adjacent(rb_inorder(plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right))), old(node), parent) == 1 by {
                                apply(plug_keeps_adjacent(above, RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right), old(node), parent)) using {
                                    rb_list_adjacent(rb_inorder(RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right)), old(node), parent) == 1;
                                }
                                assumption();
                            }
                            have rb_list_adjacent(rb_inorder(plug(old(c.model), old(t.model))), old(node),
                                parent) == 1 by {
                                rewrite(plug(old(c.model), old(t.model)) == plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, t.model, frame_right)));
                                assumption();
                            }
                            match t.model {
                                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                                RbTree::Node(top_identity, top_parent, top_color, top_left, top_right) => {
                                    have plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right)) == plug(old(c.model), old(t.model)) by {
                                        rewrite(RbTree::Node(top_identity, top_parent, top_color, top_left, top_right) == t.model);
                                        assumption();
                                    }
                        have rb_parent_is(RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), parent) == 1 by {
                            rewrite(RbTree::Node(top_identity, top_parent, top_color, top_left, top_right) == t.model);
                            assumption();
                        }
                                    let { sibling: s, up: u } = unfold(c);
                                    have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right), above) == 1 by {
                                        apply(rb_ctx_linked_node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right),
                                                frame_right, above));
                                        rewrite(rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right), above) == ctx_node_is(above, frame_parent));
                                        assumption();
                                    }
                                    match u.model {
                                        Context::Top => {
                                            have plug(Context::Top, RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right)) == plug(old(c.model), old(t.model)) by {
                                                rewrite(Context::Top == u.model);
                                                rewrite(u.model == above);
                                                assumption();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right), Context::Top) == 1 by {
                                                rewrite(Context::Top == u.model);
                                                rewrite(u.model == above);
                                                assumption();
                                            }
                                            unfold(u);
                                            let ctx = fold(ctx_at(parent), { model: Context::Top });
                                            let sub = fold(rb_at(parent), { model: RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right) }, { left: t, right: s });
                                            let rest = fold(rb_remainder_at(parent), { model: Remainder::More });
                                            have plug(ctx.model, sub.model) == plug(old(c.model), old(t.model)) by {
                                                rewrite(ctx.model == Context::Top);
                                                rewrite(sub.model == RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right));
                                                assumption();
                                            }
                                            have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                                rewrite(ctx.model == Context::Top);
                                                rewrite(sub.model == RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right));
                                                assumption();
                                            }
                                            step();
                                            simp();
                                        },
                                        Context::Left(up_identity, up_parent, up_color, up_sibling, up_above) => {
                                            have plug(Context::Left(up_identity, up_parent, up_color, up_sibling, up_above), RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right)) == plug(old(c.model), old(t.model)) by {
                                                rewrite(Context::Left(up_identity, up_parent, up_color, up_sibling, up_above) == u.model);
                                                rewrite(u.model == above);
                                                assumption();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right), Context::Left(up_identity, up_parent, up_color, up_sibling, up_above)) == 1 by {
                                                rewrite(Context::Left(up_identity, up_parent, up_color, up_sibling, up_above) == u.model);
                                                rewrite(u.model == above);
                                                assumption();
                                            }
                                            let { sibling: up_s, up: up_u } = unfold(u);
                                            let ctx = fold(ctx_at(parent), { model: Context::Left(up_identity, up_parent, up_color, up_sibling, up_above) },
                                                { sibling: up_s, up: up_u });
                                            let sub = fold(rb_at(parent), { model: RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right) }, { left: t, right: s });
                                            let rest = fold(rb_remainder_at(parent), { model: Remainder::More });
                                            have plug(ctx.model, sub.model) == plug(old(c.model), old(t.model)) by {
                                                rewrite(ctx.model == Context::Left(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model == RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right));
                                                assumption();
                                            }
                                            have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                                rewrite(ctx.model == Context::Left(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model == RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right));
                                                assumption();
                                            }
                                            step();
                                            simp();
                                        },
                                        Context::Right(up_identity, up_parent, up_color, up_sibling, up_above) => {
                                            have plug(Context::Right(up_identity, up_parent, up_color, up_sibling, up_above), RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right)) == plug(old(c.model), old(t.model)) by {
                                                rewrite(Context::Right(up_identity, up_parent, up_color, up_sibling, up_above) == u.model);
                                                rewrite(u.model == above);
                                                assumption();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right), Context::Right(up_identity, up_parent, up_color, up_sibling, up_above)) == 1 by {
                                                rewrite(Context::Right(up_identity, up_parent, up_color, up_sibling, up_above) == u.model);
                                                rewrite(u.model == above);
                                                assumption();
                                            }
                                            let { sibling: up_s, up: up_u } = unfold(u);
                                            let ctx = fold(ctx_at(parent), { model: Context::Right(up_identity, up_parent, up_color, up_sibling, up_above) },
                                                { sibling: up_s, up: up_u });
                                            let sub = fold(rb_at(parent), { model: RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right) }, { left: t, right: s });
                                            let rest = fold(rb_remainder_at(parent), { model: Remainder::More });
                                            have plug(ctx.model, sub.model) == plug(old(c.model), old(t.model)) by {
                                                rewrite(ctx.model == Context::Right(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model == RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right));
                                                assumption();
                                            }
                                            have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                                rewrite(ctx.model == Context::Right(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model == RbTree::Node(frame_identity, frame_parent, frame_color, RbTree::Node(top_identity, top_parent, top_color, top_left, top_right), frame_right));
                                                assumption();
                                            }
                                            step();
                                            simp();
                                        },
                                    }
                                },
                            }
                        },
                        Context::Right(frame_identity, frame_parent, frame_color, frame_left,
                            above) => {
                            have ctx_is_right(Context::Right(frame_identity, frame_parent,
                                    frame_color, frame_left, above)) == 0 by {
                                rewrite(Context::Right(frame_identity, frame_parent,
                                        frame_color, frame_left, above) == c.model);
                                assumption();
                            }
                            have ctx_is_right(Context::Right(frame_identity, frame_parent,
                                    frame_color, frame_left, above)) != 1 by {
                                rewrite(ctx_is_right(Context::Right(frame_identity,
                                        frame_parent, frame_color, frame_left, above)) == 0);
                                normalize();
                            }
                            have ctx_is_right(Context::Right(frame_identity, frame_parent,
                                    frame_color, frame_left, above)) == 1 by {
                                unfold(ctx_is_right(Context::Right(frame_identity,
                                            frame_parent, frame_color, frame_left, above)));
                                normalize();
                            }
                            contradiction(ctx_is_right(Context::Right(frame_identity,
                                        frame_parent, frame_color, frame_left, above)) == 1);
                        },
                    }
                },
            }
        },
    }
}
```

```expect
fail: `ensures result != 0 implies plug(ctx.model, sub.model) == old(t.model)` failed
```
