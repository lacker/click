# `rb_prev` does not hand back the entry subtree alone

This is [`rb_prev.md`](rb_prev.md) with one clause changed, the mirror of
[`rb_next_rejects_a_dropped_context.md`](rb_next_rejects_a_dropped_context.md).
The contract claims that the frame and the subtree produced at the result
rebuild `old(t.model)` rather than the whole entry tree. The descent's first
frame is folded over the entry context, so the claim holds only under `Top`,
and the changed clause is refused at the descent's `return`.

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

```c filename=rb_prev.c
#include "rbtree.h"

struct rb_node *rb_prev(struct rb_node *node)
{
	struct rb_node *parent;

	if (RB_EMPTY_NODE(node))
		return NULL;

	/*
	 * If we have a left-hand child, go down and then right as far
	 * as we can.
	 */
	if (node->rb_left) {
		node = node->rb_left;
		while (node->rb_right)
			node = node->rb_right;
		return (struct rb_node *)node;
	}

	/*
	 * No left-hand children. Go up till we find an ancestor which
	 * is a right-hand child of its parent.
	 */
	while ((parent = rb_parent(node)) && node == parent->rb_left)
		node = parent;

	return parent;
}
```

```click
verifying "rb_prev.c";

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
            list::append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))),
    }
}

function rb_list_starts_with<T>(xs: List<T>, value: T) -> int32 {
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) => if value == head { 1 } else { 0 },
    }
}

function rb_list_ends_with<T>(xs: List<T>, value: T) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) =>
            if tail == List<T>::Nil {
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

theorem list_starts_with_append<T>(xs: List<T>, ys: List<T>,
                                value: T) {
    requires rb_list_starts_with(xs, value) != 0;
    ensures rb_list_starts_with(list::append(xs, ys), value) == 1 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                have rb_list_starts_with(List<T>::Nil, value) == 0 by {
                    unfold(rb_list_starts_with(List<T>::Nil, value));
                    close();
                }
                contradiction(rb_list_starts_with(List<T>::Nil, value) == 0);
            }
            List::Cons(head, tail) => {
                have rb_list_starts_with(List<T>::Cons(head, tail), value)
                    == if value == head { 1 } else { 0 } by {
                    unfold(rb_list_starts_with(List<T>::Cons(head, tail), value));
                    close();
                }
                if value == head {
                    have list::append(List<T>::Cons(head, tail), ys)
                        == List<T>::Cons(head, list::append(tail, ys)) by {
                        unfold(list::append(List<T>::Cons(head, tail), ys));
                        close();
                    }
                    have rb_list_starts_with(
                            List<T>::Cons(head, list::append(tail, ys)),
                            value) == 1 by {
                        unfold(rb_list_starts_with(
                            List<T>::Cons(head, list::append(tail, ys)), value));
                        close();
                    }
                    rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                    close();
                } else {
                    have rb_list_starts_with(List<T>::Cons(head, tail),
                                             value) == 0 by {
                        rewrite(rb_list_starts_with(List<T>::Cons(head, tail), value), if value == head { 1 } else { 0 });
                        close();
                    }
                    contradiction(rb_list_starts_with(
                        List<T>::Cons(head, tail), value) == 0);
                }
            }
        }
    }
}

theorem list_ends_with_is_nonempty<T>(xs: List<T>, value: T) {
    requires rb_list_ends_with(xs, value) != 0;
    ensures xs != List<T>::Nil by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                have rb_list_ends_with(List<T>::Nil, value) == 0 by {
                    unfold(rb_list_ends_with(List<T>::Nil, value));
                    close();
                }
                contradiction(rb_list_ends_with(List<T>::Nil, value) == 0);
            }
            List::Cons(head, tail) => {
                close();
            }
        }
    }
}

theorem list_ends_with_cons_nonempty<T>(head: T,
                                     tail: List<T>,
                                     value: T) {
    requires tail != List<T>::Nil;
    ensures rb_list_ends_with(List<T>::Cons(head, tail), value)
        == rb_list_ends_with(tail, value) by {
        unfold(rb_list_ends_with(List<T>::Cons(head, tail), value));
        close();
    }
}

theorem list_ends_with_append<T>(xs: List<T>, ys: List<T>,
                              value: T) {
    requires rb_list_ends_with(ys, value) == 1;
    ensures rb_list_ends_with(list::append(xs, ys), value) == 1 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                close();
            }
            List::Cons(head, tail) => {
                apply(ih(tail, ys, value));
                have rb_list_ends_with(list::append(tail, ys), value) != 0 by {
                    rewrite(rb_list_ends_with(list::append(tail, ys), value), 1);
                    close();
                }
                apply(list_ends_with_is_nonempty(list::append(tail, ys), value));
                apply(list_ends_with_cons_nonempty(head, list::append(tail, ys), value));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                rewrite(rb_list_ends_with(
                        List<T>::Cons(head, list::append(tail, ys)), value), rb_list_ends_with(list::append(tail, ys), value));
                close();
            }
        }
    }
}

theorem rb_inorder_first_at_leftmost(tree: RbTree, node: struct rb_node*) {
    requires rb_left(tree) == RbTree::Empty;
    requires rb_identity_is(tree, node) == 1;
    ensures rb_list_starts_with(rb_inorder(tree), node) == 1 by {
        let ih = induct(tree);
        match tree {
            RbTree::Empty => {
                have rb_identity_is(RbTree::Empty, node) != 0 by {
                    rewrite(rb_identity_is(RbTree::Empty, node), 1);
                    close();
                }
                have rb_identity_is(RbTree::Empty, node) == 0 by {
                    unfold(rb_identity_is(RbTree::Empty, node));
                    close();
                }
                contradiction(rb_identity_is(RbTree::Empty, node) == 0);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                have rb_left(RbTree::Node(identity, parent, color, left, right)) == left by {
                    unfold(rb_left(RbTree::Node(identity, parent, color, left, right)));
                    close();
                }
                have left == RbTree::Empty by {
                    rewrite(left, rb_left(RbTree::Node(identity, parent, color, left, right)));
                    close();
                }

                have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                    == if node == identity { 1 } else { 0 } by {
                    unfold(rb_identity_is(
                        RbTree::Node(identity, parent, color, left, right), node));
                    close();
                }
                if node == identity {
                    have rb_inorder(RbTree::Node(identity, parent, color, RbTree::Empty, right))
                        == list::append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))) by {
                        unfold(rb_inorder(
                            RbTree::Node(identity, parent, color, RbTree::Empty, right)));
                        unfold(rb_inorder(RbTree::Empty));
                        close();
                    }
                    have list::append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)))
                        == List<struct rb_node*>::Cons(identity, rb_inorder(right)) by {
                        unfold(list::append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))));
                        close();
                    }
                    have rb_list_starts_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)),
                            node) == 1 by {
                        unfold(rb_list_starts_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(right)), node));
                        close();
                    }
                    rewrite(left, RbTree::Empty);
                    rewrite(rb_inorder(RbTree::Node(identity, parent, color, RbTree::Empty, right)), list::append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))));
                    rewrite(list::append(List<struct rb_node*>::Nil,
                            List<struct rb_node*>::Cons(identity, rb_inorder(right))), List<struct rb_node*>::Cons(identity, rb_inorder(right)));
                    close();
                } else {
                    have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                        == 0 by {
                        rewrite(rb_identity_is(
                                RbTree::Node(identity, parent, color, left, right), node), if node == identity { 1 } else { 0 });
                        close();
                    }
                    have rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node) != 0 by {
                        rewrite(rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node), 1);
                        close();
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
        let ih = induct(tree);
        match tree {
            RbTree::Empty => {
                have rb_identity_is(RbTree::Empty, node) != 0 by {
                    rewrite(rb_identity_is(RbTree::Empty, node), 1);
                    close();
                }
                have rb_identity_is(RbTree::Empty, node) == 0 by {
                    unfold(rb_identity_is(RbTree::Empty, node));
                    close();
                }
                contradiction(rb_identity_is(RbTree::Empty, node) == 0);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                have rb_right(RbTree::Node(identity, parent, color, left, right)) == right by {
                    unfold(rb_right(RbTree::Node(identity, parent, color, left, right)));
                    close();
                }
                have right == RbTree::Empty by {
                    rewrite(right, rb_right(
                        RbTree::Node(identity, parent, color, left, right)));
                    close();
                }

                have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                    == if node == identity { 1 } else { 0 } by {
                    unfold(rb_identity_is(
                        RbTree::Node(identity, parent, color, left, right), node));
                    close();
                }
                if node == identity {
                    have rb_inorder(RbTree::Node(identity, parent, color, left, RbTree::Empty))
                        == list::append(rb_inorder(left),
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil)) by {
                        unfold(rb_inorder(
                            RbTree::Node(identity, parent, color, left, RbTree::Empty)));
                        unfold(rb_inorder(RbTree::Empty));
                        close();
                    }
                    have rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil), node) == 1 by {
                        unfold(rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil), node));
                        close();
                    }
                    have rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil), node) != 0 by {
                        rewrite(rb_list_ends_with(
                                List<struct rb_node*>::Cons(identity,
                                    List<struct rb_node*>::Nil), node), 1);
                        close();
                    }
                    apply(list_ends_with_append(rb_inorder(left),
                        List<struct rb_node*>::Cons(identity,
                            List<struct rb_node*>::Nil), node));
                    rewrite(right, RbTree::Empty);
                    rewrite(rb_inorder(
                            RbTree::Node(identity, parent, color, left, RbTree::Empty)), list::append(rb_inorder(left),
                            List<struct rb_node*>::Cons(identity,
                                List<struct rb_node*>::Nil)));
                    close();
                } else {
                    have rb_identity_is(RbTree::Node(identity, parent, color, left, right), node)
                        == 0 by {
                        rewrite(rb_identity_is(
                                RbTree::Node(identity, parent, color, left, right), node), if node == identity { 1 } else { 0 });
                        close();
                    }
                    have rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node) != 0 by {
                        rewrite(rb_identity_is(
                            RbTree::Node(identity, parent, color, left, right), node), 1);
                        close();
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
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                close();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_left(Context::Left(identity, grandparent, color, sibling_model,
                                                up_model)) == ctx_all_left(up_model) by {
                    unfold(ctx_all_left(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model)));
                    close();
                }
                have ctx_all_left(up_model) == 1 by {
                    rewrite(ctx_all_left(up_model), ctx_all_left(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model)));
                    close();
                }
                have rb_inorder(RbTree::Node(identity, grandparent, color, sub, sibling_model))
                    == list::append(rb_inorder(sub),
                        List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sub, sibling_model)));
                    close();
                }
                have rb_list_starts_with(rb_inorder(sub), node) != 0 by {
                    rewrite(rb_list_starts_with(rb_inorder(sub), node), 1);
                    close();
                }
                apply(list_starts_with_append(rb_inorder(sub),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model)), node));
                have rb_list_starts_with(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sub,
                                                sibling_model)), node) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sub, sibling_model)), list::append(rb_inorder(sub),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))));
                    close();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sub, sibling_model), node));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                            sub));
                close();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_left(Context::Right(identity, grandparent, color, sibling_model,
                                                 up_model)) != 0 by {
                    rewrite(ctx_all_left(Context::Right(identity, grandparent, color,
                                                        sibling_model, up_model)), 1);
                    close();
                }
                have ctx_all_left(Context::Right(identity, grandparent, color, sibling_model,
                                                 up_model)) == 0 by {
                    unfold(ctx_all_left(Context::Right(identity, grandparent, color,
                                                       sibling_model, up_model)));
                    close();
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
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                close();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_right(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model)) != 0 by {
                    rewrite(ctx_all_right(Context::Left(identity, grandparent, color,
                                                        sibling_model, up_model)), 1);
                    close();
                }
                have ctx_all_right(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model)) == 0 by {
                    unfold(ctx_all_right(Context::Left(identity, grandparent, color,
                                                       sibling_model, up_model)));
                    close();
                }
                contradiction(ctx_all_right(Context::Left(identity, grandparent, color,
                                                          sibling_model, up_model)) == 0);
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_all_right(Context::Right(identity, grandparent, color, sibling_model,
                                                  up_model)) == ctx_all_right(up_model) by {
                    unfold(ctx_all_right(Context::Right(identity, grandparent, color,
                                                        sibling_model, up_model)));
                    close();
                }
                have ctx_all_right(up_model) == 1 by {
                    rewrite(ctx_all_right(up_model), ctx_all_right(Context::Right(identity, grandparent, color,
                                                        sibling_model, up_model)));
                    close();
                }
                have rb_list_ends_with(rb_inorder(sub), node) != 0 by {
                    rewrite(rb_list_ends_with(rb_inorder(sub), node), 1);
                    close();
                }
                apply(list_ends_with_is_nonempty(rb_inorder(sub), node));
                apply(list_ends_with_cons_nonempty(identity, rb_inorder(sub), node));
                have rb_list_ends_with(
                        List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node) == 1 by {
                    rewrite(rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node), rb_list_ends_with(rb_inorder(sub), node));
                    close();
                }
                have rb_list_ends_with(
                        List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node) != 0 by {
                    rewrite(rb_list_ends_with(
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node), 1);
                    close();
                }
                apply(list_ends_with_append(rb_inorder(sibling_model),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sub)), node));
                have rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, sub))
                    == list::append(rb_inorder(sibling_model),
                        List<struct rb_node*>::Cons(identity, rb_inorder(sub))) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sibling_model, sub)));
                    close();
                }
                have rb_list_ends_with(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, sub)),
                        node) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sibling_model, sub)), list::append(rb_inorder(sibling_model),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub))));
                    close();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sibling_model, sub), node));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                            sub));
                close();
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

function rb_list_pair_at<T>(head: T, tail: List<T>,
                         first: T, second: T) -> int32 {
    if rb_list_starts_with(tail, second) == 1 {
        if first == head { 1 } else { 0 }
    } else {
        0
    }
}

function rb_list_adjacent<T>(xs: List<T>, first: T,
                          second: T) -> int32
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

theorem list_adjacent_here<T>(head: T, tail: List<T>,
                           first: T, second: T) {
    requires first == head;
    requires rb_list_starts_with(tail, second) == 1;
    ensures rb_list_adjacent(List<T>::Cons(head, tail), first, second) == 1 by {
        have rb_list_pair_at(head, tail, first, second) == 1 by {
            unfold(rb_list_pair_at(head, tail, first, second));
            have (if first == head { 1 } else { 0 }) == 1 by close();
            rewrite((if first == head { 1 } else { 0 }), 1);
            close();
        }
        unfold(rb_list_adjacent(List<T>::Cons(head, tail), first, second));
        close();
    }
}

theorem list_adjacent_cons<T>(head: T, tail: List<T>,
                           first: T, second: T) {
    requires rb_list_adjacent(tail, first, second) == 1;
    ensures rb_list_adjacent(List<T>::Cons(head, tail), first, second) == 1 by {
        unfold(rb_list_adjacent(List<T>::Cons(head, tail), first, second));
        if rb_list_pair_at(head, tail, first, second) == 1 {
            close();
        } else {
            have (if rb_list_pair_at(head, tail, first, second) == 1 {
                1
            } else {
                rb_list_adjacent(tail, first, second)
            }) == rb_list_adjacent(tail, first, second) by close();
            rewrite((if rb_list_pair_at(head, tail, first, second) == 1 {
                1
            } else {
                rb_list_adjacent(tail, first, second)
            }), rb_list_adjacent(tail, first, second));
            close();
        }
    }
}

theorem list_adjacent_append_left<T>(xs: List<T>, ys: List<T>,
                                  first: T, second: T) {
    requires rb_list_adjacent(ys, first, second) == 1;
    ensures rb_list_adjacent(list::append(xs, ys), first, second) == 1 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                unfold(list::append(List<T>::Nil, ys));
                close();
            }
            List::Cons(head, tail) => {
                apply(ih(tail, ys, first, second));
                apply(list_adjacent_cons(head, list::append(tail, ys), first, second));
                apply(list::append_cons(head, tail, ys));
                rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                close();
            }
        }
    }
}

theorem list_pair_at_parts<T>(head: T, tail: List<T>,
                           first: T, second: T) {
    requires rb_list_pair_at(head, tail, first, second) == 1;
    ensures rb_list_starts_with(tail, second) == 1 by {
        if rb_list_starts_with(tail, second) == 1 {
            close();
        } else {
            have rb_list_pair_at(head, tail, first, second) == 0 by {
                unfold(rb_list_pair_at(head, tail, first, second));
                close();
            }
            have rb_list_pair_at(head, tail, first, second) != 0 by {
                rewrite(rb_list_pair_at(head, tail, first, second), 1);
                close();
            }
            contradiction(rb_list_pair_at(head, tail, first, second) == 0);
        }
    }
    ensures first == head by {
        if first == head {
            close();
        } else {
            have rb_list_pair_at(head, tail, first, second) == 0 by {
                unfold(rb_list_pair_at(head, tail, first, second));
                have (if first == head { 1 } else { 0 }) == 0 by close();
                rewrite((if first == head { 1 } else { 0 }), 0);
                if rb_list_starts_with(tail, second) == 1 {
                    close();
                } else {
                    close();
                }
            }
            have rb_list_pair_at(head, tail, first, second) != 0 by {
                rewrite(rb_list_pair_at(head, tail, first, second), 1);
                close();
            }
            contradiction(rb_list_pair_at(head, tail, first, second) == 0);
        }
    }
}

theorem list_adjacent_append_right<T>(xs: List<T>, ys: List<T>,
                                   first: T, second: T) {
    requires rb_list_adjacent(xs, first, second) == 1;
    ensures rb_list_adjacent(list::append(xs, ys), first, second) == 1 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                have rb_list_adjacent(List<T>::Nil, first, second) == 0 by {
                    unfold(rb_list_adjacent(List<T>::Nil, first, second));
                    close();
                }
                have rb_list_adjacent(List<T>::Nil, first, second) != 0 by {
                    rewrite(rb_list_adjacent(List<T>::Nil, first, second), 1);
                    close();
                }
                contradiction(rb_list_adjacent(List<T>::Nil, first, second) == 0);
            }
            List::Cons(head, tail) => {
                apply(list::append_cons(head, tail, ys));
                if rb_list_pair_at(head, tail, first, second) == 1 {
                    apply(list_pair_at_parts(head, tail, first, second));
                    have rb_list_starts_with(tail, second) != 0 by {
                        rewrite(rb_list_starts_with(tail, second), 1);
                        close();
                    }
                    apply(list_starts_with_append(tail, ys, second));
                    apply(list_adjacent_here(head, list::append(tail, ys), first, second));
                    rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                    close();
                } else {
                    have rb_list_adjacent(tail, first, second) == 1 by {
                        have rb_list_adjacent(List<T>::Cons(head, tail), first, second)
                            == rb_list_adjacent(tail, first, second) by {
                            unfold(rb_list_adjacent(List<T>::Cons(head, tail),
                                                    first, second));
                            close();
                        }
                        rewrite(rb_list_adjacent(tail, first, second), rb_list_adjacent(List<T>::Cons(head, tail),
                                                first, second));
                        close();
                    }
                    apply(ih(tail, ys, first, second));
                    apply(list_adjacent_cons(head, list::append(tail, ys), first, second));
                    rewrite(list::append(List<T>::Cons(head, tail), ys), List<T>::Cons(head, list::append(tail, ys)));
                    close();
                }
            }
        }
    }
}

theorem list_ends_then_adjacent<T>(xs: List<T>, head: T,
                                ys: List<T>,
                                first: T, second: T) {
    requires rb_list_ends_with(xs, first) == 1;
    requires second == head;
    ensures rb_list_adjacent(
        list::append(xs, List<T>::Cons(head, ys)), first, second) == 1 by {
        let ih = induct(xs);
        match xs {
            List::Nil => {
                have rb_list_ends_with(List<T>::Nil, first) == 0 by {
                    unfold(rb_list_ends_with(List<T>::Nil, first));
                    close();
                }
                have rb_list_ends_with(List<T>::Nil, first) != 0 by {
                    rewrite(rb_list_ends_with(List<T>::Nil, first), 1);
                    close();
                }
                contradiction(rb_list_ends_with(List<T>::Nil, first) == 0);
            }
            List::Cons(front, tail) => {
                apply(list::append_cons(front, tail, List<T>::Cons(head, ys)));
                if tail == List<T>::Nil {
                    have rb_list_ends_with(List<T>::Cons(front, tail), first)
                        == if first == front { 1 } else { 0 } by {
                        unfold(rb_list_ends_with(List<T>::Cons(front, tail), first));
                        close();
                    }
                    if first == front {
                        have rb_list_starts_with(
                                List<T>::Cons(head, ys), second) == 1 by {
                            unfold(rb_list_starts_with(
                                List<T>::Cons(head, ys), second));
                            close();
                        }
                        apply(list_adjacent_here(front,
                            List<T>::Cons(head, ys), first, second));
                        have list::append(List<T>::Nil,
                                List<T>::Cons(head, ys))
                            == List<T>::Cons(head, ys) by {
                            unfold(list::append(List<T>::Nil,
                                List<T>::Cons(head, ys)));
                            close();
                        }
                        rewrite(list::append(List<T>::Cons(front, tail),
                                List<T>::Cons(head, ys)), List<T>::Cons(front, list::append(tail,
                                List<T>::Cons(head, ys))));
                        rewrite(tail, List<T>::Nil);
                        rewrite(list::append(List<T>::Nil,
                                List<T>::Cons(head, ys)), List<T>::Cons(head, ys));
                        close();
                    } else {
                        have rb_list_ends_with(List<T>::Cons(front, tail), first)
                            == 0 by {
                            rewrite(rb_list_ends_with(
                                    List<T>::Cons(front, tail), first), if first == front { 1 } else { 0 });
                            close();
                        }
                        have rb_list_ends_with(List<T>::Cons(front, tail), first)
                            != 0 by {
                            rewrite(rb_list_ends_with(
                                List<T>::Cons(front, tail), first), 1);
                            close();
                        }
                        contradiction(rb_list_ends_with(
                            List<T>::Cons(front, tail), first) == 0);
                    }
                } else {
                    apply(list_ends_with_cons_nonempty(front, tail, first));
                    have rb_list_ends_with(tail, first) == 1 by {
                        rewrite(rb_list_ends_with(tail, first), rb_list_ends_with(List<T>::Cons(front, tail), first));
                        close();
                    }
                    apply(ih(tail, head, ys, first, second));
                    apply(list_adjacent_cons(front,
                        list::append(tail, List<T>::Cons(head, ys)),
                        first, second));
                    rewrite(list::append(List<T>::Cons(front, tail),
                            List<T>::Cons(head, ys)), List<T>::Cons(front, list::append(tail,
                            List<T>::Cons(head, ys))));
                    close();
                }
            }
        }
    }
}

theorem rb_inorder_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                        left: RbTree, right: RbTree) {
    ensures rb_inorder(RbTree::Node(identity, parent, color, left, right))
        == list::append(rb_inorder(left),
            List<struct rb_node*>::Cons(identity, rb_inorder(right))) by {
        unfold(rb_inorder(RbTree::Node(identity, parent, color, left, right)));
        close();
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
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right)), list::append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        close();
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
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right)), list::append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        close();
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
            rewrite(rb_list_ends_with(rb_inorder(right), node), 1);
            close();
        }
        apply(list_ends_with_is_nonempty(rb_inorder(right), node));
        apply(list_ends_with_cons_nonempty(identity, rb_inorder(right), node));
        have rb_list_ends_with(
                List<struct rb_node*>::Cons(identity, rb_inorder(right)), node) == 1 by {
            rewrite(rb_list_ends_with(
                    List<struct rb_node*>::Cons(identity, rb_inorder(right)), node), rb_list_ends_with(rb_inorder(right), node));
            close();
        }
        apply(list_ends_with_append(rb_inorder(left),
            List<struct rb_node*>::Cons(identity, rb_inorder(right)), node));
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right)), list::append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        close();
    }
}

theorem plug_keeps_adjacent(ctx: Context, sub: RbTree,
                            first: struct rb_node*, second: struct rb_node*) {
    requires rb_list_adjacent(rb_inorder(sub), first, second) == 1;
    ensures rb_list_adjacent(rb_inorder(plug(ctx, sub)), first, second) == 1 by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                close();
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
                            RbTree::Node(identity, grandparent, color, sub, sibling_model)), list::append(rb_inorder(sub),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))));
                    close();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sub, sibling_model),
                         first, second));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                            sub));
                close();
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
                            RbTree::Node(identity, grandparent, color, sibling_model, sub)), list::append(rb_inorder(sibling_model),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sub))));
                    close();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sibling_model, sub),
                         first, second));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                            sub));
                close();
            }
        }
    }
}

theorem plug_successor(ctx: Context, sub: RbTree,
                       node: struct rb_node*, next: struct rb_node*) {
    requires ctx_descends_from(ctx, node) == 1;
    requires rb_list_starts_with(rb_inorder(sub), next) == 1;
    ensures rb_list_adjacent(rb_inorder(plug(ctx, sub)), node, next) == 1 by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                have ctx_descends_from(Context::Top, node) == 0 by {
                    unfold(ctx_descends_from(Context::Top, node));
                    close();
                }
                have ctx_descends_from(Context::Top, node) != 0 by {
                    rewrite(ctx_descends_from(Context::Top, node), 1);
                    close();
                }
                contradiction(ctx_descends_from(Context::Top, node) == 0);
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_descends_from(Context::Left(identity, grandparent, color,
                                                     sibling_model, up_model), node)
                    == ctx_descends_from(up_model, node) by {
                    unfold(ctx_descends_from(Context::Left(identity, grandparent, color,
                                                           sibling_model, up_model), node));
                    close();
                }
                have ctx_descends_from(up_model, node) == 1 by {
                    rewrite(ctx_descends_from(up_model, node), ctx_descends_from(Context::Left(identity, grandparent, color,
                                                           sibling_model, up_model), node));
                    close();
                }
                apply(rb_inorder_node(identity, grandparent, color, sub, sibling_model));
                have rb_list_starts_with(rb_inorder(sub), next) != 0 by {
                    rewrite(rb_list_starts_with(rb_inorder(sub), next), 1);
                    close();
                }
                apply(list_starts_with_append(rb_inorder(sub),
                    List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model)), next));
                have rb_list_starts_with(
                        rb_inorder(RbTree::Node(identity, grandparent, color, sub,
                                                sibling_model)), next) == 1 by {
                    rewrite(rb_inorder(
                            RbTree::Node(identity, grandparent, color, sub, sibling_model)), list::append(rb_inorder(sub),
                            List<struct rb_node*>::Cons(identity, rb_inorder(sibling_model))));
                    close();
                }
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sub, sibling_model),
                         node, next));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                            sub));
                close();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_descends_from(Context::Right(identity, grandparent, color,
                                                      sibling_model, up_model), node)
                    == if identity == node { 1 } else { 0 } by {
                    unfold(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                            sibling_model, up_model), node));
                    close();
                }
                if identity == node {
                    have node == identity by {
                        rewrite(identity, node);
                        close();
                    }
                    apply(rb_inorder_adjacent_below(identity, grandparent, color,
                        sibling_model, sub, node, next));
                    apply(plug_keeps_adjacent(up_model,
                        RbTree::Node(identity, grandparent, color, sibling_model, sub),
                        node, next));
                    unfold(plug(Context::Right(identity, grandparent, color, sibling_model,
                                               up_model), sub));
                    close();
                } else {
                    have ctx_descends_from(Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model), node)
                        == 0 by {
                        rewrite(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                                 sibling_model, up_model), node), if identity == node { 1 } else { 0 });
                        close();
                    }
                    have ctx_descends_from(Context::Right(identity, grandparent, color,
                                                          sibling_model, up_model), node)
                        != 0 by {
                        rewrite(ctx_descends_from(Context::Right(identity, grandparent, color,
                                                                 sibling_model, up_model), node), 1);
                        close();
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
            close();
        } else {
            have ctx_node_is(Context::Top, p) == 0 by {
                unfold(ctx_node_is(Context::Top, p));
                close();
            }
            have ctx_node_is(Context::Top, p) != 0 by {
                rewrite(ctx_node_is(Context::Top, p), 1);
                close();
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
            close();
        } else {
            have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                           up_model), p) == 0 by {
                unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model), p));
                close();
            }
            have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                           up_model), p) != 0 by {
                rewrite(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                  up_model), p), 1);
                close();
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
            close();
        } else {
            have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                            up_model), p) == 0 by {
                unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                  up_model), p));
                close();
            }
            have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                            up_model), p) != 0 by {
                rewrite(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                   up_model), p), 1);
                close();
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
        close();
    }
}

theorem rb_parent_is_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                          left: RbTree, right: RbTree, p: struct rb_node*) {
    requires rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) == 1;
    ensures parent == p by {
        if parent == p {
            close();
        } else {
            have rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) == 0 by {
                unfold(rb_parent_is(RbTree::Node(identity, parent, color, left, right), p));
                close();
            }
            have rb_parent_is(RbTree::Node(identity, parent, color, left, right), p) != 0 by {
                rewrite(rb_parent_is(RbTree::Node(identity, parent, color, left, right), p), 1);
                close();
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
        let ih = induct(tree);
        match tree {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, b));
                close();
            }
            RbTree::Node(identity, parent, color, left, right) => {
                apply(rb_parent_is_node(identity, parent, color, left, right, a));
                have parent == b by {
                    rewrite(b, a);
                    close();
                }
                unfold(rb_parent_is(RbTree::Node(identity, parent, color, left, right), b));
                close();
            }
        }
    }
}

theorem ctx_node_is_same(ctx: Context, a: struct rb_node*, b: struct rb_node*) {
    requires ctx_node_is(ctx, a) == 1;
    requires a == b;
    ensures ctx_node_is(ctx, b) == 1 by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                apply(ctx_node_is_top(a));
                have b == 0 by {
                    rewrite(b, a);
                    close();
                }
                unfold(ctx_node_is(Context::Top, b));
                close();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_node_is_left(identity, grandparent, color, sibling_model, up_model, a));
                have identity == b by {
                    rewrite(b, a);
                    close();
                }
                unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                                 up_model), b));
                close();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_node_is_right(identity, grandparent, color, sibling_model, up_model,
                                        a));
                have identity == b by {
                    rewrite(b, a);
                    close();
                }
                unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                  up_model), b));
                close();
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
            rewrite(parent, p);
            close();
        }
        apply(ctx_node_is_same(ctx, p, parent));
        unfold(rb_ctx_linked(RbTree::Node(identity, parent, color, left, right), ctx));
        close();
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
        let ih = induct(tree);
        match tree {
            RbTree::Empty => {
                have rb_ctx_linked(RbTree::Empty, ctx) == 0 by {
                    unfold(rb_ctx_linked(RbTree::Empty, ctx));
                    close();
                }
                have rb_ctx_linked(RbTree::Empty, ctx) != 0 by {
                    rewrite(rb_ctx_linked(RbTree::Empty, ctx), 1);
                    close();
                }
                contradiction(rb_ctx_linked(RbTree::Empty, ctx) == 0);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                close();
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
        let ih = induct(tree);
        match tree {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, identity));
                close();
            }
            RbTree::Node(node, parent, node_color, left, right) => {
                apply(rb_ctx_linked_node(node, parent, node_color, left, right,
                    Context::Left(identity, grandparent, color, sibling_model, up_model)));
                have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model,
                                               up_model), parent) == 1 by {
                    rewrite(ctx_node_is(Context::Left(identity, grandparent, color,
                                                      sibling_model, up_model), parent), rb_ctx_linked(RbTree::Node(node, parent, node_color, left, right),
                            Context::Left(identity, grandparent, color, sibling_model,
                                          up_model)));
                    close();
                }
                apply(ctx_node_is_left(identity, grandparent, color, sibling_model, up_model,
                                       parent));
                have parent == identity by {
                    rewrite(identity, parent);
                    close();
                }
                unfold(rb_parent_is(RbTree::Node(node, parent, node_color, left, right),
                                    identity));
                close();
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
        let ih = induct(tree);
        match tree {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, identity));
                close();
            }
            RbTree::Node(node, parent, node_color, left, right) => {
                apply(rb_ctx_linked_node(node, parent, node_color, left, right,
                    Context::Right(identity, grandparent, color, sibling_model, up_model)));
                have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model,
                                                up_model), parent) == 1 by {
                    rewrite(ctx_node_is(Context::Right(identity, grandparent, color,
                                                       sibling_model, up_model), parent), rb_ctx_linked(RbTree::Node(node, parent, node_color, left, right),
                            Context::Right(identity, grandparent, color, sibling_model,
                                           up_model)));
                    close();
                }
                apply(ctx_node_is_right(identity, grandparent, color, sibling_model, up_model,
                                        parent));
                have parent == identity by {
                    rewrite(identity, parent);
                    close();
                }
                unfold(rb_parent_is(RbTree::Node(node, parent, node_color, left, right),
                                    identity));
                close();
            }
        }
    }
}

function ctx_descends_from_left(ctx: Context, node: struct rb_node*) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if identity == node { 1 } else { 0 },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            ctx_descends_from_left(up_model, node),
    }
}

function ctx_is_left(ctx: Context) -> int32 {
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) => 1,
        Context::Right(identity, grandparent, color, sibling_model, up_model) => 0,
    }
}

theorem rb_inorder_first_through_left(identity: struct rb_node*, parent: struct rb_node*,
                                      color: Color, left: RbTree, right: RbTree,
                                      node: struct rb_node*) {
    requires rb_list_starts_with(rb_inorder(left), node) == 1;
    ensures rb_list_starts_with(
        rb_inorder(RbTree::Node(identity, parent, color, left, right)), node) == 1 by {
        apply(rb_inorder_node(identity, parent, color, left, right));
        have rb_list_starts_with(rb_inorder(left), node) != 0 by {
            rewrite(rb_list_starts_with(rb_inorder(left), node), 1);
            close();
        }
        apply(list_starts_with_append(rb_inorder(left),
            List<struct rb_node*>::Cons(identity, rb_inorder(right)), node));
        rewrite(rb_inorder(RbTree::Node(identity, parent, color, left, right)), list::append(rb_inorder(left),
                List<struct rb_node*>::Cons(identity, rb_inorder(right))));
        close();
    }
}

theorem plug_predecessor(ctx: Context, sub: RbTree,
                         node: struct rb_node*, prev: struct rb_node*) {
    requires ctx_descends_from_left(ctx, node) == 1;
    requires rb_list_ends_with(rb_inorder(sub), prev) == 1;
    ensures rb_list_adjacent(rb_inorder(plug(ctx, sub)), prev, node) == 1 by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                have ctx_descends_from_left(Context::Top, node) == 0 by {
                    unfold(ctx_descends_from_left(Context::Top, node));
                    close();
                }
                have ctx_descends_from_left(Context::Top, node) != 0 by {
                    rewrite(ctx_descends_from_left(Context::Top, node), 1);
                    close();
                }
                contradiction(ctx_descends_from_left(Context::Top, node) == 0);
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_descends_from_left(Context::Right(identity, grandparent, color,
                                                           sibling_model, up_model), node)
                    == ctx_descends_from_left(up_model, node) by {
                    unfold(ctx_descends_from_left(Context::Right(identity, grandparent, color,
                                                                 sibling_model, up_model),
                                                  node));
                    close();
                }
                have ctx_descends_from_left(up_model, node) == 1 by {
                    rewrite(ctx_descends_from_left(up_model, node), ctx_descends_from_left(Context::Right(identity, grandparent, color,
                                                                 sibling_model, up_model),
                                                  node));
                    close();
                }
                apply(rb_inorder_last_through_right(identity, grandparent, color,
                    sibling_model, sub, prev));
                apply(ih(up_model,
                         RbTree::Node(identity, grandparent, color, sibling_model, sub),
                         node, prev));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model,
                                           up_model), sub));
                close();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have ctx_descends_from_left(Context::Left(identity, grandparent, color,
                                                          sibling_model, up_model), node)
                    == if identity == node { 1 } else { 0 } by {
                    unfold(ctx_descends_from_left(Context::Left(identity, grandparent, color,
                                                                sibling_model, up_model),
                                                  node));
                    close();
                }
                if identity == node {
                    have node == identity by {
                        rewrite(identity, node);
                        close();
                    }
                    apply(rb_inorder_adjacent_above(identity, grandparent, color,
                        sub, sibling_model, prev, node));
                    apply(plug_keeps_adjacent(up_model,
                        RbTree::Node(identity, grandparent, color, sub, sibling_model),
                        prev, node));
                    unfold(plug(Context::Left(identity, grandparent, color, sibling_model,
                                              up_model), sub));
                    close();
                } else {
                    have ctx_descends_from_left(Context::Left(identity, grandparent, color,
                                                              sibling_model, up_model), node)
                        == 0 by {
                        rewrite(ctx_descends_from_left(Context::Left(identity, grandparent,
                                                                     color, sibling_model,
                                                                     up_model), node), if identity == node { 1 } else { 0 });
                        close();
                    }
                    have ctx_descends_from_left(Context::Left(identity, grandparent, color,
                                                              sibling_model, up_model), node)
                        != 0 by {
                        rewrite(ctx_descends_from_left(Context::Left(identity, grandparent,
                                                                     color, sibling_model,
                                                                     up_model), node), 1);
                        close();
                    }
                    contradiction(ctx_descends_from_left(Context::Left(identity, grandparent,
                                                                       color, sibling_model,
                                                                       up_model), node)
                        == 0);
                }
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
            fact address(parent) != address(p);
            fact aligned(p, 8);
            fact aligned(parent, 8);
            fact p->__rb_parent_color == address(parent) + (p->__rb_parent_color & 1);
            fact ((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
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
            fact address(grandparent) != address(identity);
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_left == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent;
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
            fact address(grandparent) != address(identity);
            fact aligned(identity, 8);
            fact aligned(grandparent, 8);
            fact identity->rb_right == child;
            fact identity->__rb_parent_color
                == address(grandparent) + (identity->__rb_parent_color & 1);
            fact ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent;
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
struct rb_node* rb_prev(struct rb_node* node) {
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
        rb_list_adjacent(rb_inorder(plug(old(c.model), old(t.model))), result, node) == 1;
    ensures result == 0 implies
        rb_remainder_tree(rest.model) == plug(old(c.model), old(t.model));
    ensures result == 0 implies
        rb_list_starts_with(rb_inorder(plug(old(c.model), old(t.model))), node) == 1;
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(entry_identity, entry_parent, entry_color, entry_right, entry_left) => {
            have ctx_node_is(old(c.model), entry_parent) == 1 by {
                apply(rb_ctx_linked_node(entry_identity, entry_parent, entry_color, entry_right,
                        entry_left, old(c.model)));
                rewrite(ctx_node_is(old(c.model),
                        entry_parent), rb_ctx_linked(RbTree::Node(entry_identity,
                            entry_parent, entry_color, entry_right, entry_left), old(c.model)));
                rewrite(RbTree::Node(entry_identity, entry_parent, entry_color, entry_right,
                        entry_left), t.model);
                close();
            }
            have plug(Context::Left(entry_identity, entry_parent, entry_color, entry_left,
                    old(c.model)), entry_right) == plug(old(c.model), old(t.model)) by {
                unfold(plug(Context::Left(entry_identity, entry_parent, entry_color,
                            entry_left, old(c.model)), entry_right));
                rewrite(RbTree::Node(entry_identity, entry_parent, entry_color, entry_right,
                        entry_left), t.model);
                close();
            }
            let { right: entry_l, left: entry_r } = unfold(t);
            step();
            have address(entry_parent) == (node->__rb_parent_color & ~3) by close() using {
                aligned(entry_parent, 8);
                node->__rb_parent_color == address(entry_parent) + (node->__rb_parent_color & 1);
            };
            have address(node) == (address(node) & ~3) by close() using {
                aligned(node, 8);
            };
            have node->__rb_parent_color != address(node) by {
                if node->__rb_parent_color == address(node) {
                    have address(entry_parent) == address(node) by {
                        rewrite(address(entry_parent), (node->__rb_parent_color & ~3));
                        rewrite(node->__rb_parent_color, address(node));
                        rewrite(address(node), (address(node) & ~3));
                        close();
                    }
                    contradiction(address(entry_parent) == address(node));
                } else {
                    close();
                }
            }
            step();
            match entry_r.model {
                RbTree::Node(right_identity, right_parent, right_color, right_right,
                    right_left) => {
                    have RbTree::Node(right_identity, right_parent, right_color, right_right,
                        right_left) == entry_right by { close(); }
                    have rb_parent_is(RbTree::Node(right_identity, right_parent, right_color,
                            right_right, right_left), node) == 1 by {
                        rewrite(RbTree::Node(right_identity, right_parent, right_color,
                                right_right, right_left), entry_right);
                        close();
                    }
                    have ctx_node_is(Context::Left(node, entry_parent, entry_color, entry_left,
                            old(c.model)), node) == 1 by {
                        unfold(ctx_node_is(Context::Left(node, entry_parent, entry_color,
                                    entry_left, old(c.model)), node));
                        close();
                    }
                    have rb_ctx_linked(RbTree::Node(right_identity, right_parent, right_color,
                            right_right, right_left), Context::Left(node, entry_parent,
                            entry_color, entry_left, old(c.model))) == 1 by {
                        apply(rb_ctx_linked_from_parent(right_identity, right_parent,
                                right_color, right_right, right_left, Context::Left(node,
                                    entry_parent, entry_color, entry_left, old(c.model)),
                                node));
                        close();
                    }
                    have plug(Context::Left(node, entry_parent, entry_color, entry_left,
                            old(c.model)), entry_right) == plug(old(c.model), old(t.model)) by {
                        rewrite(node, entry_identity);
                        close();
                    }
                    have ctx_descends_from_left(Context::Left(node, entry_parent, entry_color,
                            entry_left, old(c.model)), node) == 1 by {
                        unfold(ctx_descends_from_left(Context::Left(node, entry_parent, entry_color,
                                    entry_left, old(c.model)), node));
                        close();
                    }
                    let { right: right_l, left: right_r } = unfold(entry_r);
                    have node->rb_left != 0;
                    have ((node->rb_left->__rb_parent_color & ~3) as (struct rb_node *)) == right_parent by close();
                    let t = fold(rb_at(node->rb_left), {
                        model: entry_right,
                        right: right_l,
                            left: right_r
                    });
                    step();
                    step();
                    let ctx = fold(ctx_at(node->rb_left), {
                        model: Context::Left(node,
                                entry_parent, entry_color, entry_left, old(c.model)),
                        sibling: entry_l, up: c
                    });
                    have ctx.model == Context::Left(node, entry_parent, entry_color,
                        entry_left, old(c.model)) by { close(); }
                    match ctx.model {
                        Context::Top => { contradiction(ctx.model == Context::Top); },
                        Context::Right(first_identity, first_parent, first_color, first_right,
                            above) => { contradiction(ctx.model == Context::Right(first_identity,
                                    first_parent, first_color, first_right, above)); },
                        Context::Left(first_identity, first_parent, first_color, first_left,
                            above) => {
                            have Context::Left(first_identity, first_parent, first_color,
                                first_left, above) == Context::Left(node, entry_parent,
                                entry_color, entry_left, old(c.model)) by {
                                rewrite(Context::Left(first_identity, first_parent,
                                        first_color, first_left, above), ctx.model);
                                rewrite(Context::Left(node, entry_parent, entry_color,
                                        entry_left, old(c.model)), ctx.model);
                                normalize();
                            }
                            have above == old(c.model) by close();
                            have plug(above, RbTree::Node(entry_identity, entry_parent,
                                    entry_color, entry_right, entry_left)) == plug(old(c.model),
                                old(t.model)) by {
                                rewrite(above, old(c.model));
                                rewrite(RbTree::Node(entry_identity, entry_parent, entry_color,
                                        entry_right, entry_left), old(t.model));
                                normalize();
                            }
                            have t.model == entry_right;
                            have plug(ctx.model, t.model) == plug(old(c.model),
                                old(t.model)) by {
                                rewrite(ctx.model, Context::Left(node, entry_parent,
                                        entry_color, entry_left, old(c.model)));
                                rewrite(t.model, entry_right);
                                close();
                            }
                            have plug(ctx.model, t.model) == plug(above,
                                RbTree::Node(entry_identity, entry_parent, entry_color,
                                    entry_right, entry_left)) by {
                                rewrite(plug(above, RbTree::Node(entry_identity, entry_parent,
                                            entry_color, entry_right,
                                            entry_left)), plug(old(c.model), old(t.model)));
                                close();
                            }
                            have rb_ctx_linked(t.model, ctx.model) == 1 by {
                                rewrite(ctx.model, Context::Left(node, entry_parent,
                                        entry_color, entry_left, old(c.model)));
                                rewrite(t.model, entry_right);
                                rewrite(entry_right, RbTree::Node(right_identity,
                                        right_parent, right_color, right_right, right_left));
                                close();
                            }
                            have ctx_descends_from_left(ctx.model, old(node)) == 1 by {
                                rewrite(ctx.model, Context::Left(node, entry_parent,
                                        entry_color, entry_left, old(c.model)));
                                close();
                            }
                            step();
                            loop {
                                owns ctx: ctx_at(node);
                                owns t: rb_at(node);
                                decreases t;
                                invariant t.model != RbTree::Empty;
                                invariant rb_ctx_linked(t.model, ctx.model) == 1;
                                invariant ctx_descends_from_left(ctx.model, old(node)) == 1;
                                invariant plug(ctx.model, t.model) == plug(above,
                                    RbTree::Node(entry_identity, entry_parent, entry_color,
                                        entry_right, entry_left));

                                initialize by close();
                                maintain by {
                                    match t.model {
                                        RbTree::Empty => { contradiction(t.model
                                                == RbTree::Empty); },
                                        RbTree::Node(identity, par, color, right_model,
                                            left_model) => {
                                            have ctx_node_is(ctx.model, par) == 1 by {
                                                apply(rb_ctx_linked_node(identity, par, color,
                                                        right_model, left_model, ctx.model));
                                                rewrite(ctx_node_is(ctx.model,
                                                        par), rb_ctx_linked(RbTree::Node(identity, par,
                                                            color, right_model, left_model),
                                                        ctx.model));
                                                rewrite(RbTree::Node(identity, par, color,
                                                        right_model, left_model), t.model);
                                                close();
                                            }
                                            have plug(Context::Right(identity, par, color,
                                                    right_model, ctx.model),
                                                left_model) == plug(above,
                                                RbTree::Node(entry_identity, entry_parent,
                                                    entry_color, entry_right, entry_left)) by {
                                                unfold(plug(Context::Right(identity, par, color,
                                                            right_model, ctx.model),
                                                        left_model));
                                                rewrite(RbTree::Node(identity, par, color,
                                                        right_model, left_model), t.model);
                                                close();
                                            }
                                            let { right: l, left: rt } = unfold(t);
                                            have plug(Context::Right(node, par, color,
                                                    right_model, ctx.model),
                                                left_model) == plug(above,
                                                RbTree::Node(entry_identity, entry_parent,
                                                    entry_color, entry_right, entry_left)) by {
                                                rewrite(node, identity);
                                                close();
                                            }
                                            have ctx_descends_from_left(Context::Right(node, par,
                                                    color, right_model, ctx.model),
                                                old(node)) == 1 by {
                                                unfold(ctx_descends_from_left(Context::Right(node,
                                                            par, color, right_model, ctx.model),
                                                        old(node)));
                                                close();
                                            }
                                            have ctx_node_is(Context::Right(node, par, color,
                                                    right_model, ctx.model), node) == 1 by {
                                                unfold(ctx_node_is(Context::Right(node, par,
                                                            color, right_model, ctx.model),
                                                        node));
                                                normalize();
                                            }
                                            match l.model {
                                                RbTree::Empty => { contradiction(l.model
                                                        == RbTree::Empty); },
                                                RbTree::Node(left_identity, left_parent,
                                                    left_color, left_right, left_left) => {
                                                    have left_model
                                                        == RbTree::Node(left_identity,
                                                        left_parent, left_color, left_right,
                                                        left_left) by { close(); }
                                                    have rb_parent_is(RbTree::Node(left_identity,
                                                            left_parent, left_color, left_right,
                                                            left_left), node) == 1 by {
                                                        rewrite(RbTree::Node(left_identity,
                                                                left_parent, left_color,
                                                                left_right,
                                                                left_left), left_model);
                                                        close();
                                                    }
                                                    have rb_ctx_linked(RbTree::Node(left_identity,
                                                            left_parent, left_color, left_right,
                                                            left_left), Context::Right(node,
                                                            par, color, right_model,
                                                            ctx.model)) == 1 by {
                                                        apply(rb_ctx_linked_from_parent(left_identity,
                                                                left_parent, left_color,
                                                                left_right, left_left,
                                                                Context::Right(node, par, color,
                                                                    right_model, ctx.model),
                                                                node));
                                                        close();
                                                    }
                                                    have rb_ctx_linked(left_model,
                                                        Context::Right(node, par, color,
                                                            right_model, ctx.model)) == 1 by {
                                                        rewrite(left_model, RbTree::Node(left_identity,
                                                                left_parent, left_color,
                                                                left_right, left_left));
                                                        close();
                                                    }
                                                    let frame = fold(ctx_at(node->rb_right),
                                                        {
                                                        model: Context::Right(node, par, color,
                                                                right_model, ctx.model),
                                                        sibling: rt, up: ctx
                                                    });
                                                    step();
                                                },
                                            }
                                        },
                                    }
                                }
                            }
                            match t.model {
                                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                                RbTree::Node(identity, par, color, right_model, left_model) => {
                                    have plug(ctx.model, RbTree::Node(identity, par, color,
                                            right_model, left_model)) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(RbTree::Node(identity, par, color, right_model,
                                                left_model), t.model);
                                        rewrite(plug(ctx.model, t.model), plug(above,
                                                RbTree::Node(entry_identity, entry_parent,
                                                    entry_color, entry_right, entry_left)));
                                        close();
                                    }
                                    have rb_ctx_linked(RbTree::Node(identity, par, color,
                                            right_model, left_model), ctx.model) == 1 by {
                                        rewrite(RbTree::Node(identity, par, color, right_model,
                                                left_model), t.model);
                                        close();
                                    }
                                    let { right: l, left: rt } = unfold(t);
                                    have rb_right(RbTree::Node(identity, par, color, right_model,
                                            left_model)) == left_model by {
                                        unfold(rb_right(RbTree::Node(identity, par, color,
                                                    right_model, left_model)));
                                        normalize();
                                    }
                                    have node != 0;
                                    let sub = fold(rb_at(node), {
                                        model: RbTree::Node(identity,
                                                par, color, right_model, left_model),
                                        right: l, left: rt
                                    });
                                    have rb_right(sub.model) == RbTree::Empty by {
                                        rewrite(sub.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        rewrite(rb_right(RbTree::Node(identity, par, color,
                                                    right_model, left_model)), left_model);
                                        close();
                                    }
                                    have rb_identity_is(sub.model, node) == 1 by {
                                        rewrite(sub.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        unfold(rb_identity_is(RbTree::Node(identity, par, color,
                                                    right_model, left_model), node));
                                        normalize() using { node == identity; };
                                    }
                                    have rb_list_ends_with(rb_inorder(sub.model),
                                        node) == 1 by {
                                        apply(rb_inorder_last_at_rightmost(sub.model,
                                                node));
                                        close();
                                    }
                                    have rb_list_adjacent(rb_inorder(plug(ctx.model,
                                                sub.model)), node, old(node)) == 1 by {
                                        apply(plug_predecessor(ctx.model, sub.model, old(node),
                                                node));
                                        close();
                                    }
                                    have plug(ctx.model, sub.model) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(sub.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        close();
                                    }
                                    have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                        rewrite(sub.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        close();
                                    }
                                    have rb_list_adjacent(rb_inorder(plug(old(c.model),
                                                old(t.model))), node, old(node)) == 1 by {
                                        rewrite(plug(old(c.model),
                                                old(t.model)), plug(ctx.model, sub.model));
                                        close();
                                    }
                                    let rest = fold(rb_remainder_at(node),
                                        { model: Remainder::More });
                                    step();
                                    close();
                                },
                            }
                        },
                    }
                },
                RbTree::Empty => {
                    have entry_right == RbTree::Empty;
                    have rb_left(RbTree::Node(entry_identity, entry_parent, entry_color,
                            entry_right, entry_left)) == RbTree::Empty by {
                        unfold(rb_left(RbTree::Node(entry_identity, entry_parent, entry_color,
                                    entry_right, entry_left)));
                        close();
                    }
                    have rb_identity_is(RbTree::Node(entry_identity, entry_parent, entry_color,
                            entry_right, entry_left), node) == 1 by {
                        unfold(rb_identity_is(RbTree::Node(entry_identity, entry_parent,
                                    entry_color, entry_right, entry_left), node));
                        normalize() using { node == entry_identity; };
                    }
                    have rb_list_starts_with(rb_inorder(RbTree::Node(entry_identity, entry_parent,
                                entry_color, entry_right, entry_left)), node) == 1 by {
                        apply(rb_inorder_first_at_leftmost(RbTree::Node(entry_identity,
                                    entry_parent, entry_color, entry_right, entry_left),
                                node));
                        close();
                    }
                    unfold(entry_r);
                    have node->rb_left == 0;
                    let entry_r = fold(rb_at(node->rb_left), { model: RbTree::Empty });
                    step();
                    step();
                    step();
                    have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == entry_parent by close();
                    let t = fold(rb_at(node), {
                        model: old(t.model),
                        right: entry_l,
                            left: entry_r
                    });
                    have rb_list_starts_with(rb_inorder(t.model), old(node)) == 1 by {
                        rewrite(t.model, RbTree::Node(entry_identity, entry_parent,
                                entry_color, entry_right, entry_left));
                        close();
                    }
                    loop {
                        owns c: ctx_at(node);
                        owns t: rb_at(node);
                        decreases c;
                        invariant t.model != RbTree::Empty;
                        invariant rb_ctx_linked(t.model, c.model) == 1;
                        invariant rb_list_starts_with(rb_inorder(t.model), old(node)) == 1;
                        invariant plug(c.model, t.model) == plug(old(c.model), old(t.model));

                        initialize by close();
                        maintain by {
                            match t.model {
                                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                                RbTree::Node(identity, par, color, right_model, left_model) => {
                                    have ctx_node_is(c.model, par) == 1 by {
                                        apply(rb_ctx_linked_node(identity, par, color,
                                                right_model, left_model, c.model));
                                        rewrite(ctx_node_is(c.model,
                                                par), rb_ctx_linked(RbTree::Node(identity,
                                                    par, color, right_model, left_model),
                                                c.model));
                                        rewrite(RbTree::Node(identity, par, color, right_model,
                                                left_model), t.model);
                                        close();
                                    }
                                    have rb_list_starts_with(rb_inorder(RbTree::Node(identity,
                                                par, color, right_model, left_model)),
                                        old(node)) == 1 by {
                                        rewrite(RbTree::Node(identity, par, color, right_model,
                                                left_model), t.model);
                                        close();
                                    }
                                    have plug(c.model, RbTree::Node(identity, par, color,
                                            right_model, left_model)) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(RbTree::Node(identity, par, color, right_model,
                                                left_model), t.model);
                                        close();
                                    }
                                    have rb_ctx_linked(RbTree::Node(identity, par, color,
                                            right_model, left_model), c.model) == 1 by {
                                        rewrite(RbTree::Node(identity, par, color, right_model,
                                                left_model), t.model);
                                        close();
                                    }
                                    let { right: l, left: r } = unfold(t);
                                    // Recover the parent before evaluating the rest of the loop test.
                                    have address(par) == (node->__rb_parent_color & ~3) by close() using {
                                        aligned(par, 8);
                                        node->__rb_parent_color == address(par) + (node->__rb_parent_color & 1);
                                    };
                                    have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == par by close();
                                    step();
                                    have parent == par by close();
                                    have par == parent by {
                                        rewrite(parent, par);
                                        normalize();
                                    }
                                    let t = fold(rb_at(node), {
                                        model: RbTree::Node(identity,
                                                par, color, right_model, left_model),
                                        right: l, left: r
                                    });
                                    have rb_list_starts_with(rb_inorder(t.model),
                                        old(node)) == 1 by {
                                        rewrite(t.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        close();
                                    }
                                    have plug(c.model, t.model) == plug(old(c.model),
                                        old(t.model)) by {
                                        rewrite(t.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        close();
                                    }
                                    have rb_ctx_linked(t.model, c.model) == 1 by {
                                        rewrite(t.model, RbTree::Node(identity, par, color,
                                                right_model, left_model));
                                        close();
                                    }
                                    have ctx_node_is(c.model, parent) == 1 by {
                                        apply(ctx_node_is_same(c.model, par, parent));
                                        close();
                                    }
                                    match c.model {
                                        Context::Top => {
                                            have ctx_is_left(c.model) == 0 by {
                                                rewrite(c.model, Context::Top);
                                                unfold(ctx_is_left(Context::Top));
                                                normalize();
                                            }
                                            have ctx_node_is(Context::Top, parent) == 1 by {
                                                rewrite(Context::Top, c.model);
                                                close();
                                            }
                                            have parent == 0 by {
                                                apply(ctx_node_is_top(parent));
                                                close();
                                            }
                                            step();
                                        },
                                        Context::Right(frame_identity, frame_parent, frame_color,
                                            frame_right, above) => {
                                            have ctx_node_is(Context::Right(frame_identity,
                                                    frame_parent, frame_color, frame_right,
                                                    above), parent) == 1 by {
                                                rewrite(Context::Right(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above), c.model);
                                                close();
                                            }
                                            have frame_identity == parent by {
                                                apply(ctx_node_is_right(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above, parent));
                                                close();
                                            }
                                            have ctx_is_left(Context::Right(frame_identity,
                                                    frame_parent, frame_color, frame_right,
                                                    above)) == 0 by {
                                                unfold(ctx_is_left(Context::Right(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_right, above)));
                                                normalize();
                                            }
                                            have plug(Context::Right(frame_identity,
                                                    frame_parent, frame_color, frame_right,
                                                    above), t.model) == plug(old(c.model),
                                                old(t.model)) by {
                                                rewrite(Context::Right(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above), c.model);
                                                close();
                                            }
                                            have rb_ctx_linked(t.model,
                                                Context::Right(frame_identity, frame_parent,
                                                    frame_color, frame_right, above)) == 1 by {
                                                rewrite(Context::Right(frame_identity,
                                                        frame_parent, frame_color, frame_right,
                                                        above), c.model);
                                                close();
                                            }
                                            let { sibling: s, up: u } = unfold(c);
                                            have defined(parent->rb_left) by {
                                                rewrite(parent, frame_identity);
                                                normalize();
                                            }
                                            match s.model {
                                                RbTree::Empty => {
                                                    unfold(s);
                                                    have parent->rb_left == 0;
                                                    have node != parent->rb_left;
                                                    let s = fold(rb_at(0),
                                                        { model: RbTree::Empty });
                                                    let c = fold(ctx_at(node),
                                                        {
                                                        model: Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above),
                                                        sibling: s, up: u
                                                    });
                                                    have ctx_node_is(c.model, parent) == 1 by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    have ctx_is_left(c.model) == 0 by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    have plug(c.model,
                                                        t.model) == plug(old(c.model),
                                                        old(t.model)) by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    have rb_ctx_linked(t.model,
                                                        c.model) == 1 by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    step();
                                                },
                                                RbTree::Node(sibling_identity, sibling_parent,
                                                    sibling_color, sibling_right,
                                                    sibling_left) => {
                                                    let { right: node_l,
                                                            left: node_r } = unfold(t);
                                                    let { right: sibling_l,
                                                            left: sibling_r } = unfold(s);
                                                    have separate(memory(node->__rb_parent_color), memory(parent->rb_left->__rb_parent_color)) by {
                                                        rewrite(parent, frame_identity);
                                                        close();
                                                    }
                                                    have node != parent->rb_left by close() using {
                                                        separate(memory(node->__rb_parent_color), memory(parent->rb_left->__rb_parent_color));
                                                    };
                                                    // Refold using the opened frame's sibling address.
                                                    have frame_identity->rb_left != 0 by close();
                                                    have frame_identity->rb_left == sibling_identity by close();
                                                    have address(sibling_parent) != address(frame_identity->rb_left) by close();
                                                    have aligned(frame_identity->rb_left, 8) by close();
                                                    have ((frame_identity->rb_left->__rb_parent_color & ~3) as (struct rb_node *)) == sibling_parent by close();
                                                    have frame_identity->rb_left->__rb_parent_color ==
                                                        address(sibling_parent) + (frame_identity->rb_left->__rb_parent_color & 1) by close();
                                                    have (frame_identity->rb_left->__rb_parent_color & 1) == color_bit(sibling_color) by close();
                                                    have rb_parent_is(sibling_left, frame_identity->rb_left) == 1 by close();
                                                    have rb_parent_is(sibling_right, frame_identity->rb_left) == 1 by close();
                                                    let s = fold(rb_at(frame_identity->rb_left),
                                                        {
                                                        model: frame_right,
                                                        right: sibling_l, left: sibling_r
                                                    });
                                                    let t = fold(rb_at(node),
                                                        {
                                                        model: RbTree::Node(identity, par,
                                                                color, right_model,
                                                                left_model),
                                                        right: node_l,
                                                            left: node_r
                                                    });
                                                    let c = fold(ctx_at(node),
                                                        {
                                                        model: Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above),
                                                        sibling: s, up: u
                                                    });
                                                    have ctx_node_is(c.model, parent) == 1 by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    have ctx_is_left(c.model) == 0 by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    have plug(c.model,
                                                        t.model) == plug(old(c.model),
                                                        old(t.model)) by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    have rb_ctx_linked(t.model,
                                                        c.model) == 1 by {
                                                        rewrite(c.model, Context::Right(frame_identity,
                                                                frame_parent, frame_color,
                                                                frame_right, above));
                                                        close();
                                                    }
                                                    step();
                                                },
                                            }
                                        },
                                        Context::Left(frame_identity, frame_parent,
                                            frame_color, frame_left, above) => {
                                            have ctx_node_is(Context::Left(frame_identity,
                                                    frame_parent, frame_color, frame_left,
                                                    above), parent) == 1 by {
                                                rewrite(Context::Left(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above), c.model);
                                                close();
                                            }
                                            have frame_identity == parent by {
                                                apply(ctx_node_is_left(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above, parent));
                                                close();
                                            }
                                            have rb_ctx_linked(RbTree::Node(identity, par,
                                                    color, right_model, left_model),
                                                Context::Left(frame_identity, frame_parent,
                                                    frame_color, frame_left, above)) == 1 by {
                                                rewrite(Context::Left(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above), c.model);
                                                close();
                                            }
                                            have rb_parent_is(RbTree::Node(identity, par, color,
                                                    right_model, left_model),
                                                frame_identity) == 1 by {
                                                apply(rb_ctx_linked_left_parent(RbTree::Node(identity,
                                                            par, color, right_model,
                                                            left_model), frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above));
                                                close();
                                            }
                                            have rb_parent_is(RbTree::Node(identity, par, color,
                                                    right_model, left_model), parent) == 1 by {
                                                apply(rb_parent_is_same(RbTree::Node(identity,
                                                            par, color, right_model,
                                                            left_model), frame_identity,
                                                        parent));
                                                close();
                                            }
                                            have rb_list_starts_with(rb_inorder(RbTree::Node(frame_identity,
                                                        frame_parent, frame_color, RbTree::Node(identity, par, color,
                                                            right_model, left_model),
                                                        frame_left)),
                                                old(node)) == 1 by {
                                                apply(rb_inorder_first_through_left(frame_identity,
                                                        frame_parent, frame_color, RbTree::Node(identity, par, color,
                                                            right_model, left_model),
                                                        frame_left,
                                                        old(node)));
                                                close();
                                            }
                                            have plug(above, RbTree::Node(frame_identity,
                                                    frame_parent, frame_color, RbTree::Node(identity, par, color,
                                                        right_model,
                                                        left_model),
                                                    frame_left)) == plug(old(c.model),
                                                old(t.model)) by {
                                                unfold(plug(Context::Left(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, above),
                                                        RbTree::Node(identity, par, color,
                                                            right_model, left_model)));
                                                rewrite(plug(above, RbTree::Node(frame_identity,
                                                            frame_parent, frame_color,
                                                            RbTree::Node(identity,
                                                                par, color, right_model,
                                                                left_model), frame_left)), plug(Context::Left(frame_identity,
                                                            frame_parent, frame_color,
                                                            frame_left, above),
                                                        RbTree::Node(identity, par, color,
                                                            right_model, left_model)));
                                                rewrite(Context::Left(frame_identity,
                                                        frame_parent, frame_color, frame_left,
                                                        above), c.model);
                                                close();
                                            }
                                            let { sibling: s, up: u } = unfold(c);
                                            have parent->rb_left == node by {
                                                rewrite(parent, frame_identity);
                                                close();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity,
                                                    frame_parent, frame_color, RbTree::Node(identity, par, color,
                                                        right_model, left_model),
                                                    frame_left),
                                                above) == 1 by {
                                                unfold(rb_ctx_linked(RbTree::Node(frame_identity,
                                                            frame_parent, frame_color,
                                                            RbTree::Node(identity,
                                                                par, color, right_model,
                                                                left_model), frame_left), above));
                                                close();
                                            }
                                            step();
                                            step();
                                            let lifted = fold(rb_at(node),
                                                {
                                                model: RbTree::Node(frame_identity,
                                                        frame_parent, frame_color, RbTree::Node(identity, par, color,
                                                            right_model, left_model),
                                                        frame_left),
                                                right: s, left: t
                                            });
                                        },
                                    }
                                },
                            }
                        }
                    }
                    match c.model {
                        Context::Top => {
                            have ctx_node_is(Context::Top, parent) == 1 by {
                                rewrite(Context::Top, c.model);
                                close();
                            }
                            have parent == 0 by {
                                apply(ctx_node_is_top(parent));
                                close();
                            }
                            have plug(Context::Top, t.model) == plug(old(c.model),
                                old(t.model)) by {
                                rewrite(Context::Top, c.model);
                                close();
                            }
                            have plug(Context::Top, t.model) == t.model by {
                                unfold(plug(Context::Top, t.model));
                                normalize();
                            }
                            have t.model == plug(old(c.model), old(t.model)) by {
                                rewrite(t.model, plug(Context::Top, t.model));
                                close();
                            }
                            have rb_remainder_tree(Remainder::Whole(node, t.model)) == t.model by {
                                unfold(rb_remainder_tree(Remainder::Whole(node, t.model)));
                                normalize();
                            }
                            have rb_remainder_tree(Remainder::Whole(node, t.model))
                                == plug(old(c.model), old(t.model)) by {
                                rewrite(rb_remainder_tree(Remainder::Whole(node, t.model)), t.model);
                                close();
                            }
                            have rb_list_starts_with(rb_inorder(plug(old(c.model), old(t.model))),
                                old(node)) == 1 by {
                                rewrite(plug(old(c.model), old(t.model)), t.model);
                                close();
                            }
                            unfold(c);
                            let ctx = fold(ctx_at(parent), { model: Context::Top });
                            let sub = fold(rb_at(parent), { model: RbTree::Empty });
                            let rest = fold(rb_remainder_at(parent),
                                { model: Remainder::Whole(node, t.model), whole: t });
                            step();
                            close();
                        },
                        Context::Right(frame_identity, frame_parent, frame_color, frame_right,
                            above) => {
                            have ctx_node_is(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), parent) == 1 by {
                                rewrite(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), c.model);
                                close();
                            }
                            have frame_identity == parent by {
                                apply(ctx_node_is_right(frame_identity, frame_parent, frame_color,
                                        frame_right, above, parent));
                                close();
                            }
                            have rb_ctx_linked(t.model, Context::Right(frame_identity, frame_parent, frame_color, frame_right, above)) == 1 by {
                                rewrite(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), c.model);
                                close();
                            }
                            have rb_parent_is(t.model, frame_identity) == 1 by {
                                apply(rb_ctx_linked_right_parent(t.model, frame_identity,
                                        frame_parent, frame_color, frame_right, above));
                                close();
                            }
                            have rb_parent_is(t.model, parent) == 1 by {
                                apply(rb_parent_is_same(t.model, frame_identity, parent));
                                close();
                            }
                            have plug(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), t.model) == plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model)) by {
                                unfold(plug(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), t.model));
                                normalize();
                            }
                            have plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model)) == plug(old(c.model), old(t.model)) by {
                                rewrite(plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model)), plug(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), t.model));
                                rewrite(Context::Right(frame_identity, frame_parent, frame_color, frame_right, above), c.model);
                                close();
                            }
                            have rb_list_adjacent(rb_inorder(RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model)), parent, old(node)) == 1 by {
                                apply(rb_inorder_adjacent_below(frame_identity, frame_parent,
                                        frame_color, frame_right, t.model, parent, old(node)));
                                close();
                            }
                            have rb_list_adjacent(rb_inorder(plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model))), parent, old(node)) == 1 by {
                                apply(plug_keeps_adjacent(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model), parent, old(node)));
                                close();
                            }
                            have rb_list_adjacent(rb_inorder(plug(old(c.model), old(t.model))), parent,
                                old(node)) == 1 by {
                                rewrite(plug(old(c.model), old(t.model)), plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, t.model)));
                                close();
                            }
                            match t.model {
                                RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                                RbTree::Node(top_identity, top_parent, top_color, top_right, top_left) => {
                                    have plug(above, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left))) == plug(old(c.model), old(t.model)) by {
                                        rewrite(RbTree::Node(top_identity, top_parent, top_color, top_right, top_left), t.model);
                                        close();
                                    }
                        have rb_parent_is(RbTree::Node(top_identity, top_parent, top_color, top_right, top_left), parent) == 1 by {
                            rewrite(RbTree::Node(top_identity, top_parent, top_color, top_right, top_left), t.model);
                            close();
                        }
                                    let { sibling: s, up: u } = unfold(c);
                                    have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), above) == 1 by {
                                        apply(rb_ctx_linked_node(frame_identity, frame_parent, frame_color, frame_right,
                                                RbTree::Node(top_identity, top_parent, top_color, top_right, top_left), above));
                                        rewrite(rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), above), ctx_node_is(above, frame_parent));
                                        close();
                                    }
                                    match u.model {
                                        Context::Top => {
                                            have plug(Context::Top, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left))) == plug(old(c.model), old(t.model)) by {
                                                rewrite(Context::Top, u.model);
                                                rewrite(u.model, above);
                                                close();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), Context::Top) == 1 by {
                                                rewrite(Context::Top, u.model);
                                                rewrite(u.model, above);
                                                close();
                                            }
                                            unfold(u);
                                            let ctx = fold(ctx_at(parent), { model: Context::Top });
                                            let sub = fold(rb_at(parent), { model: RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), right: t, left: s });
                                            let rest = fold(rb_remainder_at(parent), { model: Remainder::More });
                                            have plug(ctx.model, sub.model) == plug(old(c.model), old(t.model)) by {
                                                rewrite(ctx.model, Context::Top);
                                                rewrite(sub.model, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)));
                                                close();
                                            }
                                            have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                                rewrite(ctx.model, Context::Top);
                                                rewrite(sub.model, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)));
                                                close();
                                            }
                                            step();
                                            close();
                                        },
                                        Context::Right(up_identity, up_parent, up_color, up_sibling, up_above) => {
                                            have plug(Context::Right(up_identity, up_parent, up_color, up_sibling, up_above), RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left))) == plug(old(c.model), old(t.model)) by {
                                                rewrite(Context::Right(up_identity, up_parent, up_color, up_sibling, up_above), u.model);
                                                rewrite(u.model, above);
                                                close();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), Context::Right(up_identity, up_parent, up_color, up_sibling, up_above)) == 1 by {
                                                rewrite(Context::Right(up_identity, up_parent, up_color, up_sibling, up_above), u.model);
                                                rewrite(u.model, above);
                                                close();
                                            }
                                            let { sibling: up_s, up: up_u } = unfold(u);
                                            let ctx = fold(ctx_at(parent), {
                                                model: Context::Right(up_identity, up_parent, up_color, up_sibling, up_above),
                                                sibling: up_s, up: up_u
                                            });
                                            let sub = fold(rb_at(parent), { model: RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), right: t, left: s });
                                            let rest = fold(rb_remainder_at(parent), { model: Remainder::More });
                                            have plug(ctx.model, sub.model) == plug(old(c.model), old(t.model)) by {
                                                rewrite(ctx.model, Context::Right(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)));
                                                close();
                                            }
                                            have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                                rewrite(ctx.model, Context::Right(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)));
                                                close();
                                            }
                                            step();
                                            close();
                                        },
                                        Context::Left(up_identity, up_parent, up_color, up_sibling, up_above) => {
                                            have plug(Context::Left(up_identity, up_parent, up_color, up_sibling, up_above), RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left))) == plug(old(c.model), old(t.model)) by {
                                                rewrite(Context::Left(up_identity, up_parent, up_color, up_sibling, up_above), u.model);
                                                rewrite(u.model, above);
                                                close();
                                            }
                                            have rb_ctx_linked(RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), Context::Left(up_identity, up_parent, up_color, up_sibling, up_above)) == 1 by {
                                                rewrite(Context::Left(up_identity, up_parent, up_color, up_sibling, up_above), u.model);
                                                rewrite(u.model, above);
                                                close();
                                            }
                                            let { sibling: up_s, up: up_u } = unfold(u);
                                            let ctx = fold(ctx_at(parent), {
                                                model: Context::Left(up_identity, up_parent, up_color, up_sibling, up_above),
                                                sibling: up_s, up: up_u
                                            });
                                            let sub = fold(rb_at(parent), { model: RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)), right: t, left: s });
                                            let rest = fold(rb_remainder_at(parent), { model: Remainder::More });
                                            have plug(ctx.model, sub.model) == plug(old(c.model), old(t.model)) by {
                                                rewrite(ctx.model, Context::Left(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)));
                                                close();
                                            }
                                            have rb_ctx_linked(sub.model, ctx.model) == 1 by {
                                                rewrite(ctx.model, Context::Left(up_identity, up_parent, up_color, up_sibling, up_above));
                                                rewrite(sub.model, RbTree::Node(frame_identity, frame_parent, frame_color, frame_right, RbTree::Node(top_identity, top_parent, top_color, top_right, top_left)));
                                                close();
                                            }
                                            step();
                                            close();
                                        },
                                    }
                                },
                            }
                        },
                        Context::Left(frame_identity, frame_parent, frame_color, frame_left,
                            above) => {
                            have ctx_is_left(Context::Left(frame_identity, frame_parent,
                                    frame_color, frame_left, above)) == 0 by {
                                rewrite(Context::Left(frame_identity, frame_parent,
                                        frame_color, frame_left, above), c.model);
                                close();
                            }
                            have ctx_is_left(Context::Left(frame_identity, frame_parent,
                                    frame_color, frame_left, above)) != 1 by {
                                rewrite(ctx_is_left(Context::Left(frame_identity,
                                        frame_parent, frame_color, frame_left, above)), 0);
                                normalize();
                            }
                            have ctx_is_left(Context::Left(frame_identity, frame_parent,
                                    frame_color, frame_left, above)) == 1 by {
                                unfold(ctx_is_left(Context::Left(frame_identity,
                                            frame_parent, frame_color, frame_left, above)));
                                normalize();
                            }
                            contradiction(ctx_is_left(Context::Left(frame_identity,
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
