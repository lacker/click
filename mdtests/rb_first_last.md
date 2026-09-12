# `rb_first` and `rb_last` on the node-keyed model

The unchanged Linux `rb_first` and `rb_last` descend from the root to the
leftmost or rightmost node. They are the reason the rbtree model is keyed by
node with the parent in the payload (gap 35 in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md)):
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

`rb_first` also states its result's *position*: on a non-empty tree the result
is the head of `rb_inorder`. `exists` cannot quantify a `List`-typed variable,
so the `Cons(result, rest)` form is not spellable; `rb_list_starts_with` says
the same thing without a witness. Proving it needs the descent's own extra
invariant — every frame the loop pushes is a `Left` frame, `ctx_all_left` — and
two pure theorems: a list that starts with a value still starts with it after an
append, and plugging an all-left context preserves the head of `rb_inorder`.
`rb_last` states the structural half only. Its mirror needs `ends_with` and an
append lemma on the right, whose `Cons` case has to know that the appended tail
is non-empty; that is three more list theorems and it is not done here.

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
            unfold(t) as { left: entry_l, right: entry_r };
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
                            unfold(t) as { left: l, right: rt };
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
                    unfold(t) as { left: l, right: rt };
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
            unfold(t) as { left: entry_l, right: entry_r };
            have root->rb_node != 0 by { simp(); }
            let t = fold(rb_at(n), { model: old(t.model) },
                         { left: entry_l, right: entry_r });
            let ctx = fold(ctx_at(n, root), { model: Context::Top });
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
                            unfold(t) as { left: l, right: rt };
                            have plug(Context::Right(n, parent, color, left_model, ctx.model),
                                      right_model)
                                == old(t.model) by {
                                rewrite(n == identity);
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
                    unfold(t) as { left: l, right: rt };
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
