verifying "rb_insert_color.c";

import "../rbtree-model/rbtree_model.click";
import "../rbtree-model/rbtree_resources.click";

theorem ctx_rb_red_focus_not_top(ctx: Context, bh: Nat) {
    requires ctx_rb(ctx, bh, Color::Red) == 1;

    ensures ctx != Context::Top by {
        induct(ctx) as ih {
            Context::Top => {
                have ctx_rb(Context::Top, bh, Color::Red) != 1 by {
                    unfold(ctx_rb(Context::Top, bh, Color::Red));
                    unfold(color_black(Color::Red));
                    normalize();
                }
                contradiction(ctx_rb(Context::Top, bh, Color::Red) == 1);
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                normalize();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                normalize();
            }
        }
    }
}

theorem color_bit_zero_is_red(color: Color) {
    requires color_bit(color) == 0;

    ensures color == Color::Red by {
        induct(color) as ih {
            Color::Red => {
                normalize();
            }
            Color::Black => {
                have color_bit(Color::Black) != 0 by auto;
                contradiction(color_bit(Color::Black) == 0);
            }
        }
    }
}

theorem color_bit_one_is_black(color: Color) {
    requires color_bit(color) == 1;

    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                have color_bit(Color::Red) != 1 by auto;
                contradiction(color_bit(Color::Red) == 1);
            }
            Color::Black => {
                normalize();
            }
        }
    }
}

theorem rb_root_black_node_color_bit(node: struct rb_node*, parent: struct rb_node*,
                                     color: Color, left: RbTree, right: RbTree) {
    requires rb_root_black(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures color_bit(color) == 1 by {
        induct(color) as ih {
            Color::Red => {
                have rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) != 1 by {
                    unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)));
                    normalize();
                }
                contradiction(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right))
                    == 1);
            }
            Color::Black => {
                unfold(color_bit(Color::Black));
                normalize();
            }
        }
    }
}

theorem ctx_node_is_top_null(p: struct rb_node*) {
    requires ctx_node_is(Context::Top, p) == 1;

    ensures p == 0 by {
        if p == 0 {
            assumption();
        } else {
            have ctx_node_is(Context::Top, p) != 1 by {
                unfold(ctx_node_is(Context::Top, p));
                normalize() using { not(p == 0); }
            }
            contradiction(ctx_node_is(Context::Top, p) == 1);
        }
    }
}

theorem rb_ptr_transitive(a: struct rb_node*, b: struct rb_node*, c: struct rb_node*) {
    requires a == b;
    requires a == c;

    ensures c == b by simp;
}

theorem rb_has_parent_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                           left: RbTree, right: RbTree, q: struct rb_node*) {
    requires rb_has_parent(RbTree::Node(identity, parent, color, left, right), q) == 1;

    ensures parent == q by {
        if parent == q {
            assumption();
        } else {
            have rb_has_parent(RbTree::Node(identity, parent, color, left, right), q) != 1 by {
                unfold(rb_has_parent(
                    RbTree::Node(identity, parent, color, left, right), q));
                normalize() using { not(parent == q); }
            }
            contradiction(rb_has_parent(
                RbTree::Node(identity, parent, color, left, right), q) == 1);
        }
    }
}

theorem rb_has_parent_same(sub: RbTree, q: struct rb_node*, p: struct rb_node*) {
    requires rb_has_parent(sub, q) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures p == q by {
        induct(sub) as ih {
            RbTree::Empty => {
                have rb_has_parent(RbTree::Empty, q) != 1 by auto;
                contradiction(rb_has_parent(RbTree::Empty, q) == 1);
            }
            RbTree::Node(identity, parent, color, left, right) => {
                apply(rb_has_parent_node(identity, parent, color, left, right, q));
                apply(rb_has_parent_node(identity, parent, color, left, right, p));
                apply(rb_ptr_transitive(parent, q, p));
                assumption();
            }
        }
    }
}

theorem ctx_holds_top_parent(sub: RbTree) {
    requires ctx_holds(Context::Top, sub) == 1;

    ensures rb_has_parent(sub, 0) == 1 by {
        unfold(ctx_holds(Context::Top, sub));
        rewrite(rb_has_parent(sub, 0) == ctx_holds(Context::Top, sub));
        assumption();
    }
}

theorem ctx_holds_left_parent(cid: struct rb_node*, grandparent: struct rb_node*,
                              ccolor: Color, sibling_model: RbTree, up_model: Context,
                              sub: RbTree) {
    requires ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        sub) == 1;

    ensures rb_has_parent(sub, cid) == 1 by {
        unfold(ctx_holds(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), sub));
        rewrite(rb_has_parent(sub, cid)
            == ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        assumption();
    }
}

theorem ctx_holds_right_parent(cid: struct rb_node*, grandparent: struct rb_node*,
                               ccolor: Color, sibling_model: RbTree, up_model: Context,
                               sub: RbTree) {
    requires ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        sub) == 1;

    ensures rb_has_parent(sub, cid) == 1 by {
        unfold(ctx_holds(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), sub));
        rewrite(rb_has_parent(sub, cid)
            == ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        assumption();
    }
}

theorem ctx_node_is_from_parent(ctx: Context, sub: RbTree, p: struct rb_node*) {
    requires ctx_holds(ctx, sub) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures ctx_node_is(ctx, p) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_holds_top_parent(sub));
                apply(rb_has_parent_same(sub, 0, p));
                have ctx_node_is(Context::Top, p) == 1 by {
                    unfold(ctx_node_is(Context::Top, p));
                    normalize() using { p == 0; }
                }
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_holds_left_parent(cid, grandparent, ccolor, sibling_model,
                    up_model, sub));
                apply(rb_has_parent_same(sub, cid, p));
                have ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                    p) == 1 by {
                    unfold(ctx_node_is(
                        Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                    normalize() using { p == cid; }
                }
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_holds_right_parent(cid, grandparent, ccolor, sibling_model,
                    up_model, sub));
                apply(rb_has_parent_same(sub, cid, p));
                have ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                    p) == 1 by {
                    unfold(ctx_node_is(
                        Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                    normalize() using { p == cid; }
                }
                assumption();
            }
        }
    }
}

theorem ctx_node_is_left_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                  ccolor: Color, sibling_model: RbTree, up_model: Context,
                                  p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_node_is_right_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                   ccolor: Color, sibling_model: RbTree, up_model: Context,
                                   p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_top_fixed(p: struct rb_node*) {
    ensures Context::Top == ctx_reroot(Context::Top, p) by {
        unfold(ctx_reroot(Context::Top, p));
        normalize();
    }
}

theorem ctx_reroot_left_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
                              ccolor: Color, sibling_model: RbTree, up_model: Context,
                              p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures Context::Left(cid, grandparent, ccolor, sibling_model, up_model)
        == ctx_reroot(Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_right_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
                               ccolor: Color, sibling_model: RbTree, up_model: Context,
                               p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures Context::Right(cid, grandparent, ccolor, sibling_model, up_model)
        == ctx_reroot(Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_fixed(ctx: Context, p: struct rb_node*) {
    requires ctx_node_is(ctx, p) == 1;

    ensures ctx == ctx_reroot(ctx, p) by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_reroot_top_fixed(p));
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_left_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_right_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                assumption();
            }
        }
    }
}

function ctx_depth(ctx: Context) -> Integer
    decreases ctx
{
    match ctx {
        Context::Top => 0,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            ctx_depth(up_model) + 1,
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            ctx_depth(up_model) + 1,
    }
}

theorem ctx_depth_is_nonnegative(ctx: Context) {
    ensures 0 <= ctx_depth(ctx) by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(ctx_depth(Context::Top));
                normalize();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                arithmetic() using { 0 <= ctx_depth(up_model); }
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                arithmetic() using { 0 <= ctx_depth(up_model); }
            }
        }
    }
}

theorem rb_parent_consistent_parent_is(t: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(t, p) == 1;
    ensures rb_parent_is(t, p) == 1 by {
        induct(t) as ih {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, p));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_parent(node, parent, color, left, right, p));
                apply(rb_parent_is_node_is(node, parent, color, left, right, p));
                rewrite(rb_parent_is(RbTree::Node(node, parent, color, left, right), p)
                    == rb_node_is(parent, p));
                assumption();
            }
        }
    }
}

tactic refold_to_root(focus: struct rb_node*, root: struct rb_root*) {
    consumes c: ctx_at(focus, root);
    decreases ctx_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == plug(old(c.model), old(t.model));
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let whole = fold(rb_root_at(root), { model: t.model }, { tree: t });
            have whole.model == plug(old(c.model), old(t.model)) by auto;
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by auto;
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(rb_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(ctx_depth_is_nonnegative(up_model));
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by auto;
            have plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by auto;
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by auto;
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by auto;
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by auto;
            apply(plug_parent_consistent_ctx(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(rb_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)) }, { left: s, right: t });
            apply(ctx_depth_is_nonnegative(up_model));
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by auto;
            have plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) by auto;
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by auto;
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by auto;
        },
    }
}

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
} by {
    execute();
    simp();
}

void __rb_insert(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires AugmentRotate(augment_rotate);
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces tree: rb_root_at(root);
    ensures rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(tree.model) == 1;
    ensures rb_tree_parent_consistent(tree.model) == 1;
} by {
    match t.model {
        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
        RbTree::Node(identity, node_parent, color, left_model, right_model) => {
            let { left: l, right: r } = unfold(t);
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model)
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, node_parent, color, left_model, right_model)));
                assumption();
            }
            step();
            step();
            step();
            step();
            let t = fold(rb_at(node), { model: old(t.model) }, { left: l, right: r });
            have rb_has_parent(t.model, node_parent) == 1 by {
                rewrite(t.model
                    == RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_has_parent(
                    RbTree::Node(identity, node_parent, color, left_model, right_model),
                    node_parent));
                normalize();
            }
            have ctx_node_is(c.model, node_parent) == 1 by {
                apply(ctx_node_is_from_parent(c.model, t.model, node_parent)) using {
                    ctx_holds(c.model, t.model) == 1;
                    rb_has_parent(t.model, node_parent) == 1;
                }
                assumption();
            }
            have c.model == ctx_reroot(c.model, node_parent) by {
                apply(ctx_reroot_fixed(c.model, node_parent)) using {
                    ctx_node_is(c.model, node_parent) == 1;
                }
                assumption();
            }
            have parent == node_parent;
            loop {
                owns c: ctx_at(node, root);
                owns t: rb_at(node);
                decreases c;
                invariant t.model != RbTree::Empty;
                invariant rb_color_bit(t.model) == 0;
                invariant rb_parent_is(t.model, parent) == 1;
                invariant ctx_node_is(c.model, parent) == 1;
                invariant c.model == ctx_reroot(c.model, parent);
                invariant is_rb(t.model) == 1;
                invariant ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
                invariant rb_inorder(plug(c.model, t.model))
                    == rb_inorder(plug(old(c.model),
                        RbTree::Node(identity, node_parent, color,
                            left_model, right_model)));
                invariant rb_tree_parent_consistent(plug(c.model, t.model)) == 1;

                initialize by simp;
                preserve by {
                    match t.model {
                        RbTree::Empty => { contradiction(t.model == RbTree::Empty); },
                        RbTree::Node(nid, nparent, ncolor, nleft, nright) => {
                            if parent == 0 {
                                match c.model {
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor, csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor, csib, cup, parent)) using {
                                                ctx_node_is(Context::Left(cid, cgp, ccolor, csib, cup), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        contradiction(parent == 0);
                                    },
                                    Context::Right(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Right(cid, cgp, ccolor, csib, cup), parent) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor, csib, cup, parent)) using {
                                                ctx_node_is(Context::Right(cid, cgp, ccolor, csib, cup), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        contradiction(parent == 0);
                                    },
                                    Context::Top => {
                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have nparent == parent by {
                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        have RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black) by {
                                            unfold(rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            simp();
                                        }
                                        have is_rb(RbTree::Node(nid, nparent, ncolor, nleft, nright)) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have is_rb_root(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == 1 by {
                                            apply(ctx_insert_root_exit(RbTree::Node(nid, nparent, ncolor, nleft, nright))) using {
                                                is_rb(RbTree::Node(nid, nparent, ncolor, nleft, nright)) == 1;
                                            }
                                            assumption();
                                        }
                                        have is_rb_root(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright))) == 1 by {
                                            rewrite(RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Top == c.model);
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))) by {
                                            apply(plug_recolor_inorder(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            rewrite(rb_inorder(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            rewrite(rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)), 0) == rb_tree_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            rewrite(Context::Top == c.model);
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                            assumption();
                                        }
                                        have rb_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), 0) == 1 by {
                                            unfold(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            assumption();
                                        }
                                        have rb_parent_consistent(rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black), 0) == 1 by {
                                            apply(rb_recolor_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black, 0)) using {
                                                rb_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), 0) == 1;
                                            }
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright)), 0) == 1 by {
                                            unfold(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright)));
                                            rewrite(RbTree::Node(nid, 0, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            assumption();
                                        }
                                        let { left: l, right: r } = unfold(t);
                                        step();
                                        step();
                                        have (node->__rb_parent_color & 1)
                                            == color_bit(Color::Black) by {
                                            unfold(color_bit(Color::Black));
                                            simp();
                                        }
                                        let t = fold(rb_at(node),
                                            { model: RbTree::Node(nid, 0, Color::Black, nleft, nright) },
                                            { left: l, right: r });
                                        have is_rb_root(plug(c.model, t.model)) == 1 by {
                                            rewrite(c.model == Context::Top);
                                            rewrite(t.model == RbTree::Node(nid, 0, Color::Black, nleft, nright));
                                            assumption();
                                        }
                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(c.model == Context::Top);
                                            rewrite(t.model == RbTree::Node(nid, 0, Color::Black, nleft, nright));
                                            assumption();
                                        }
                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                            rewrite(c.model == Context::Top);
                                            rewrite(t.model == RbTree::Node(nid, 0, Color::Black, nleft, nright));
                                            assumption();
                                        }
                                        step();
                                    },
                                }
                            } else {
                                match c.model {
                                    Context::Top => {
                                        contradiction(c.model == Context::Top);
                                    },
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor,
                                                csib, cup, parent)) using {
                                                ctx_node_is(Context::Left(cid, cgp, ccolor,
                                                    csib, cup), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        have ctx_rb(Context::Left(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model))) using {
                                                ctx_almost_rb_insert(c.model,
                                                    black_height(t.model)) == 1;
                                            }
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model))
                                            == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(rb_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model), 0)
                                                == rb_tree_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have ctx_almost_rb_insert(Context::Left(cid, cgp, ccolor, csib, cup), black_height(t.model)) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    simp();
                                                }
                                                have ctx_almost_rb_insert(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1 by {
                                                    rewrite(Color::Black == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1 by {
                                                    apply(ctx_black_frame_left_restores(cid, cgp, csib, cup, black_height(t.model), rb_color(t.model))) using {
                                                        ctx_almost_rb_insert(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1;
                                                    }
                                                    assumption();
                                                }
                                                have is_rb_root(plug(Context::Left(cid, cgp, Color::Black, csib, cup), t.model)) == 1 by {
                                                    apply(ctx_insert_black_parent_exit(Context::Left(cid, cgp, Color::Black, csib, cup), t.model)) using {
                                                        is_rb(t.model) == 1;
                                                        ctx_rb(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1;
                                                    }
                                                    assumption();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    { model: Context::Left(cid, cgp, ccolor,
                                                        csib, cup) },
                                                    { sibling: cs, up: cu });
                                                have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                    rewrite(c.model == Context::Left(cid, cgp, ccolor, csib, cup));
                                                    rewrite(ccolor == Color::Black);
                                                    assumption();
                                                }
                                                have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                }
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    simp();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_left_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black)) using {
                                                        ctx_rb(Context::Left(cid, cgp, Color::Red,
                                                            csib, cup), black_height(t.model),
                                                            Color::Black) == 1;
                                                    }
                                                    rewrite(cu.model == cup);
                                                    assumption();
                                                }
                                                step();
                                                step();
                                                step();
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model))) using {
                                                        ctx_rb(cu.model,
                                                            black_height(t.model),
                                                            Color::Red) == 1;
                                                    }
                                                    assumption();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    contradiction(cu.model == Context::Top);
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    step();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Left(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            }
                                                            simp();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            }
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case3_left_step(ugp, gparent, cid, nid, nleft, nright, csib, usib, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        }
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        match cs.model ensuring {
                                                            owns sn: rb_at(tmp);
                                                            fact sn.model == rb_reparent(csib, gparent);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(cs);
                                                                step();
                                                                step();
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(csib, gparent) == RbTree::Empty by {
                                                                    rewrite(csib == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent));
                                                                }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Empty);
                                                                    simp();
                                                                }
                                                            },
                                                            RbTree::Node(sx, sp, scol, sl, sr) => {
                                                                let { left: sl_at, right: sr_at } = unfold(cs);
                                                                step();
                                                                step();
                                                                step();
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                have rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1 by {
                                                                    rewrite(RbTree::Node(sx, sp, scol, sl, sr) == csib);
                                                                    assumption();
                                                                }
                                                                have color_bit(scol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(sx, sp, scol, sl, sr)) using {
                                                                        rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr) by {
                                                                    rewrite(csib == RbTree::Node(sx, sp, scol, sl, sr));
                                                                    unfold(rb_reparent(RbTree::Node(sx, sp, scol, sl, sr), gparent));
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Node(sx, gparent, scol, sl, sr) }, { left: sl_at, right: sr_at });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr));
                                                                    simp();
                                                                }
                                                            },
                                                        }
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            simp();
                                                        }
                                                        match uu.model ensuring {
                                                            owns uu: ctx_at(parent, root);
                                                            fact uu.model == uup;
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                step();
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Top });
                                                                have uu.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                step();
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                    },
                                                                }
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(csib, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(csib, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib) }, { left: sn, right: un });
                                                            have rb_parent_is(RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), cid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), cid));
                                                            }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                simp();
                                                            }
                                                        let c = fold(ctx_at(node, root), { model: Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup) }, { sibling: gn, up: uu });
                                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(c.model == Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup));
                                                            rewrite(t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright));
                                                            rewrite(rb_inorder(plug(Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                            assumption();
                                                        }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            simp();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, t.model, csib)) == 1 by {
                                                                            apply(ctx_insert_cursor_left_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Left(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        have ctx_rb(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(RbTree::Node(nid, nparent, ncolor, nleft, nright)), Color::Red) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_left_step(ugp, gparent, cid, unid, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib, unl, unr, uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1;
                                                                            ctx_rb(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(RbTree::Node(nid, nparent, ncolor, nleft, nright)), Color::Red) == 1;
                                                                        }
                                                                        have rb_inorder(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0) == 1 by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0)
                                                                                == rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))));
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib) }, { left: t, right: cs });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp));
                                                                        }
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)) }, { left: pn, right: un });
                                                                        step();
                                                                        close_invariants();
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty));
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    step();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Right(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            }
                                                            simp();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            }
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case2_right_exit_step(ugp, gparent, cid, nid, usib, nleft, nright, csib, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        }
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        step();
                                                        step();
                                                        step();
                                                        match nr_at.model ensuring {
                                                            owns bn: rb_at(tmp);
                                                            fact bn.model == rb_reparent(nright, cid);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nr_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nright, cid) == RbTree::Empty by {
                                                                    rewrite(nright == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, cid));
                                                                }
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have bn.model == rb_reparent(nright, cid) by {
                                                                    rewrite(rb_reparent(nright, cid) == RbTree::Empty);
                                                                    simp();
                                                                }
                                                            },
                                                            RbTree::Node(bx, bp, bcol, bl, br) => {
                                                                let { left: bl_at, right: br_at } = unfold(nr_at);
                                                                step();
                                                                have rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1 by {
                                                                    rewrite(RbTree::Node(bx, bp, bcol, bl, br) == nright);
                                                                    assumption();
                                                                }
                                                                have color_bit(bcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(bx, bp, bcol, bl, br)) using {
                                                                        rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nright, cid) == RbTree::Node(bx, cid, bcol, bl, br) by {
                                                                    rewrite(nright == RbTree::Node(bx, bp, bcol, bl, br));
                                                                    unfold(rb_reparent(RbTree::Node(bx, bp, bcol, bl, br), cid));
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Node(bx, cid, bcol, bl, br) }, { left: bl_at, right: br_at });
                                                                have bn.model == rb_reparent(nright, cid) by {
                                                                    rewrite(rb_reparent(nright, cid) == RbTree::Node(bx, cid, bcol, bl, br));
                                                                    simp();
                                                                }
                                                            },
                                                        }
                                                        step();
                                                        have rb_parent_is(rb_reparent(nright, cid), cid) == 1 by {
                                                            apply(rb_reparent_parent_is(nright, cid));
                                                            assumption();
                                                        }
                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib) }, { left: bn, right: cs });
                                                        step();
                                                        step();
                                                        match nl_at.model ensuring {
                                                            owns rn: rb_at(tmp);
                                                            fact rn.model == rb_reparent(nleft, gparent);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nl_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nleft, gparent) == RbTree::Empty by {
                                                                    rewrite(nleft == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent));
                                                                }
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have rn.model == rb_reparent(nleft, gparent) by {
                                                                    rewrite(rb_reparent(nleft, gparent) == RbTree::Empty);
                                                                    simp();
                                                                }
                                                            },
                                                            RbTree::Node(rx, rp, rcol, rl, rr) => {
                                                                let { left: rl_at, right: rr_at } = unfold(nl_at);
                                                                step();
                                                                have rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1 by {
                                                                    rewrite(RbTree::Node(rx, rp, rcol, rl, rr) == nleft);
                                                                    assumption();
                                                                }
                                                                have color_bit(rcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(rx, rp, rcol, rl, rr)) using {
                                                                        rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nleft, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr) by {
                                                                    rewrite(nleft == RbTree::Node(rx, rp, rcol, rl, rr));
                                                                    unfold(rb_reparent(RbTree::Node(rx, rp, rcol, rl, rr), gparent));
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Node(rx, gparent, rcol, rl, rr) }, { left: rl_at, right: rr_at });
                                                                have rn.model == rb_reparent(nleft, gparent) by {
                                                                    rewrite(rb_reparent(nleft, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr));
                                                                    simp();
                                                                }
                                                            },
                                                        }
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            simp();
                                                        }
                                                        match uu.model ensuring {
                                                            owns c: ctx_at(node, root);
                                                            fact c.model == uup;
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                step();
                                                                let c = fold(ctx_at(node, root), { model: Context::Top });
                                                                have c.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                step();
                                                                let c = fold(ctx_at(node, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                    },
                                                                }
                                                                let c = fold(ctx_at(node, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(nleft, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(nleft, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)) }, { left: un, right: rn });
                                                            have rb_parent_is(RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), nid));
                                                            }
                                                            have rb_parent_is(RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), nid));
                                                            }
                                                            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                simp();
                                                            }
                                                            let t = fold(rb_at(node), { model: RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)) }, { left: gn, right: pn });
                                                            have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                rewrite(rb_inorder(plug(uup, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)))) == rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                                assumption();
                                                            }
                                                            have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                assumption();
                                                            }
                                                            have rb_parent_consistent(plug(c.model, t.model), 0) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                assumption();
                                                            }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            simp();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, t.model, csib)) == 1 by {
                                                                            apply(ctx_insert_cursor_left_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Left(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        have ctx_rb(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(RbTree::Node(nid, nparent, ncolor, nleft, nright)), Color::Red) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_right_step(ugp, gparent, cid, unid, unl, unr, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib, uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1;
                                                                            ctx_rb(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(RbTree::Node(nid, nparent, ncolor, nleft, nright)), Color::Red) == 1;
                                                                        }
                                                                        have rb_inorder(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0) == 1 by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib))
                                                                                == plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))), 0)
                                                                                == rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))));
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib) }, { left: t, right: cs });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), ugp));
                                                                        }
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) }, { left: un, right: pn });
                                                                        step();
                                                                        close_invariants();
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty));
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                }
                                            },
                                        }
                                    },
                                    Context::Right(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Right(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor,
                                                csib, cup, parent)) using {
                                                ctx_node_is(Context::Right(cid, cgp, ccolor,
                                                    csib, cup), parent) == 1;
                                            }
                                            assumption();
                                        }
                                        have ctx_rb(Context::Right(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model))) using {
                                                ctx_almost_rb_insert(c.model,
                                                    black_height(t.model)) == 1;
                                            }
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup)
                                                == c.model);
                                            assumption();
                                        }
                                        have rb_inorder(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model))
                                            == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have rb_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(rb_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model), 0)
                                                == rb_tree_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        have ctx_almost_rb_insert(Context::Right(cid, cgp, ccolor, csib, cup), black_height(t.model)) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup) == c.model);
                                            assumption();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1)
                                                        == color_bit(ccolor));
                                                    rewrite(ccolor == Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    simp();
                                                }
                                                have ctx_almost_rb_insert(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1 by {
                                                    rewrite(Color::Black == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1 by {
                                                    apply(ctx_black_frame_right_restores(cid, cgp, csib, cup, black_height(t.model), rb_color(t.model))) using {
                                                        ctx_almost_rb_insert(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1;
                                                    }
                                                    assumption();
                                                }
                                                have is_rb_root(plug(Context::Right(cid, cgp, Color::Black, csib, cup), t.model)) == 1 by {
                                                    apply(ctx_insert_black_parent_exit(Context::Right(cid, cgp, Color::Black, csib, cup), t.model)) using {
                                                        is_rb(t.model) == 1;
                                                        ctx_rb(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1;
                                                    }
                                                    assumption();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    { model: Context::Right(cid, cgp, ccolor,
                                                        csib, cup) },
                                                    { sibling: cs, up: cu });
                                                have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                    rewrite(c.model == Context::Right(cid, cgp, ccolor, csib, cup));
                                                    rewrite(ccolor == Color::Black);
                                                    assumption();
                                                }
                                                have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                }
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor == Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    simp();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red == ccolor);
                                                    assumption();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_right_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black)) using {
                                                        ctx_rb(Context::Right(cid, cgp, Color::Red,
                                                            csib, cup), black_height(t.model),
                                                            Color::Black) == 1;
                                                    }
                                                    rewrite(cu.model == cup);
                                                    assumption();
                                                }
                                                step();
                                                step();
                                                step();
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model))) using {
                                                        ctx_rb(cu.model,
                                                            black_height(t.model),
                                                            Color::Red) == 1;
                                                    }
                                                    assumption();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    contradiction(cu.model == Context::Top);
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    step();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Left(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            }
                                                            simp();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            }
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case2_left_exit_step(ugp, gparent, cid, nid, csib, nleft, nright, usib, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        }
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        step();
                                                        step();
                                                        step();
                                                        match nl_at.model ensuring {
                                                            owns bn: rb_at(tmp);
                                                            fact bn.model == rb_reparent(nleft, cid);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nl_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nleft, cid) == RbTree::Empty by {
                                                                    rewrite(nleft == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, cid));
                                                                }
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have bn.model == rb_reparent(nleft, cid) by {
                                                                    rewrite(rb_reparent(nleft, cid) == RbTree::Empty);
                                                                    simp();
                                                                }
                                                            },
                                                            RbTree::Node(bx, bp, bcol, bl, br) => {
                                                                let { left: bl_at, right: br_at } = unfold(nl_at);
                                                                step();
                                                                have rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1 by {
                                                                    rewrite(RbTree::Node(bx, bp, bcol, bl, br) == nleft);
                                                                    assumption();
                                                                }
                                                                have color_bit(bcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(bx, bp, bcol, bl, br)) using {
                                                                        rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nleft, cid) == RbTree::Node(bx, cid, bcol, bl, br) by {
                                                                    rewrite(nleft == RbTree::Node(bx, bp, bcol, bl, br));
                                                                    unfold(rb_reparent(RbTree::Node(bx, bp, bcol, bl, br), cid));
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let bn = fold(rb_at(tmp), { model: RbTree::Node(bx, cid, bcol, bl, br) }, { left: bl_at, right: br_at });
                                                                have bn.model == rb_reparent(nleft, cid) by {
                                                                    rewrite(rb_reparent(nleft, cid) == RbTree::Node(bx, cid, bcol, bl, br));
                                                                    simp();
                                                                }
                                                            },
                                                        }
                                                        step();
                                                        have rb_parent_is(rb_reparent(nleft, cid), cid) == 1 by {
                                                            apply(rb_reparent_parent_is(nleft, cid));
                                                            assumption();
                                                        }
                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)) }, { left: cs, right: bn });
                                                        step();
                                                        step();
                                                        match nr_at.model ensuring {
                                                            owns rn: rb_at(tmp);
                                                            fact rn.model == rb_reparent(nright, gparent);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(nr_at);
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(nright, gparent) == RbTree::Empty by {
                                                                    rewrite(nright == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent));
                                                                }
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have rn.model == rb_reparent(nright, gparent) by {
                                                                    rewrite(rb_reparent(nright, gparent) == RbTree::Empty);
                                                                    simp();
                                                                }
                                                            },
                                                            RbTree::Node(rx, rp, rcol, rl, rr) => {
                                                                let { left: rl_at, right: rr_at } = unfold(nr_at);
                                                                step();
                                                                have rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1 by {
                                                                    rewrite(RbTree::Node(rx, rp, rcol, rl, rr) == nright);
                                                                    assumption();
                                                                }
                                                                have color_bit(rcol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(rx, rp, rcol, rl, rr)) using {
                                                                        rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_reparent(nright, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr) by {
                                                                    rewrite(nright == RbTree::Node(rx, rp, rcol, rl, rr));
                                                                    unfold(rb_reparent(RbTree::Node(rx, rp, rcol, rl, rr), gparent));
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let rn = fold(rb_at(tmp), { model: RbTree::Node(rx, gparent, rcol, rl, rr) }, { left: rl_at, right: rr_at });
                                                                have rn.model == rb_reparent(nright, gparent) by {
                                                                    rewrite(rb_reparent(nright, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr));
                                                                    simp();
                                                                }
                                                            },
                                                        }
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            simp();
                                                        }
                                                        match uu.model ensuring {
                                                            owns c: ctx_at(node, root);
                                                            fact c.model == uup;
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                step();
                                                                let c = fold(ctx_at(node, root), { model: Context::Top });
                                                                have c.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                step();
                                                                let c = fold(ctx_at(node, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                    },
                                                                }
                                                                let c = fold(ctx_at(node, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have c.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(nright, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(nright, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib) }, { left: rn, right: un });
                                                            have rb_parent_is(RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), nid));
                                                            }
                                                            have rb_parent_is(RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), nid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), nid));
                                                            }
                                                            have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                simp();
                                                            }
                                                            let t = fold(rb_at(node), { model: RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)) }, { left: pn, right: gn });
                                                            have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                rewrite(rb_inorder(plug(uup, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)))) == rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                                assumption();
                                                            }
                                                            have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                assumption();
                                                            }
                                                            have rb_parent_consistent(plug(c.model, t.model), 0) == 1 by {
                                                                rewrite(c.model == uup);
                                                                rewrite(t.model == RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                assumption();
                                                            }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            simp();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, csib, t.model)) == 1 by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        have black_height(csib) == black_height(t.model) by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have ctx_rb(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(csib), Color::Red) == 1 by {
                                                                            rewrite(black_height(csib) == black_height(t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(cup == Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_left_step(ugp, gparent, cid, unid, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright), unl, unr, uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1;
                                                                            ctx_rb(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(csib), Color::Red) == 1;
                                                                        }
                                                                        have rb_inorder(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0) == 1 by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0)
                                                                                == rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))));
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)) }, { left: cs, right: t });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp));
                                                                        }
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)) }, { left: pn, right: un });
                                                                        step();
                                                                        close_invariants();
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty));
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup)
                                                            == cu.model);
                                                        rewrite(cu.model == cup);
                                                        assumption();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp)) using {
                                                            ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                                usib, uup), cgp) == 1;
                                                        }
                                                        assumption();
                                                    }
                                                    have ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup) == cu.model);
                                                        assumption();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    step();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr)) using {
                                                                        rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor)) using {
                                                                        color_bit(uncolor) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                    assumption();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                        rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp == gparent);
                                                                    rewrite(uncolor == Color::Black);
                                                                    normalize();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black == uncolor);
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    normalize();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                        ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    normalize();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Right(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor == Color::Black);
                                                            rewrite(uid == gparent);
                                                            normalize();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent)) using {
                                                                rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1;
                                                            }
                                                            simp();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor) == rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor)) using {
                                                                color_bit(ncolor) == 0;
                                                            }
                                                            assumption();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model == RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent == cid);
                                                            rewrite(ncolor == Color::Red);
                                                            normalize();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            assumption();
                                                        }
                                                        have ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        have rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright) == t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup) == cup);
                                                            rewrite(gparent == cgp);
                                                            rewrite(Color::Red == ccolor);
                                                            assumption();
                                                        }
                                                        apply(ctx_insert_case3_right_step(ugp, gparent, cid, nid, usib, csib, nleft, nright, uup)) using {
                                                            is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1;
                                                            rb_root_black(usib) == 1;
                                                            ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1;
                                                            rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1;
                                                        }
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(Color::Red == ncolor);
                                                            assumption();
                                                        }
                                                        match cs.model ensuring {
                                                            owns sn: rb_at(tmp);
                                                            fact sn.model == rb_reparent(csib, gparent);
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(cs);
                                                                step();
                                                                step();
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                have rb_reparent(csib, gparent) == RbTree::Empty by {
                                                                    rewrite(csib == RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent));
                                                                }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Empty);
                                                                    simp();
                                                                }
                                                            },
                                                            RbTree::Node(sx, sp, scol, sl, sr) => {
                                                                let { left: sl_at, right: sr_at } = unfold(cs);
                                                                step();
                                                                step();
                                                                step();
                                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright) }, { left: nl_at, right: nr_at });
                                                                have rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1 by {
                                                                    rewrite(RbTree::Node(sx, sp, scol, sl, sr) == csib);
                                                                    assumption();
                                                                }
                                                                have color_bit(scol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(sx, sp, scol, sl, sr)) using {
                                                                        rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                have rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr) by {
                                                                    rewrite(csib == RbTree::Node(sx, sp, scol, sl, sr));
                                                                    unfold(rb_reparent(RbTree::Node(sx, sp, scol, sl, sr), gparent));
                                                                }
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                step();
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Node(sx, gparent, scol, sl, sr) }, { left: sl_at, right: sr_at });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr));
                                                                    simp();
                                                                }
                                                            },
                                                        }
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1) == color_bit(ucolor));
                                                            rewrite(ucolor == Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            simp();
                                                        }
                                                        match uu.model ensuring {
                                                            owns uu: ctx_at(parent, root);
                                                            fact uu.model == uup;
                                                        } {
                                                            Context::Top => {
                                                                have ctx_node_is(Context::Top, ugp) == 1 by {
                                                                    rewrite(Context::Top == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == 0 by {
                                                                    apply(ctx_node_is_top_null(ugp)) using {
                                                                        ctx_node_is(Context::Top, ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                unfold(uu);
                                                                step();
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Top });
                                                                have uu.model == uup by { rewrite(uup == Context::Top); normalize(); }
                                                            },
                                                            Context::Left(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Left(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_left_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Left(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                step();
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Left(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Left(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                            Context::Right(xid, xgp, xcol, xsib, xup) => {
                                                                have ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1 by {
                                                                    rewrite(Context::Right(xid, xgp, xcol, xsib, xup) == uu.model);
                                                                    rewrite(uu.model == uup);
                                                                    assumption();
                                                                }
                                                                have ugp == xid by {
                                                                    apply(ctx_node_is_right_identity(xid, xgp, xcol, xsib, xup, ugp)) using {
                                                                        ctx_node_is(Context::Right(xid, xgp, xcol, xsib, xup), ugp) == 1;
                                                                    }
                                                                    assumption();
                                                                }
                                                                let { sibling: xs, up: xu } = unfold(uu);
                                                                match xsib ensuring {
                                                                    owns xs: rb_at(xid->rb_left);
                                                                    fact xs.model == xsib;
                                                                } {
                                                                    RbTree::Empty => {
                                                                        unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(0), { model: xsib });
                                                                    },
                                                                    RbTree::Node(yid, yp, ycol, yl, yr) => {
                                                                        let { left: yl_at, right: yr_at } = unfold(xs);
                                                                        step();
                                                                        let xs = fold(rb_at(yid), { model: xsib }, { left: yl_at, right: yr_at });
                                                                    },
                                                                }
                                                                let uu = fold(ctx_at(parent, root), { model: Context::Right(xid, xgp, xcol, xsib, xup) }, { sibling: xs, up: xu });
                                                                have uu.model == uup by { rewrite(uup == Context::Right(xid, xgp, xcol, xsib, xup)); normalize(); }
                                                            },
                                                        }
                                                            have rb_parent_is(rb_reparent(csib, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(csib, gparent));
                                                                assumption();
                                                            }
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)) }, { left: un, right: sn });
                                                            have rb_parent_is(RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), cid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), cid));
                                                            }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                simp();
                                                            }
                                                        let c = fold(ctx_at(node, root), { model: Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup) }, { sibling: gn, up: uu });
                                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(c.model == Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup));
                                                            rewrite(t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright));
                                                            rewrite(rb_inorder(plug(Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                            assumption();
                                                        }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1) == color_bit(uncolor));
                                                                            rewrite(uncolor == Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            simp();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model))) using {
                                                                                ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr) == usib);
                                                                            assumption();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent)) using {
                                                                                rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp == gparent);
                                                                            rewrite(uncolor == Color::Red);
                                                                            normalize();
                                                                        }
                                                                        have cup == Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib == RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor == Color::Black);
                                                                            rewrite(uid == gparent);
                                                                            normalize();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, csib, t.model)) == 1 by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(gparent == cgp);
                                                                            assumption();
                                                                        }
                                                                        have black_height(csib) == black_height(t.model) by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup)) using {
                                                                                is_rb(t.model) == 1;
                                                                                ctx_rb(Context::Right(cid, cgp, Color::Red, csib, cup), black_height(t.model), Color::Black) == 1;
                                                                            }
                                                                            assumption();
                                                                        }
                                                                        have ctx_rb(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(csib), Color::Red) == 1 by {
                                                                            rewrite(black_height(csib) == black_height(t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(cup == Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            assumption();
                                                                        }
                                                                        apply(ctx_insert_case1_right_step(ugp, gparent, cid, unid, unl, unr, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright), uup)) using {
                                                                            almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1;
                                                                            ctx_rb(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), black_height(csib), Color::Red) == 1;
                                                                        }
                                                                        have rb_inorder(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0) == 1 by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) == cup);
                                                                            rewrite(gparent == cgp);
                                                                            rewrite(Color::Red == ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model))
                                                                                == plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            assumption();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))), 0)
                                                                                == rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0));
                                                                            assumption();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))));
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright) == t.model);
                                                                            assumption();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                        }
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr) }, { left: ul, right: ur });
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)) }, { left: cs, right: t });
                                                                        step();
                                                                        step();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), ugp));
                                                                        }
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) }, { left: un, right: pn });
                                                                        step();
                                                                        close_invariants();
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib == RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor == Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            assumption();
                                                                        }
                                                                        contradiction(rb_root_black(usib) == 1);
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib == RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty));
                                                                }
                                                                contradiction(rb_root_black(usib) == 1);
                                                            },
                                                        }
                                                    }
                                                },
                                                }
                                            },
                                        }
                                    },
                                }
                            }
                        },
                    }
                }
            }
            have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), old(t.model))) by {
                rewrite(old(t.model) == RbTree::Node(identity, node_parent, color, left_model, right_model));
                assumption();
            }
            mark refold;
            let { whole: tree } = refold_to_root(node, root, { c: c, t: t });
            have rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model))) by {
                rewrite(tree.model == at(refold, plug(c.model, t.model)));
                assumption();
            }
            have is_rb_root(tree.model) == 1 by {
                rewrite(tree.model == at(refold, plug(c.model, t.model)));
                assumption();
            }
            have rb_tree_parent_consistent(tree.model) == 1 by {
                rewrite(tree.model == at(refold, plug(c.model, t.model)));
                assumption();
            }
            step();
            simp();
        },
    }
}

void rb_insert_color(struct rb_node* node, struct rb_root* root) {
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces tree: rb_root_at(root);
    ensures rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(tree.model) == 1;
    ensures rb_tree_parent_consistent(tree.model) == 1;
} by {
    let { tree: tree } = step(__rb_insert(node, root, dummy_rotate), { c: c, t: t });
    step();
    simp();
}
