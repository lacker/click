verifying "rb_insert_color.c";

import "../rbtree-model/rbtree_model.click";
import "../rbtree-model/rbtree_resources.click";
import "rbtree_insert_rotation.click";
import click::separation;

// Retain the complete tagged parent relation while other links change.
resource insert_parent_tag(p: struct rb_node*, up: struct rb_node*) {
    field color: Color;
    owns p->__rb_parent_color;
    fact aligned(up, 8);
    fact p->__rb_parent_color == address(up) + (p->__rb_parent_color & 1);
    fact ((p->__rb_parent_color & ~3) as (struct rb_node *)) == up;
    fact (p->__rb_parent_color & 1) == color_bit(color);
}

spec enum InsertLink { To(struct rb_node*), }

resource insert_left_link(p: struct rb_node*) {
    field link: InsertLink;
    match link { InsertLink::To(child) => {
            owns p->rb_left;
            fact p->rb_left == child;
        }, }
}

resource insert_right_link(p: struct rb_node*) {
    field link: InsertLink;
    match link { InsertLink::To(child) => {
            owns p->rb_right;
            fact p->rb_right == child;
        }, }
}

theorem ctx_rb_red_focus_not_top(ctx: Context, bh: Nat) {
    requires ctx_rb(ctx, bh, Color::Red) == 1;

    ensures ctx != Context::Top by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                have ctx_rb(Context::Top, bh, Color::Red) != 1 by {
                    unfold(ctx_rb(Context::Top, bh, Color::Red));
                    unfold(color_black(Color::Red));
                    close();
                }
                close();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                close();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                close();
            }
        }
    }
}

theorem color_bit_zero_is_red(color: Color) {
    requires color_bit(color) == 0;

    ensures color == Color::Red by {
        let ih = induct(color);
        match color {
            Color::Red => {
                close();
            }
            Color::Black => {
                have color_bit(Color::Black) != 0;
                close();
            }
        }
    }
}

theorem color_bit_one_is_black(color: Color) {
    requires color_bit(color) == 1;

    ensures color == Color::Black by {
        let ih = induct(color);
        match color {
            Color::Red => {
                have color_bit(Color::Red) != 1;
                close();
            }
            Color::Black => {
                close();
            }
        }
    }
}

theorem rb_root_black_node_color_bit(node: struct rb_node*, parent: struct rb_node*,
                                     color: Color, left: RbTree, right: RbTree) {
    requires rb_root_black(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures color_bit(color) == 1 by {
        let ih = induct(color);
        match color {
            Color::Red => {
                have rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) != 1 by {
                    unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)));
                    close();
                }
                close();
            }
            Color::Black => {
                unfold(color_bit(Color::Black));
                close();
            }
        }
    }
}

theorem ctx_node_is_top_null(p: struct rb_node*) {
    requires ctx_node_is(Context::Top, p) == 1;

    ensures p == 0;
}

theorem rb_ptr_transitive(a: struct rb_node*, b: struct rb_node*, c: struct rb_node*) {
    requires a == b;
    requires a == c;

    ensures c == b by close();
}

theorem rb_has_parent_node(identity: struct rb_node*, parent: struct rb_node*, color: Color,
                           left: RbTree, right: RbTree, q: struct rb_node*) {
    requires rb_has_parent(RbTree::Node(identity, parent, color, left, right), q) == 1;

    ensures parent == q;
}

theorem rb_has_parent_same(sub: RbTree, q: struct rb_node*, p: struct rb_node*) {
    requires rb_has_parent(sub, q) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures p == q by {
        let ih = induct(sub);
        match sub {
            RbTree::Empty => {
                have rb_has_parent(RbTree::Empty, q) != 1;
                close();
            }
            RbTree::Node(identity, parent, color, left, right) => {
                apply(rb_has_parent_node(identity, parent, color, left, right, q));
                apply(rb_has_parent_node(identity, parent, color, left, right, p));
                apply(rb_ptr_transitive(parent, q, p));
                close();
            }
        }
    }
}

theorem ctx_holds_top_parent(sub: RbTree) {
    requires ctx_holds(Context::Top, sub) == 1;

    ensures rb_has_parent(sub, 0) == 1 by {
        unfold(ctx_holds(Context::Top, sub));
        rewrite(rb_has_parent(sub, 0), ctx_holds(Context::Top, sub));
        close();
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
        rewrite(rb_has_parent(sub, cid), ctx_holds(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        close();
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
        rewrite(rb_has_parent(sub, cid), ctx_holds(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
                sub));
        close();
    }
}

theorem ctx_node_is_from_parent(ctx: Context, sub: RbTree, p: struct rb_node*) {
    requires ctx_holds(ctx, sub) == 1;
    requires rb_has_parent(sub, p) == 1;

    ensures ctx_node_is(ctx, p) == 1 by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                apply(ctx_holds_top_parent(sub));
                apply(rb_has_parent_same(sub, 0, p));
                have ctx_node_is(Context::Top, p) == 1 by {
                    unfold(ctx_node_is(Context::Top, p));
                    close();
                }
                close();
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
                    close();
                }
                close();
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
                    close();
                }
                close();
            }
        }
    }
}

theorem ctx_node_is_left_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                  ccolor: Color, sibling_model: RbTree, up_model: Context,
                                  p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid;
}

theorem ctx_node_is_right_identity(cid: struct rb_node*, grandparent: struct rb_node*,
                                   ccolor: Color, sibling_model: RbTree, up_model: Context,
                                   p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
        p) == 1;

    ensures p == cid;
}

theorem ctx_reroot_top_fixed(p: struct rb_node*) {
    ensures Context::Top == ctx_reroot(Context::Top, p) by {
        unfold(ctx_reroot(Context::Top, p));
        close();
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
            rewrite(p, cid);
            close();
        } else {
            have ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                have (if p == cid { 1 } else { 0 }) == 0 by close();
                rewrite(if p == cid { 1 } else { 0 }, 0);
                close();
            }
            close();
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
            rewrite(p, cid);
            close();
        } else {
            have ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                    Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                have (if p == cid { 1 } else { 0 }) == 0 by close();
                rewrite(if p == cid { 1 } else { 0 }, 0);
                close();
            }
            close();
        }
    }
}

theorem ctx_reroot_fixed(ctx: Context, p: struct rb_node*) {
    requires ctx_node_is(ctx, p) == 1;

    ensures ctx == ctx_reroot(ctx, p) by {
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                apply(ctx_reroot_top_fixed(p));
                close();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_left_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                close();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_right_fixed(cid, grandparent, ccolor, sibling_model,
                    up_model, p));
                close();
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
        let ih = induct(ctx);
        match ctx {
            Context::Top => {
                unfold(ctx_depth(Context::Top));
                close();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                close() using { 0 <= ctx_depth(up_model); };
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ih(up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                close() using { 0 <= ctx_depth(up_model); };
            }
        }
    }
}

theorem rb_parent_consistent_parent_is(t: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(t, p) == 1;
    ensures rb_parent_is(t, p) == 1 by {
        let ih = induct(t);
        match t {
            RbTree::Empty => {
                unfold(rb_parent_is(RbTree::Empty, p));
                close();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_parent(node, parent, color, left, right, p));
                apply(rb_parent_is_node_is(node, parent, color, left, right, p));
                rewrite(rb_parent_is(RbTree::Node(node, parent, color, left, right), p), rb_node_is(parent, p));
                close();
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
            let whole = fold(rb_root_at(root), { model: t.model, tree: t });
            have whole.model == plug(old(c.model), old(t.model));
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                unfold(rb_tree_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model)));
                close();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0));
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0));
            apply(rb_parent_consistent_parent_is(t.model, identity));
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model), left: t, right: s });
            apply(ctx_depth_is_nonnegative(up_model));
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model), Context::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                close();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model));
            have plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1;
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model));
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                unfold(rb_tree_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model)));
                close();
            }
            apply(plug_parent_consistent_ctx(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0));
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0));
            apply(rb_parent_consistent_parent_is(t.model, identity));
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)), left: s, right: t });
            apply(ctx_depth_is_nonnegative(up_model));
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model), Context::Right(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                close();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model));
            have plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)));
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1;
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model));
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
}

theorem dummy_rotate_is_augment_rotate()
    executes dummy_rotate(struct rb_node* old, struct rb_node* new) {
    ensures AugmentRotate(&dummy_rotate) by {
        step() {
            requires new != 0 by close();
        }
    }
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
        RbTree::Empty => { close(); },
        RbTree::Node(identity, node_parent, color, left_model, right_model) => {
            have color_bit(color) == 0 by {
                unfold(rb_color_bit(RbTree::Node(identity, node_parent, color, left_model, right_model)));
                close();
            }
            let { left: l, right: r } = unfold(t);
            have (node->__rb_parent_color & 1) == rb_color_bit(old(t.model)) by {
                rewrite(old(t.model), RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_color_bit(
                    RbTree::Node(identity, node_parent, color, left_model, right_model)));
                close();
            }
            have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == node_parent by close();
            let t = fold(rb_at(node), { model: RbTree::Node(identity, node_parent, color, left_model, right_model), left: l, right: r });
            step(); // Declare parent.
            let { left: l, right: r } = unfold(t);
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1), color_bit(color));
                rewrite(color_bit(color), 0);
                close();
            }
            let load_tag = fold(insert_red_tag(node), { link: InsertParent::To(node_parent) });

            let { after: load_tag } = step(rb_red_parent, { before: load_tag });
            unfold(load_tag);
            let t = fold(rb_at(node), { model: RbTree::Node(identity, node_parent, color, left_model, right_model), left: l, right: r });
            step(); // Initialize parent.
            step(); // Declare gparent.
            step(); // Declare tmp.
            have rb_has_parent(t.model, node_parent) == 1 by {
                rewrite(t.model, RbTree::Node(identity, node_parent, color, left_model, right_model));
                unfold(rb_has_parent(
                    RbTree::Node(identity, node_parent, color, left_model, right_model),
                    node_parent));
                close();
            }
            have ctx_node_is(c.model, node_parent) == 1 by {
                apply(ctx_node_is_from_parent(c.model, t.model, node_parent));
                close();
            }
            have c.model == ctx_reroot(c.model, node_parent) by {
                apply(ctx_reroot_fixed(c.model, node_parent));
                close();
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

                initialize by close();
                maintain by {
                    match t.model {
                        RbTree::Empty => { close(); },
                        RbTree::Node(nid, nparent, ncolor, nleft, nright) => {
                            if parent == 0 {
                                match c.model {
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor, csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor, csib, cup, parent));
                                            close();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        have parent != 0 by {
                                            rewrite(parent, cid);
                                            close();
                                        }
                                        close();
                                    },
                                    Context::Right(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Right(cid, cgp, ccolor, csib, cup), parent) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor, csib, cup, parent));
                                            close();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        have parent != 0 by {
                                            rewrite(parent, cid);
                                            close();
                                        }
                                        close();
                                    },
                                    Context::Top => {
                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                            close();
                                        }
                                        have nparent == parent by {
                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent));
                                            close();
                                        }
                                        have nparent == 0 by {
                                            rewrite(nparent, parent);
                                            close();
                                        }
                                        have RbTree::Node(nid, nparent, Color::Black, nleft, nright) == rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black) by {
                                            unfold(rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            close();
                                        }
                                        have is_rb(RbTree::Node(nid, nparent, ncolor, nleft, nright)) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                            close();
                                        }
                                        have is_rb_root(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == 1 by {
                                            apply(ctx_insert_root_exit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            close();
                                        }
                                        have is_rb_root(plug(Context::Top, RbTree::Node(nid, nparent, Color::Black, nleft, nright))) == 1 by {
                                            rewrite(RbTree::Node(nid, nparent, Color::Black, nleft, nright), rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            close();
                                        }
                                        have rb_inorder(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))) == rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))) by {
                                            apply(plug_recolor_inorder(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            close();
                                        }
                                        have rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, Color::Black, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(RbTree::Node(nid, nparent, Color::Black, nleft, nright), rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            rewrite(rb_inorder(plug(Context::Top, rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black))), rb_inorder(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            close();
                                        }
                                        have rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            rewrite(rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)), 0), rb_tree_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright))));
                                            rewrite(Context::Top, c.model);
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                            close();
                                        }
                                        have rb_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), 0) == 1 by {
                                            unfold(plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), plug(Context::Top, RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                            close();
                                        }
                                        have rb_parent_consistent(rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black), 0) == 1 by {
                                            apply(rb_recolor_parent_consistent(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black, 0));
                                            close();
                                        }
                                        have rb_parent_consistent(plug(Context::Top, RbTree::Node(nid, nparent, Color::Black, nleft, nright)), 0) == 1 by {
                                            unfold(plug(Context::Top, RbTree::Node(nid, nparent, Color::Black, nleft, nright)));
                                            rewrite(RbTree::Node(nid, nparent, Color::Black, nleft, nright), rb_recolor(RbTree::Node(nid, nparent, ncolor, nleft, nright), Color::Black));
                                            close();
                                        }
                                        let { left: l, right: r } = unfold(t);
                                        step();
                                        step();
                                        have node->__rb_parent_color == 1 by close() using {
                                            node->__rb_parent_color == address(0) + 1;
                                        };
                                        have (node->__rb_parent_color & 1)
                                            == color_bit(Color::Black) by {
                                            rewrite(node->__rb_parent_color, 1);
                                            unfold(color_bit(Color::Black));
                                            close();
                                        }
                                        have ((node->__rb_parent_color & ~3) as (struct rb_node *)) == 0 by {
                                            rewrite(node->__rb_parent_color, 1);
                                            close();
                                        }
                                        let t = fold(rb_at(node),
                                            {
                                            model: RbTree::Node(nid, nparent, Color::Black, nleft, nright),
                                            left: l, right: r
                                        });
                                        have is_rb_root(plug(c.model, t.model)) == 1 by {
                                            rewrite(c.model, Context::Top);
                                            rewrite(t.model, RbTree::Node(nid, nparent, Color::Black, nleft, nright));
                                            close();
                                        }
                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(c.model, Context::Top);
                                            rewrite(t.model, RbTree::Node(nid, nparent, Color::Black, nleft, nright));
                                            close();
                                        }
                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                            rewrite(c.model, Context::Top);
                                            rewrite(t.model, RbTree::Node(nid, nparent, Color::Black, nleft, nright));
                                            close();
                                        }
                                        step();
                                    },
                                }
                            } else {
                                match c.model {
                                    Context::Top => {
                                        have ctx_node_is(Context::Top, parent) == 1 by {
                                            rewrite(Context::Top, c.model);
                                            close();
                                        }
                                        unfold(ctx_node_is(Context::Top, parent));
                                        have parent == 0;
                                        close();
                                    },
                                    Context::Left(cid, cgp, ccolor, csib, cup) => {
                                        have ctx_node_is(Context::Left(cid, cgp, ccolor,
                                            csib, cup), parent) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_left_identity(cid, cgp, ccolor,
                                                csib, cup, parent));
                                            close();
                                        }
                                        have ctx_rb(Context::Left(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model)));
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have rb_inorder(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model))
                                            == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have rb_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(rb_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model), 0), rb_tree_parent_consistent(plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have ctx_almost_rb_insert(Context::Left(cid, cgp, ccolor, csib, cup), black_height(t.model)) == 1 by {
                                            rewrite(Context::Left(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1), color_bit(ccolor));
                                                    rewrite(ccolor, Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    close();
                                                }
                                                have ctx_almost_rb_insert(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1 by {
                                                    rewrite(Color::Black, ccolor);
                                                    close();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1 by {
                                                    apply(ctx_black_frame_left_restores(cid, cgp, csib, cup, black_height(t.model), rb_color(t.model)));
                                                    close();
                                                }
                                                have is_rb_root(plug(Context::Left(cid, cgp, Color::Black, csib, cup), t.model)) == 1 by {
                                                    apply(ctx_insert_black_parent_exit(Context::Left(cid, cgp, Color::Black, csib, cup), t.model));
                                                    close();
                                                }
                                                have (parent->__rb_parent_color & 1) != 0 by {
                                                    rewrite((parent->__rb_parent_color & 1), 1);
                                                    close();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    {
                                                    model: Context::Left(cid, cgp, ccolor,
                                                        csib, cup),
                                                    sibling: cs, up: cu
                                                });
                                                have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                    rewrite(c.model, Context::Left(cid, cgp, ccolor, csib, cup));
                                                    rewrite(ccolor, Color::Black);
                                                    close();
                                                }
                                                have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                }
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor, Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    close();
                                                }
                                                have ctx_rb(Context::Left(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red, ccolor);
                                                    close();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_left_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black));
                                                    rewrite(cu.model, cup);
                                                    close();
                                                }
                                                step();
                                                step();
                                                let load_tag = fold(insert_red_tag(parent), { link: InsertParent::To(cgp) });
                                                let { left: call_left, right: call_right } = unfold(t);
                                                have separate(load_tag, memory(node->rb_right)) by close();
                                                have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_right)) by close();
                                                have separate(load_tag, memory(node->rb_left)) by close();
                                                have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_left)) by close();
                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, nparent, ncolor, nleft, nright), left: call_left, right: call_right });
                                                mark before_gparent_call;

                                                let { after: load_tag } = step(rb_red_parent, { before: load_tag });
                                                unfold(load_tag);
                                                step(); // Assign the decoded grandparent.
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model)));
                                                    close();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    close();
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup), cu.model);
                                                        rewrite(cu.model, cup);
                                                        close();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp));
                                                        close();
                                                    }
                                                    have ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup), cu.model);
                                                        close();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                    mark before_grandparent_links;
                                                    have separate(memory(gparent->rb_right), memory(gparent->rb_left)) by { close(); }
                                                    have separate(memory(gparent->rb_right), memory(parent->rb_right)) by { close(); }
                                                    have separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)) by { close(); }
                                                    have separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)) by { close(); }
                                                    have at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { close(); }
                                                    have separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right)) by { close(); }
                                                    have separate(memory(gparent->__rb_parent_color), memory(parent->rb_left)) by { close(); }
                                                        have gparent->rb_left == parent by { rewrite(gparent, uid); rewrite(parent, cid); close(); }
                                                        let read_focus_link = fold(insert_left_link(gparent), { link: InsertLink::To(parent) });
                                                        let rotation_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                        have gparent->rb_right == uid->rb_right by { rewrite(gparent, uid); close(); }
                                                        have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(gparent->rb_right)) by close();
                                                        have parent->rb_left == cid->rb_left by { rewrite(parent, cid); close(); }
                                                        have parent->rb_left == node by close();
                                                        have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(parent->rb_left)) by close();
                                                        step(); // Load the uncle into tmp.
                                                        have tmp == at(before_grandparent_links, uid->rb_right) by close();
                                                        have separate(statement(1).statement(3).footprint, memory(gparent->rb_right)) by {
                                                            close();
                                                        }
                                                        have gparent->rb_right == at(before_grandparent_links, gparent->rb_right) by {
                                                            preserve(memory(gparent->rb_right), statement(1).statement(3));
                                                        }
                                                        have separate(statement(1).statement(3).footprint, memory(parent->rb_left)) by {
                                                            close();
                                                        }
                                                        have parent->rb_left == at(before_grandparent_links, parent->rb_left) by {
                                                            preserve(memory(parent->rb_left), statement(1).statement(3));
                                                        }
                                                        unfold(read_focus_link);
                                                    mark before_uncle_pointer_changes;
                                                    have at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)) by { close(); }
                                                    have at(before_uncle_pointer_changes, parent->rb_left == node) by { close(); }
                                                    have separate(memory(parent->rb_left), memory(gparent->rb_left)) by { close(); }
                                                    have separate(memory(parent->rb_left), memory(parent->rb_right)) by { close(); }
                                                    have separate(memory(parent->rb_left), memory(gparent->__rb_parent_color)) by { close(); }
                                                    have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { close(); }
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr));
                                                                    close();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor));
                                                                    close();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                    close();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp, gparent);
                                                                    rewrite(uncolor, Color::Black);
                                                                    close();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black, uncolor);
                                                                    close();
                                                                }
                                                                have tmp == at(before_uncle_pointer_changes, tmp) by { close(); }
                                                                have tmp->rb_left == at(before_uncle_pointer_changes, tmp)->rb_left by {
                                                                    rewrite(tmp, at(before_uncle_pointer_changes, tmp)); close();
                                                                }
                                                                have tmp->rb_right == at(before_uncle_pointer_changes, tmp)->rb_right by {
                                                                    rewrite(tmp, at(before_uncle_pointer_changes, tmp)); close();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    close();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    close();
                                                                }
                                                            },
                                                        }
                                                        have cup == Context::Left(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup, Context::Left(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor, Color::Black);
                                                            rewrite(uid, gparent);
                                                            close();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent));
                                                            close();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor), rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor));
                                                            close();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model, RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent, cid);
                                                            rewrite(ncolor, Color::Red);
                                                            close();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        apply(ctx_insert_case3_left_step(ugp, gparent, cid, nid, nleft, nright, csib, usib, uup));
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                                rewrite(Color::Red, ncolor); close();
                                                        }
                                                            have node == at(before_gparent_call, node) by { close(); }
                                                            have node->rb_left == at(before_gparent_call, node)->rb_left by {
                                                                rewrite(node, at(before_gparent_call, node)); close();
                                                            }
                                                            have node->rb_right == at(before_gparent_call, node)->rb_right by {
                                                                rewrite(node, at(before_gparent_call, node)); close();
                                                            }
                                                            let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright), left: nl_at, right: nr_at });
                                                            let held_uncle_link = fold(insert_right_link(gparent), { link: InsertLink::To(at(before_uncle_pointer_changes, tmp)) });
                                                            let held_focus_link = fold(insert_left_link(parent), { link: InsertLink::To(node) });
                                                        match cs.model ensuring {
                                                            owns sn: rb_at(tmp);
                                                                owns rotation_tag: insert_parent_tag(gparent, ugp);
                                                                fact rotation_tag.color == ucolor;
                                                                fact gparent->rb_left == tmp;
                                                                fact parent->rb_right == gparent;
                                                            fact sn.model == rb_reparent(csib, gparent);
                                                            fact gparent->rb_right == at(before_uncle_pointer_changes, tmp);
                                                            fact parent->rb_left == node;
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(cs);
                                                                    have parent->rb_right == cid->rb_right by { rewrite(parent, cid); close(); }
                                                                    mark before_sibling_read;
                                                                step();
                                                                step();
                                                                    have tmp == at(before_sibling_read, cid->rb_right) by close();
                                                                step();
                                                                step();
                                                                step();
                                                                    let written_sibling_link = fold(insert_left_link(gparent), { link: InsertLink::To(tmp) });
                                                                    step();
                                                                    let written_grandparent_link = fold(insert_right_link(parent), { link: InsertLink::To(gparent) });
                                                                step();
                                                                step();
                                                                    unfold(written_sibling_link);
                                                                    unfold(written_grandparent_link);
                                                                have rb_reparent(csib, gparent) == RbTree::Empty by {
                                                                    rewrite(csib, RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent)); close();
                                                                }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent), RbTree::Empty);
                                                                    close();
                                                                }
                                                                    unfold(held_uncle_link);
                                                                    have gparent->rb_right == at(before_uncle_pointer_changes, tmp) by close();
                                                                    unfold(held_focus_link);
                                                                    have parent->rb_left == node by close();
                                                                    have gparent->rb_left == tmp by close();
                                                                    have parent->rb_right == gparent by close();
                                                            },
                                                            RbTree::Node(sx, sp, scol, sl, sr) => {
                                                                let { left: sl_at, right: sr_at } = unfold(cs);
                                                                    have sx == cid->rb_right by close();
                                                                    have sx->rb_left == cid->rb_right->rb_left by { rewrite(sx, cid->rb_right); close(); }
                                                                    have sx->rb_right == cid->rb_right->rb_right by { rewrite(sx, cid->rb_right); close(); }
                                                                    let saved_child_left = fold(insert_left_link(sx), { link: InsertLink::To(sx->rb_left) });
                                                                    let saved_child_right = fold(insert_right_link(sx), { link: InsertLink::To(sx->rb_right) });
                                                                    have parent->rb_right == cid->rb_right by { rewrite(parent, cid); close(); }
                                                                    mark before_sibling_read;
                                                                step();
                                                                step();
                                                                    have tmp == at(before_sibling_read, cid->rb_right) by close();
                                                                    have tmp == sx by close();
                                                                    let { left: node_l, right: node_r } = unfold(t);
                                                                    have separate(memory(node->__rb_parent_color), memory(sx->__rb_parent_color)) by close();
                                                                    step(); // Disjoint owned nodes rule out the triangle branch.
                                                                    let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright), left: node_l, right: node_r });
                                                                have gparent == uid by { close(); }
                                                                have tmp == sx by { close(); }
                                                                have rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1 by {
                                                                    rewrite(RbTree::Node(sx, sp, scol, sl, sr), csib);
                                                                    close();
                                                                }
                                                                have color_bit(scol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(sx, sp, scol, sl, sr));
                                                                    close();
                                                                }
                                                                have rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr) by {
                                                                    rewrite(csib, RbTree::Node(sx, sp, scol, sl, sr));
                                                                    unfold(rb_reparent(RbTree::Node(sx, sp, scol, sl, sr), gparent)); close();
                                                                }
                                                                step();
                                                                step();
                                                                    let written_sibling_link = fold(insert_left_link(gparent), { link: InsertLink::To(tmp) });
                                                                step();
                                                                    let written_grandparent_link = fold(insert_right_link(parent), { link: InsertLink::To(gparent) });
                                                                step();
                                                                    mark before_sibling_recolor;
                                                                    have separate(memory(sx->rb_left), memory(sx->__rb_parent_color)) by close();
                                                                    have separate(memory(sx->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp, sx); close(); }
                                                                    have separate(memory(sx->rb_right), memory(sx->__rb_parent_color)) by close();
                                                                    have separate(memory(sx->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp, sx); close(); }
                                                                step();
                                                                    have separate(statement(1).statement(4).statement(5).statement(0).footprint, memory(sx->rb_left)) by { close(); }
                                                                    have sx->rb_left == at(before_sibling_recolor, sx->rb_left) by { preserve(memory(sx->rb_left), statement(1).statement(4).statement(5).statement(0)); }
                                                                    have separate(statement(1).statement(4).statement(5).statement(0).footprint, memory(sx->rb_right)) by { close(); }
                                                                    have sx->rb_right == at(before_sibling_recolor, sx->rb_right) by { preserve(memory(sx->rb_right), statement(1).statement(4).statement(5).statement(0)); }
                                                                    unfold(written_sibling_link);
                                                                    unfold(written_grandparent_link);
                                                                    unfold(saved_child_left);
                                                                    unfold(saved_child_right);
                                                                    have tmp->rb_left == sx->rb_left by { rewrite(tmp, sx); close(); }
                                                                    have tmp->rb_right == sx->rb_right by { rewrite(tmp, sx); close(); }
                                                                    have aligned(gparent, 8) by { rewrite(gparent, uid); close(); }
                                                                    have (address(gparent) | 1) == address(gparent) + 1 by { close() using { aligned(gparent, 8); }; }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Node(sx, gparent, scol, sl, sr), left: sl_at, right: sr_at });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent), RbTree::Node(sx, gparent, scol, sl, sr));
                                                                    close();
                                                                }
                                                                    unfold(held_uncle_link);
                                                                    have gparent->rb_right == at(before_uncle_pointer_changes, tmp) by close();
                                                                    unfold(held_focus_link);
                                                                    have parent->rb_left == node by close();
                                                                    have gparent->rb_left == tmp by close();
                                                                    have parent->rb_right == gparent by close();
                                                            },
                                                        }
                                                            unfold(rotation_tag);
                                                            have ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp by close();
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1), color_bit(ucolor));
                                                            rewrite(ucolor, Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            close();
                                                        }
                                                            have ctx_node_is(uu.model, ugp) == 1 by close();
                                                            have ctx_identity(uu.model) == ugp by { apply(ctx_node_is_identity(uu.model, ugp)); }
                                                            have gparent->__rb_parent_color == address(ugp) + 1 by close();
                                                            apply(insert_black_context_word(uu.model, ugp));
                                                            have ctx_parent_word(uu.model, gparent->__rb_parent_color) == 1 by {
                                                                rewrite(gparent->__rb_parent_color, address(ugp) + 1);
                                                                close();
                                                            }
                                                            let outer_uncle_link = fold(insert_right_link(gparent), { link: InsertLink::To(at(before_uncle_pointer_changes, tmp)) });
                                                            let outer_focus_link = fold(insert_left_link(parent), { link: InsertLink::To(node) });
                                                            let moved_sibling_link = fold(insert_left_link(gparent), { link: InsertLink::To(tmp) });
                                                            let moved_grandparent_link = fold(insert_right_link(parent), { link: InsertLink::To(gparent) });
                                                            let { after: uu } = step(__rb_rotate_set_parents, { c: uu });
                                                            unfold(moved_sibling_link);
                                                            unfold(moved_grandparent_link);
                                                            unfold(outer_uncle_link);
                                                            unfold(outer_focus_link);
                                                            have rb_parent_is(rb_reparent(csib, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(csib, gparent));
                                                                close();
                                                            }
                                                            have parent == cid by close();
                                                            have aligned(cid, 8) by close();
                                                            have gparent->__rb_parent_color == address(cid) by { rewrite(cid, parent); close(); }
                                                            have (gparent->__rb_parent_color & 1) == 0 by {
                                                                rewrite(gparent->__rb_parent_color, address(cid));
                                                                close() using { aligned(cid, 8); };
                                                            }
                                                            have gparent->__rb_parent_color == address(cid) + (gparent->__rb_parent_color & 1) by { rewrite((gparent->__rb_parent_color & 1), 0); close(); }
                                                            have ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == cid by { rewrite(cid, parent); close(); }
                                                            unfold(color_bit(Color::Red));
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), left: sn, right: un });
                                                            have rb_parent_is(RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), cid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), cid));
                                                                close();
                                                            }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                close();
                                                            }
                                                        let c = fold(ctx_at(node, root), { model: Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup), sibling: gn, up: uu });
                                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(c.model, Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup));
                                                            rewrite(t.model, RbTree::Node(nid, cid, Color::Red, nleft, nright));
                                                            rewrite(rb_inorder(plug(Context::Left(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, rb_reparent(csib, gparent), usib), uup), RbTree::Node(nid, cid, Color::Red, nleft, nright))), rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                            close();
                                                        }
                                                        have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                            unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                        }
                                                        step();
                                                        step();
                                                    } else {
                                                        unfold(rotation_tag);
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1), color_bit(uncolor));
                                                                            rewrite(uncolor, Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                            close();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                            close();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp, gparent);
                                                                            rewrite(uncolor, Color::Red);
                                                                            close();
                                                                        }
                                                                        have cup == Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup, Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib, RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor, Color::Black);
                                                                            rewrite(uid, gparent);
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, t.model, csib)) == 1 by {
                                                                            apply(ctx_insert_cursor_left_parent(cid, cgp, t.model, csib, cup));
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(gparent, cgp);
                                                                            close();
                                                                        }
                                                                        apply(ctx_insert_case1_left_step(ugp, gparent, cid, unid, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib, unl, unr, uup));
                                                                        have rb_inorder(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib)), plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0) == 1 by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib)), plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0), rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0));
                                                                            close();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr))));
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                            let flip_tmp_rb_left = fold(insert_left_link(tmp), { link: InsertLink::To(tmp->rb_left) });
                                                                            let flip_tmp_rb_right = fold(insert_right_link(tmp), { link: InsertLink::To(tmp->rb_right) });
                                                                            let flip_parent_rb_left = fold(insert_left_link(parent), { link: InsertLink::To(parent->rb_left) });
                                                                            let flip_parent_rb_right = fold(insert_right_link(parent), { link: InsertLink::To(parent->rb_right) });
                                                                            let flip_gparent_rb_left = fold(insert_left_link(gparent), { link: InsertLink::To(gparent->rb_left) });
                                                                            let flip_gparent_rb_right = fold(insert_right_link(gparent), { link: InsertLink::To(gparent->rb_right) });
                                                                            let flip_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                                        step();
                                                                        step();
                                                                            unfold(flip_tmp_rb_left);
                                                                            unfold(flip_tmp_rb_right);
                                                                            have aligned(gparent, 8) by { rewrite(gparent, uid); close(); }
                                                                            have (address(gparent) | 1) == address(gparent) + 1 by {
                                                                                close() using { aligned(gparent, 8); };
                                                                            }
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                            step();
                                                                            unfold(flip_parent_rb_left);
                                                                            unfold(flip_parent_rb_right);
                                                                            have parent->__rb_parent_color == (address(gparent) | 1) by close();
                                                                            have parent->__rb_parent_color == address(gparent) + 1 by close();
                                                                            have (parent->__rb_parent_color & 1) == 1 by close();
                                                                            have parent->__rb_parent_color == address(gparent) + (parent->__rb_parent_color & 1) by close();
                                                                            have ((parent->__rb_parent_color & ~3) as (struct rb_node *)) == gparent by close();
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), left: t, right: cs });
                                                                        step();
                                                                            unfold(flip_tag);
                                                                        step();
                                                                            step();
                                                                            have parent == ugp by close();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp));
                                                                            close();
                                                                        }
                                                                            unfold(flip_gparent_rb_left);
                                                                            unfold(flip_gparent_rb_right);
                                                                            have aligned(ugp, 8) by close();
                                                                            have gparent->__rb_parent_color == address(ugp) by close();
                                                                            have (gparent->__rb_parent_color & 1) == 0 by {
                                                                                rewrite(gparent->__rb_parent_color, address(ugp));
                                                                                close() using { aligned(ugp, 8); };
                                                                            }
                                                                            have gparent->__rb_parent_color == address(ugp) + (gparent->__rb_parent_color & 1) by close();
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), RbTree::Node(unid, gparent, Color::Black, unl, unr)), left: pn, right: un });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor, Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            close();
                                                                        }
                                                                        close();
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); close();
                                                                }
                                                                close();
                                                            },
                                                        }
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup), cu.model);
                                                        rewrite(cu.model, cup);
                                                        close();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp));
                                                        close();
                                                    }
                                                    have ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup), cu.model);
                                                        close();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                        mark triangle_before_uncle_load;
                                                        have gparent->rb_left == uid->rb_left by { rewrite(gparent, uid); close(); }
                                                        have gparent->rb_right == parent by { rewrite(gparent, uid); rewrite(parent, cid); close(); }
                                                        let triangle_uncle_link = fold(insert_left_link(gparent), { link: InsertLink::To(uid->rb_left) });
                                                        let triangle_parent_link = fold(insert_right_link(gparent), { link: InsertLink::To(parent) });
                                                        let triangle_focus_link = fold(insert_left_link(parent), { link: InsertLink::To(node) }) by { rewrite(parent, cid); close(); }
                                                        let triangle_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                    step();
                                                        unfold(triangle_parent_link);
                                                        have tmp == parent by close();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                            fact gparent->rb_left == tmp;
                                                                fact node->rb_right == at(triangle_before_uncle_load, node->rb_right);
                                                                fact node->rb_left == at(triangle_before_uncle_load, node->rb_left);
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                    have unid == uid->rb_left by close();
                                                                    have unid->rb_left == uid->rb_left->rb_left by { rewrite(unid, uid->rb_left); close(); }
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(unid->rb_left)) by close();
                                                                    let triangle_saved_rb_left = fold(insert_left_link(unid), { link: InsertLink::To(unid->rb_left) });
                                                                    have unid->rb_right == uid->rb_left->rb_right by { rewrite(unid, uid->rb_left); close(); }
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(unid->rb_right)) by close();
                                                                    let triangle_saved_rb_right = fold(insert_right_link(unid), { link: InsertLink::To(unid->rb_right) });

                                                                    let triangle_uncle_tag = fold(insert_parent_tag(uid->rb_left, unp), { color: uncolor });
                                                                step();
                                                                    mark triangle_before_middle_load;
                                                                step();
                                                                    unfold(triangle_uncle_tag);
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr));
                                                                    close();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor));
                                                                    close();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                    close();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp, gparent);
                                                                    rewrite(uncolor, Color::Black);
                                                                    close();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black, uncolor);
                                                                    close();
                                                                }
                                                                    unfold(triangle_uncle_link);
                                                                have gparent->rb_left == tmp by { close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(unid->rb_left)) by { close(); }
                                                                    have unid->rb_left == at(triangle_before_middle_load, unid->rb_left) by close();
                                                                    unfold(triangle_saved_rb_left);
                                                                    have tmp->rb_left == unid->rb_left by { rewrite(tmp, unid); close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(unid->rb_right)) by { close(); }
                                                                    have unid->rb_right == at(triangle_before_middle_load, unid->rb_right) by close();
                                                                    unfold(triangle_saved_rb_right);
                                                                    have tmp->rb_right == unid->rb_right by { rewrite(tmp, unid); close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_right) == at(statement(1).statement(4).statement(9).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_right) == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have node->rb_right == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_left) == at(statement(1).statement(4).statement(9).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_left) == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                    have node->rb_left == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                    let un = fold(rb_at(uid->rb_left), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    close();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                    unfold(triangle_uncle_link);
                                                                have gparent->rb_left == tmp by { close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_right) == at(statement(1).statement(4).statement(9).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_right) == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have node->rb_right == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_left) == at(statement(1).statement(4).statement(9).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_left) == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                    have node->rb_left == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    close();
                                                                }
                                                            },
                                                        }
                                                            unfold(triangle_focus_link);
                                                            unfold(triangle_tag);
                                                        mark triangle_uncle_pointer;
                                                        have at(triangle_uncle_pointer, gparent->rb_left == tmp) by { close(); }
                                                        have cup == Context::Right(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup, Context::Right(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor, Color::Black);
                                                            rewrite(uid, gparent);
                                                            close();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent));
                                                            close();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor), rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor));
                                                            close();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model, RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent, cid);
                                                            rewrite(ncolor, Color::Red);
                                                            close();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ctx_rb(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        apply(ctx_insert_case2_right_exit_step(ugp, gparent, cid, nid, usib, nleft, nright, csib, uup));
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                            match InsertParent::To(node->rb_left) {
                                                                InsertParent::To(original_left) => {
                                                                    have separate(memory(((&gparent) as (uint8 *))[0..8]), memory(node->rb_right)) by close();
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_right)) by close();
                                                                    have contains(at(before_gparent_call, load_tag), statement(1).statement(2).call(0).footprint) by close();
                                                                    apply(separation::contains_refl(memory(node->rb_right)));
                                                                    apply(separation::separate_restrict(at(before_gparent_call, load_tag), memory(node->rb_right), statement(1).statement(2).call(0).footprint, memory(node->rb_right)));
                                                                    have at(statement(1).statement(2).call(0).exit, node->rb_right) == at(before_gparent_call, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(2).call(0)); }
                                                                    have separate(statement(1).statement(2).assignment(gparent, 0).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_right) == at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(2).assignment(gparent, 0)); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_right) == at(statement(1).statement(2).call(0).exit, node->rb_right) by close();
                                                                    have separate(statement(1).statement(3).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(3).exit, node->rb_right) == at(statement(1).statement(3).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(3)); }
                                                                    have at(statement(1).statement(3).entry, node->rb_right) == at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_right) by close();

                                                                    have separate(memory(((&gparent) as (uint8 *))[0..8]), memory(node->rb_left)) by close();
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_left)) by close();
                                                                    have contains(at(before_gparent_call, load_tag), statement(1).statement(2).call(0).footprint) by close();
                                                                    apply(separation::contains_refl(memory(node->rb_left)));
                                                                    apply(separation::separate_restrict(at(before_gparent_call, load_tag), memory(node->rb_left), statement(1).statement(2).call(0).footprint, memory(node->rb_left)));
                                                                    have at(statement(1).statement(2).call(0).exit, node->rb_left) == at(before_gparent_call, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(2).call(0)); }
                                                                    have separate(statement(1).statement(2).assignment(gparent, 0).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_left) == at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(2).assignment(gparent, 0)); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_left) == at(statement(1).statement(2).call(0).exit, node->rb_left) by close();
                                                                    have separate(statement(1).statement(3).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(3).exit, node->rb_left) == at(statement(1).statement(3).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(3)); }
                                                                    have at(statement(1).statement(3).entry, node->rb_left) == at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_left) by close();

                                                                    have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                                        rewrite(Color::Red, ncolor);
                                                                        close();
                                                                    }
                                                                    have at(triangle_before_uncle_load, node->rb_left) == at(statement(1).statement(3).exit, node->rb_left) by close();
                                                                    have node->rb_left == at(before_gparent_call, node->rb_left) by close();
                                                                    let inner_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                                    let inner_uncle = fold(insert_left_link(gparent), { link: InsertLink::To(at(triangle_uncle_pointer, tmp)) });
                                                                    step();
                                                                    step();
                                                                    step();
                                                                    have separate(statement(1).statement(4).statement(11).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(11).exit, node->rb_left) == at(statement(1).statement(4).statement(11).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(4).statement(11)); }
                                                                    have at(statement(1).statement(4).statement(11).entry, node->rb_left) == at(triangle_uncle_pointer, node->rb_left) by close();
                                                                    have separate(memory(parent->rb_left), memory(node->rb_right)) by { close(); }
                                                                    mark before_inner_parent_right;
                                                                    have at(before_inner_parent_right, parent->rb_right == parent->rb_right) by { close(); }
                                                                    have separate(memory(parent->rb_right), memory(parent->rb_left)) by { close(); }
                                                                    have separate(memory(parent->rb_right), memory(node->rb_right)) by { close(); }
                                                                    mark before_inner_node_left;
                                                                    have at(before_inner_node_left, node->rb_left == node->rb_left) by { close(); }
                                                                    have separate(memory(node->rb_left), memory(parent->rb_left)) by { close(); }
                                                                    have separate(memory(node->rb_left), memory(node->rb_right)) by { close(); }
                                                                    let inner_parent_other = fold(insert_right_link(parent), { link: InsertLink::To(parent->rb_right) });
                                                                    let inner_node_other = fold(insert_left_link(node), { link: InsertLink::To(original_left) });
                                                                    match nr_at.model ensuring {
                                                                        owns bn: rb_at(tmp);
                                                                        owns inner_node_other: insert_left_link(node);
                                                                        fact inner_node_other.link == InsertLink::To(original_left);
                                                                        owns inner_tag: insert_parent_tag(gparent, ugp);
                                                                        fact inner_tag.color == ucolor;
                                                                        fact bn.model == rb_reparent(nright, cid);
                                                                        fact node->rb_right == parent;
                                                                        fact gparent->rb_left == at(triangle_uncle_pointer, tmp);

                                                                        fact parent->rb_left == tmp;
                                                                        fact parent->rb_right == at(before_inner_parent_right, parent->rb_right);
                                                                    } {
                                                                        RbTree::Empty => {
                                                                            unfold(nr_at);
                                                                            step();
                                                                            step();
                                                                            step();
                                                                            step();
                                                                            step();
                                                                            have rb_reparent(nright, cid) == RbTree::Empty by {
                                                                                rewrite(nright, RbTree::Empty);
                                                                                unfold(rb_reparent(RbTree::Empty, cid)); close();
                                                                            }
                                                                            unfold(inner_parent_other);
                                                                            have parent->rb_right == at(before_inner_parent_right, parent->rb_right) by close();
                                                                            have parent->rb_left == tmp by { close(); }
                                                                            unfold(inner_uncle);
                                                                            have gparent->rb_left == at(triangle_uncle_pointer, tmp) by close();
                                                                            have node->rb_right == parent by { close(); }
                                                                            let bn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                            have bn.model == rb_reparent(nright, cid) by {
                                                                                rewrite(rb_reparent(nright, cid), RbTree::Empty);
                                                                                close();
                                                                            }
                                                                        },
                                                                        RbTree::Node(bx, bp, bcol, bl, br) => {
                                                                            let { left: bl_at, right: br_at } = unfold(nr_at);
                                                                            step();
                                                                            mark before_inner_child_links;
                                                                            have separate(memory(node->rb_right), memory(tmp->__rb_parent_color)) by { close(); }

                                                                            have separate(memory(parent->rb_left), memory(tmp->__rb_parent_color)) by { close(); }
                                                                            have at(before_inner_child_links, tmp->rb_left == bx->rb_left) by { close(); }
                                                                            have at(before_inner_child_links, tmp->rb_right == bx->rb_right) by { close(); }
                                                                            have rb_root_black(RbTree::Node(bx, bp, bcol, bl, br)) == 1 by {
                                                                                rewrite(RbTree::Node(bx, bp, bcol, bl, br), nright);
                                                                                close();
                                                                            }
                                                                            have color_bit(bcol) == 1 by {
                                                                                apply(rb_root_black_node_color_bit(bx, bp, bcol, bl, br));
                                                                                close();
                                                                            }
                                                                            have rb_reparent(nright, cid) == RbTree::Node(bx, cid, bcol, bl, br) by {
                                                                                rewrite(nright, RbTree::Node(bx, bp, bcol, bl, br));
                                                                                unfold(rb_reparent(RbTree::Node(bx, bp, bcol, bl, br), cid)); close();
                                                                            }
                                                                            let middle_left = fold(insert_left_link(tmp), { link: InsertLink::To(at(before_inner_child_links, bx->rb_left)) }) by { close(); }
                                                                            let middle_right = fold(insert_right_link(tmp), { link: InsertLink::To(at(before_inner_child_links, bx->rb_right)) }) by { close(); }
                                                                            step();
                                                                            let inner_new_parent_focus = fold(insert_left_link(parent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let inner_new_node_focus = fold(insert_right_link(node), { link: InsertLink::To(parent) });
                                                                            step();
                                                                            step();
                                                                            unfold(middle_right);
                                                                            have tmp->rb_right == at(before_inner_child_links, bx->rb_right) by { close(); }
                                                                            unfold(middle_left);
                                                                            have tmp->rb_left == at(before_inner_child_links, bx->rb_left) by { close(); }
                                                                            unfold(inner_parent_other);
                                                                            have parent->rb_right == at(before_inner_parent_right, parent->rb_right) by close();
                                                                            unfold(inner_new_parent_focus);
                                                                            have parent->rb_left == tmp by { close(); }
                                                                            unfold(inner_uncle);
                                                                            have gparent->rb_left == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(inner_new_node_focus);
                                                                            have node->rb_right == parent by { close(); }
                                                                            have aligned(parent, 8) by { rewrite(parent, cid); close(); }
                                                                            have tmp->__rb_parent_color == (address(parent) | 1) by close();
                                                                            have (address(parent) | 1) == address(parent) + 1 by { close(); }
                                                                            have tmp->__rb_parent_color == address(parent) + 1 by close();
                                                                            have (tmp->__rb_parent_color & 1) == color_bit(bcol) by { rewrite(color_bit(bcol), 1); close(); }
                                                                            have tmp->__rb_parent_color == address(cid) + (tmp->__rb_parent_color & 1) by { rewrite(cid, parent); close(); }
                                                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == cid by { rewrite(cid, parent); close(); }
                                                                            let bn = fold(rb_at(tmp), { model: RbTree::Node(bx, cid, bcol, bl, br), left: bl_at, right: br_at });
                                                                            have bn.model == rb_reparent(nright, cid) by {
                                                                                rewrite(rb_reparent(nright, cid), RbTree::Node(bx, cid, bcol, bl, br));
                                                                                close();
                                                                            }
                                                                        },
                                                                    }
                                                                    mark before_inner_parent_color;
                                                                    have at(before_inner_parent_color, node->rb_right == parent) by { close(); }
                                                                    have separate(memory(node->rb_right), memory(parent->__rb_parent_color)) by { close(); }
                                                                    have at(before_inner_parent_color, gparent->rb_left == at(triangle_uncle_pointer, tmp)) by { close(); }
                                                                    have separate(memory(gparent->rb_left), memory(parent->__rb_parent_color)) by { close(); }

                                                                    have at(before_inner_parent_color, parent->rb_left == tmp) by { close(); }

                                                                    have at(before_inner_parent_color, parent->rb_right == at(before_inner_parent_right, parent->rb_right)) by { close(); }
                                                                    have separate(memory(parent->rb_right), memory(parent->__rb_parent_color)) by { close(); }
                                                                    have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { close(); }
                                                                    step();

                                                                    have contains(memory(parent->__rb_parent_color), statement(1).statement(4).statement(12).statement(4).footprint) by { close(); }
                                                                    apply(separation::contains_refl(memory(parent->rb_left)));
                                                                    apply(separation::separate_restrict(memory(parent->rb_left), memory(parent->__rb_parent_color), memory(parent->rb_left), statement(1).statement(4).statement(12).statement(4).footprint));
                                                                    have parent->rb_left == at(before_inner_parent_color, parent->rb_left) by {
                                                                        preserve(memory(parent->rb_left), statement(1).statement(4).statement(12).statement(4));
                                                                    }
                                                                    have parent->rb_left == tmp by {
                                                                        rewrite(parent->rb_left, at(before_inner_parent_color, parent->rb_left));
                                                                        close();
                                                                    }
                                                                    apply(separation::contains_refl(memory(parent->rb_right)));
                                                                    apply(separation::separate_restrict(memory(parent->rb_right), memory(parent->__rb_parent_color), memory(parent->rb_right), statement(1).statement(4).statement(12).statement(4).footprint));
                                                                    have parent->rb_right == at(before_inner_parent_color, parent->rb_right) by {
                                                                        preserve(memory(parent->rb_right), statement(1).statement(4).statement(12).statement(4));
                                                                    }
                                                                    have parent->rb_right == at(before_inner_parent_right, parent->rb_right) by {
                                                                        rewrite(parent->rb_right, at(before_inner_parent_color, parent->rb_right));
                                                                        close();
                                                                    }
                                                                    apply(separation::contains_refl(memory(gparent->rb_left)));
                                                                    apply(separation::separate_restrict(memory(gparent->rb_left), memory(parent->__rb_parent_color), memory(gparent->rb_left), statement(1).statement(4).statement(12).statement(4).footprint));
                                                                    have gparent->rb_left == at(before_inner_parent_color, gparent->rb_left) by {
                                                                        preserve(memory(gparent->rb_left), statement(1).statement(4).statement(12).statement(4));
                                                                    }
                                                                    have gparent->rb_left == at(triangle_uncle_pointer, tmp) by {
                                                                        rewrite(gparent->rb_left, at(before_inner_parent_color, gparent->rb_left));
                                                                        close();
                                                                    }
                                                                    apply(separation::contains_refl(memory(node->rb_right)));
                                                                    apply(separation::separate_restrict(memory(node->rb_right), memory(parent->__rb_parent_color), memory(node->rb_right), statement(1).statement(4).statement(12).statement(4).footprint));
                                                                    have node->rb_right == at(before_inner_parent_color, node->rb_right) by {
                                                                        preserve(memory(node->rb_right), statement(1).statement(4).statement(12).statement(4));
                                                                    }
                                                                    have node->rb_right == parent by {
                                                                        rewrite(node->rb_right, at(before_inner_parent_color, node->rb_right));
                                                                        close();
                                                                    }
                                                                    have rb_parent_is(rb_reparent(nright, cid), cid) == 1 by {
                                                                        apply(rb_reparent_parent_is(nright, cid));
                                                                        close();
                                                                    }
                                                                    have node == nid by close();
                                                                    have aligned(node, 8) by close();
                                                                    have parent->__rb_parent_color == address(node) by close();
                                                                    have (parent->__rb_parent_color & 1) == 0 by close();
                                                                    have parent->__rb_parent_color == address(nid) + (parent->__rb_parent_color & 1) by { rewrite(nid, node); close(); }
                                                                    have ((parent->__rb_parent_color & ~3) as (struct rb_node *)) == nid by { rewrite(nid, node); close(); }
                                                                    unfold(color_bit(Color::Red));
                                                                    let pn = fold(rb_at(parent), { model: RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), left: bn, right: cs });
                                                                    mark triangle_old_parent;
                                                                    have at(triangle_old_parent, node->rb_right == parent) by { close(); }
                                                                    step();
                                                                    mark before_triangle_parent_assignment;

                                                                    step();

                                                                    unfold(inner_node_other);
                                                                    have node->rb_left == original_left by close();
                                                                    mark before_outer_grandparent_tag;

                                                                    have at(before_outer_grandparent_tag, gparent->rb_left == at(triangle_uncle_pointer, tmp)) by { close(); }
                                                                    have separate(memory(gparent->rb_left), memory(gparent->rb_right)) by { close(); }
                                                                    have separate(memory(gparent->rb_left), memory(parent->rb_left)) by { close(); }
                                                                    have at(before_outer_grandparent_tag, node->rb_right == at(triangle_old_parent, parent)) by { close(); }
                                                                    have separate(memory(node->rb_right), memory(gparent->rb_right)) by { close(); }
                                                                    have separate(memory(node->rb_right), memory(parent->rb_left)) by { close(); }
                                                                    let triangle_outer_uncle = fold(insert_left_link(gparent), { link: InsertLink::To(at(triangle_uncle_pointer, tmp)) });
                                                                    let triangle_outer_other = fold(insert_right_link(node), { link: InsertLink::To(at(triangle_old_parent, parent)) });
                                                                    match nl_at.model ensuring {
                                                                        owns rn: rb_at(tmp);
                                                                        owns inner_tag: insert_parent_tag(gparent, ugp);
                                                                        fact inner_tag.color == ucolor;
                                                                        fact rn.model == rb_reparent(nleft, gparent);
                                                                        fact gparent->rb_right == tmp;
                                                                        fact parent->rb_left == gparent;
                                                                        fact node->rb_right == at(triangle_old_parent, parent);
                                                                        fact gparent->rb_left == at(triangle_uncle_pointer, tmp);

                                                                    } {
                                                                        RbTree::Empty => {
                                                                            unfold(nl_at);
                                                                            step();
                                                                            step();
                                                                            let triangle_new_gparent = fold(insert_right_link(gparent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let triangle_new_parent = fold(insert_left_link(parent), { link: InsertLink::To(gparent) });
                                                                            step();
                                                                            step();
                                                                            have rb_reparent(nleft, gparent) == RbTree::Empty by {
                                                                                rewrite(nleft, RbTree::Empty);
                                                                                unfold(rb_reparent(RbTree::Empty, gparent)); close();
                                                                            }
                                                                            unfold(triangle_outer_uncle);
                                                                            have gparent->rb_left == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(triangle_outer_other);
                                                                            have node->rb_right == at(triangle_old_parent, parent) by close();
                                                                            unfold(triangle_new_gparent);
                                                                            have gparent->rb_right == tmp by close();
                                                                            unfold(triangle_new_parent);
                                                                            have parent->rb_left == gparent by close();
                                                                            let rn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                            have rn.model == rb_reparent(nleft, gparent) by {
                                                                                rewrite(rb_reparent(nleft, gparent), RbTree::Empty);
                                                                                close();
                                                                            }
                                                                        },
                                                                        RbTree::Node(rx, rp, rcol, rl, rr) => {
                                                                            let { left: rl_at, right: rr_at } = unfold(nl_at);
                                                                            have separate(memory(((&parent) as (uint8 *))[0..8]), memory(original_left->rb_left)) by close();
                                                                            have separate(statement(1).statement(4).statement(12).statement(6).footprint, memory(original_left->rb_left)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(12).statement(6).exit, original_left->rb_left) == at(statement(1).statement(4).statement(12).statement(6).entry, original_left->rb_left) by { preserve(memory(original_left->rb_left), statement(1).statement(4).statement(12).statement(6)); }
                                                                            have separate(memory(((&parent) as (uint8 *))[0..8]), memory(original_left->rb_right)) by close();
                                                                            have separate(statement(1).statement(4).statement(12).statement(6).footprint, memory(original_left->rb_right)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(12).statement(6).exit, original_left->rb_right) == at(statement(1).statement(4).statement(12).statement(6).entry, original_left->rb_right) by { preserve(memory(original_left->rb_right), statement(1).statement(4).statement(12).statement(6)); }
                                                                            have rx == original_left by close();

                                                                            let outer_child_left = fold(insert_left_link(original_left), { link: InsertLink::To(original_left->rb_left) });
                                                                            let outer_child_right = fold(insert_right_link(original_left), { link: InsertLink::To(original_left->rb_right) });
                                                                            step();

                                                                            have rb_root_black(RbTree::Node(rx, rp, rcol, rl, rr)) == 1 by {
                                                                                rewrite(RbTree::Node(rx, rp, rcol, rl, rr), nleft);
                                                                                close();
                                                                            }
                                                                            have color_bit(rcol) == 1 by {
                                                                                apply(rb_root_black_node_color_bit(rx, rp, rcol, rl, rr));
                                                                                close();
                                                                            }
                                                                            have rb_reparent(nleft, gparent) == RbTree::Node(rx, gparent, rcol, rl, rr) by {
                                                                                rewrite(nleft, RbTree::Node(rx, rp, rcol, rl, rr));
                                                                                unfold(rb_reparent(RbTree::Node(rx, rp, rcol, rl, rr), gparent)); close();
                                                                            }
                                                                            step();
                                                                            let triangle_new_gparent = fold(insert_right_link(gparent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let triangle_new_parent = fold(insert_left_link(parent), { link: InsertLink::To(gparent) });
                                                                            step();
                                                                            mark before_outer_child_color;
                                                                            have separate(memory(original_left->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp, original_left); close(); }
                                                                            have separate(memory(original_left->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp, original_left); close(); }
                                                                            step();
                                                                            have separate(statement(1).statement(4).statement(15).statement(0).footprint, memory(original_left->rb_left)) by { close(); }
                                                                            have original_left->rb_left == at(before_outer_child_color, original_left->rb_left) by { preserve(memory(original_left->rb_left), statement(1).statement(4).statement(15).statement(0)); }
                                                                            have separate(statement(1).statement(4).statement(15).statement(0).footprint, memory(original_left->rb_right)) by { close(); }
                                                                            have original_left->rb_right == at(before_outer_child_color, original_left->rb_right) by { preserve(memory(original_left->rb_right), statement(1).statement(4).statement(15).statement(0)); }
                                                                            unfold(outer_child_left);
                                                                            unfold(outer_child_right);
                                                                            have tmp->rb_left == original_left->rb_left by { rewrite(tmp, original_left); close(); }
                                                                            have tmp->rb_right == original_left->rb_right by { rewrite(tmp, original_left); close(); }
                                                                            unfold(triangle_outer_uncle);
                                                                            have gparent->rb_left == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(triangle_outer_other);
                                                                            have node->rb_right == at(triangle_old_parent, parent) by close();
                                                                            unfold(triangle_new_gparent);
                                                                            have gparent->rb_right == tmp by close();
                                                                            unfold(triangle_new_parent);
                                                                            have parent->rb_left == gparent by close();
                                                                            let rn = fold(rb_at(original_left), { model: RbTree::Node(rx, gparent, rcol, rl, rr), left: rl_at, right: rr_at });
                                                                            have rn.model == rb_reparent(nleft, gparent) by {
                                                                                rewrite(rb_reparent(nleft, gparent), RbTree::Node(rx, gparent, rcol, rl, rr));
                                                                                close();
                                                                            }
                                                                        },
                                                                    }
                                                                    unfold(inner_tag);
                                                                    have (gparent->__rb_parent_color & 1) == 1 by {
                                                                        rewrite((gparent->__rb_parent_color & 1), color_bit(ucolor));
                                                                        rewrite(ucolor, Color::Black);
                                                                        unfold(color_bit(Color::Black));
                                                                        close();
                                                                    }
                                                                    have ctx_node_is(uu.model, ugp) == 1 by close();
                                                                    have ctx_identity(uu.model) == ugp by { apply(ctx_node_is_identity(uu.model, ugp)); }
                                                                    have gparent->__rb_parent_color == address(ugp) + 1 by close();
                                                                    apply(insert_black_context_word(uu.model, ugp));
                                                                    have ctx_parent_word(uu.model, gparent->__rb_parent_color) == 1 by { rewrite(gparent->__rb_parent_color, address(ugp) + 1); close(); }
                                                                    let final_uncle = fold(insert_left_link(gparent), { link: InsertLink::To(at(triangle_uncle_pointer, tmp)) });
                                                                    let final_other = fold(insert_right_link(node), { link: InsertLink::To(at(triangle_old_parent, parent)) });
                                                                    let final_child = fold(insert_right_link(gparent), { link: InsertLink::To(tmp) });
                                                                    let final_parent = fold(insert_left_link(parent), { link: InsertLink::To(gparent) });
                                                                    let { after: c } = step(__rb_rotate_set_parents, { c: uu });
                                                                    unfold(final_uncle);
                                                                    unfold(final_other);
                                                                    unfold(final_child);
                                                                    unfold(final_parent);
                                                                    have c.model == uup by close();
                                                                    have rb_parent_is(rb_reparent(nleft, gparent), gparent) == 1 by {
                                                                        apply(rb_reparent_parent_is(nleft, gparent));
                                                                        close();
                                                                    }
                                                                    have parent == nid by close();
                                                                    have aligned(nid, 8) by close();
                                                                    have gparent->__rb_parent_color == address(nid) by { rewrite(nid, parent); close(); }
                                                                    have (gparent->__rb_parent_color & 1) == 0 by {
                                                                        rewrite(gparent->__rb_parent_color, address(nid));
                                                                        close() using { aligned(nid, 8); };
                                                                    }
                                                                    have gparent->__rb_parent_color == address(nid) + (gparent->__rb_parent_color & 1) by { rewrite((gparent->__rb_parent_color & 1), 0); close(); }
                                                                    have ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == nid by { rewrite(nid, parent); close(); }
                                                                    let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), left: un, right: rn });
                                                                    have rb_parent_is(RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), nid) == 1 by {
                                                                        unfold(rb_parent_is(RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib), nid));
                                                                        close();
                                                                    }
                                                                    have rb_parent_is(RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), nid) == 1 by {
                                                                        unfold(rb_parent_is(RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), nid));
                                                                        close();
                                                                    }
                                                                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                        unfold(color_bit(Color::Black));
                                                                        close();
                                                                    }
                                                                    let t = fold(rb_at(node), { model: RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)), left: gn, right: pn });
                                                                    have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                        rewrite(c.model, uup);
                                                                        rewrite(t.model, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                        rewrite(rb_inorder(plug(uup, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)))), rb_inorder(plug(Context::Left(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                                        close();
                                                                    }
                                                                    have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                                        rewrite(c.model, uup);
                                                                        rewrite(t.model, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                        close();
                                                                    }
                                                                    have rb_parent_consistent(plug(c.model, t.model), 0) == 1 by {
                                                                        rewrite(c.model, uup);
                                                                        rewrite(t.model, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(gparent, nid, Color::Red, usib, rb_reparent(nleft, gparent)), RbTree::Node(cid, nid, Color::Red, rb_reparent(nright, cid), csib)));
                                                                        close();
                                                                    }
                                                                    have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                                        unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                                    }
                                                                    step();
                                                                    step();
                                                                },
                                                            }
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                step();
                                                                    unfold(triangle_uncle_link);
                                                                    unfold(triangle_tag);
                                                                    unfold(triangle_focus_link);
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1), color_bit(uncolor));
                                                                            rewrite(uncolor, Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                            close();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                            close();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp, gparent);
                                                                            rewrite(uncolor, Color::Red);
                                                                            close();
                                                                        }
                                                                        have cup == Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup, Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib, RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor, Color::Black);
                                                                            rewrite(uid, gparent);
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, t.model, csib)) == 1 by {
                                                                            apply(ctx_insert_cursor_left_parent(cid, cgp, t.model, csib, cup));
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(gparent, cgp);
                                                                            close();
                                                                        }
                                                                        apply(ctx_insert_case1_right_step(ugp, gparent, cid, unid, unl, unr, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib, uup));
                                                                        have rb_inorder(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib)), plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0) == 1 by {
                                                                            apply(plug_left_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, t.model, csib)), plug(Context::Left(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))), 0), rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), 0));
                                                                            close();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib))));
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                            let flip_tmp_rb_left = fold(insert_left_link(tmp), { link: InsertLink::To(tmp->rb_left) });
                                                                            let flip_tmp_rb_right = fold(insert_right_link(tmp), { link: InsertLink::To(tmp->rb_right) });
                                                                            let flip_parent_rb_left = fold(insert_left_link(parent), { link: InsertLink::To(parent->rb_left) });
                                                                            let flip_parent_rb_right = fold(insert_right_link(parent), { link: InsertLink::To(parent->rb_right) });
                                                                            let flip_gparent_rb_left = fold(insert_left_link(gparent), { link: InsertLink::To(gparent->rb_left) });
                                                                            let flip_gparent_rb_right = fold(insert_right_link(gparent), { link: InsertLink::To(gparent->rb_right) });
                                                                            let flip_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                                        step();
                                                                        step();
                                                                            unfold(flip_tmp_rb_left);
                                                                            unfold(flip_tmp_rb_right);
                                                                            have aligned(gparent, 8) by { rewrite(gparent, uid); close(); }
                                                                            have (address(gparent) | 1) == address(gparent) + 1 by {
                                                                                close() using { aligned(gparent, 8); };
                                                                            }
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                            step();
                                                                            unfold(flip_parent_rb_left);
                                                                            unfold(flip_parent_rb_right);
                                                                            have parent->__rb_parent_color == (address(gparent) | 1) by close();
                                                                            have parent->__rb_parent_color == address(gparent) + 1 by close();
                                                                            have (parent->__rb_parent_color & 1) == 1 by close();
                                                                            have parent->__rb_parent_color == address(gparent) + (parent->__rb_parent_color & 1) by close();
                                                                            have ((parent->__rb_parent_color & ~3) as (struct rb_node *)) == gparent by close();
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), left: t, right: cs });
                                                                        step();
                                                                            unfold(flip_tag);
                                                                        step();
                                                                            step();
                                                                            have parent == ugp by close();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), ugp));
                                                                            close();
                                                                        }
                                                                            unfold(flip_gparent_rb_left);
                                                                            unfold(flip_gparent_rb_right);
                                                                            have aligned(ugp, 8) by close();
                                                                            have gparent->__rb_parent_color == address(ugp) by close();
                                                                            have (gparent->__rb_parent_color & 1) == 0 by {
                                                                                rewrite(gparent->__rb_parent_color, address(ugp));
                                                                                close() using { aligned(ugp, 8); };
                                                                            }
                                                                            have gparent->__rb_parent_color == address(ugp) + (gparent->__rb_parent_color & 1) by close();
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, RbTree::Node(nid, nparent, ncolor, nleft, nright), csib)), left: un, right: pn });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor, Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            close();
                                                                        }
                                                                        close();
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); close();
                                                                }
                                                                close();
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
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have parent == cid by {
                                            apply(ctx_node_is_right_identity(cid, cgp, ccolor,
                                                csib, cup, parent));
                                            close();
                                        }
                                        have ctx_rb(Context::Right(cid, cgp, ccolor, csib, cup),
                                            black_height(t.model), Color::Black) == 1 by {
                                            apply(ctx_almost_rb_insert_black_focus(c.model,
                                                black_height(t.model)));
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have rb_inorder(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model))
                                            == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have rb_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model), 0) == 1 by {
                                            unfold(rb_tree_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(rb_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model), 0), rb_tree_parent_consistent(plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model)));
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        have ctx_almost_rb_insert(Context::Right(cid, cgp, ccolor, csib, cup), black_height(t.model)) == 1 by {
                                            rewrite(Context::Right(cid, cgp, ccolor, csib, cup), c.model);
                                            close();
                                        }
                                        let { sibling: cs, up: cu } = unfold(c);
                                        step();
                                        step();
                                        match ccolor {
                                            Color::Black => {
                                                have (parent->__rb_parent_color & 1) == 1 by {
                                                    rewrite((parent->__rb_parent_color & 1), color_bit(ccolor));
                                                    rewrite(ccolor, Color::Black);
                                                    unfold(color_bit(Color::Black));
                                                    close();
                                                }
                                                have ctx_almost_rb_insert(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model)) == 1 by {
                                                    rewrite(Color::Black, ccolor);
                                                    close();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp, Color::Black, csib, cup), black_height(t.model), rb_color(t.model)) == 1 by {
                                                    apply(ctx_black_frame_right_restores(cid, cgp, csib, cup, black_height(t.model), rb_color(t.model)));
                                                    close();
                                                }
                                                have is_rb_root(plug(Context::Right(cid, cgp, Color::Black, csib, cup), t.model)) == 1 by {
                                                    apply(ctx_insert_black_parent_exit(Context::Right(cid, cgp, Color::Black, csib, cup), t.model));
                                                    close();
                                                }
                                                have (parent->__rb_parent_color & 1) != 0 by {
                                                    rewrite((parent->__rb_parent_color & 1), 1);
                                                    close();
                                                }
                                                step();
                                                let c = fold(ctx_at(node, root),
                                                    {
                                                    model: Context::Right(cid, cgp, ccolor,
                                                        csib, cup),
                                                    sibling: cs, up: cu
                                                });
                                                have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                    rewrite(c.model, Context::Right(cid, cgp, ccolor, csib, cup));
                                                    rewrite(ccolor, Color::Black);
                                                    close();
                                                }
                                                have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                }
                                                step();
                                            },
                                            Color::Red => {
                                                have color_bit(ccolor) == 0 by {
                                                    rewrite(ccolor, Color::Red);
                                                    unfold(color_bit(Color::Red));
                                                    close();
                                                }
                                                have ctx_rb(Context::Right(cid, cgp,
                                                    Color::Red, csib, cup),
                                                    black_height(t.model),
                                                    Color::Black) == 1 by {
                                                    rewrite(Color::Red, ccolor);
                                                    close();
                                                }
                                                have ctx_rb(cu.model,
                                                    black_height(t.model), Color::Red) == 1 by {
                                                    apply(ctx_rb_right_red_up(cid, cgp, csib, cup,
                                                        black_height(t.model),
                                                        Color::Black));
                                                    rewrite(cu.model, cup);
                                                    close();
                                                }
                                                step();
                                                step();
                                                let load_tag = fold(insert_red_tag(parent), { link: InsertParent::To(cgp) });
                                                let { left: call_left, right: call_right } = unfold(t);
                                                have separate(load_tag, memory(node->rb_right)) by close();
                                                have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_right)) by close();
                                                have separate(load_tag, memory(node->rb_left)) by close();
                                                have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_left)) by close();
                                                let t = fold(rb_at(node), { model: RbTree::Node(nid, nparent, ncolor, nleft, nright), left: call_left, right: call_right });
                                                mark before_gparent_call;

                                                let { after: load_tag } = step(rb_red_parent, { before: load_tag });
                                                unfold(load_tag);
                                                step(); // Assign the decoded grandparent.
                                                have cu.model != Context::Top by {
                                                    apply(ctx_rb_red_focus_not_top(cu.model,
                                                        black_height(t.model)));
                                                    close();
                                                }
                                                match cu.model {
                                                Context::Top => {
                                                    close();
                                                },
                                                Context::Left(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Left(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup), cu.model);
                                                        rewrite(cu.model, cup);
                                                        close();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_left_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp));
                                                        close();
                                                    }
                                                    have ctx_rb(Context::Left(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Left(uid, ugp, ucolor, usib, uup), cu.model);
                                                        close();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                        mark before_grandparent_links;
                                                        mark triangle_before_uncle_load;
                                                        have separate(memory(gparent->rb_right), memory(gparent->rb_left)) by { close(); }
                                                        have separate(memory(gparent->rb_right), memory(parent->rb_left)) by { close(); }
                                                        have separate(memory(gparent->rb_right), memory(gparent->__rb_parent_color)) by { close(); }
                                                        have separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)) by { close(); }
                                                        have at(before_grandparent_links, ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp) by { close(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(gparent->rb_right)) by { close(); }
                                                        have separate(memory(gparent->__rb_parent_color), memory(parent->rb_right)) by { close(); }
                                                        have gparent->rb_left == parent by { rewrite(gparent, uid); rewrite(parent, cid); close(); }
                                                        let read_focus_link = fold(insert_left_link(gparent), { link: InsertLink::To(parent) });
                                                        let read_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                        have gparent->rb_right == uid->rb_right by { rewrite(gparent, uid); close(); }
                                                        have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(gparent->rb_right)) by close();
                                                        have parent->rb_right == cid->rb_right by { rewrite(parent, cid); close(); }
                                                        have parent->rb_right == node by close();
                                                        have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(parent->rb_right)) by close();
                                                        step(); // Load the uncle into tmp.
                                                        have tmp == at(before_grandparent_links, uid->rb_right) by close();
                                                        have separate(statement(1).statement(3).footprint, memory(gparent->rb_right)) by {
                                                            close();
                                                        }
                                                        have gparent->rb_right == at(before_grandparent_links, gparent->rb_right) by {
                                                            preserve(memory(gparent->rb_right), statement(1).statement(3));
                                                        }
                                                        have separate(statement(1).statement(3).footprint, memory(parent->rb_right)) by {
                                                            close();
                                                        }
                                                        have parent->rb_right == at(before_grandparent_links, parent->rb_right) by {
                                                            preserve(memory(parent->rb_right), statement(1).statement(3));
                                                        }
                                                        unfold(read_focus_link);
                                                        mark before_uncle_pointer_changes;
                                                        have at(before_uncle_pointer_changes, gparent->rb_right == at(before_uncle_pointer_changes, tmp)) by { close(); }
                                                        have at(before_uncle_pointer_changes, parent->rb_right == node) by { close(); }
                                                        have separate(memory(parent->rb_right), memory(gparent->rb_left)) by { close(); }
                                                        have separate(memory(parent->rb_right), memory(parent->rb_left)) by { close(); }
                                                        have separate(memory(parent->rb_right), memory(gparent->__rb_parent_color)) by { close(); }
                                                        have separate(memory(parent->rb_right), memory(parent->__rb_parent_color)) by { close(); }
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                                owns read_tag: insert_parent_tag(gparent, ugp);
                                                                fact read_tag.color == ucolor;
                                                            fact un.model == usib;
                                                            fact gparent->rb_right == tmp;
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr));
                                                                    close();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor));
                                                                    close();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                    close();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp, gparent);
                                                                    rewrite(uncolor, Color::Black);
                                                                    close();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black, uncolor);
                                                                    close();
                                                                }
                                                                have gparent->rb_right == tmp by { close(); }
                                                                have tmp == at(before_uncle_pointer_changes, tmp) by { close(); }
                                                                have tmp->rb_left == at(before_uncle_pointer_changes, tmp)->rb_left by {
                                                                    rewrite(tmp, at(before_uncle_pointer_changes, tmp)); close();
                                                                }
                                                                have tmp->rb_right == at(before_uncle_pointer_changes, tmp)->rb_right by {
                                                                    rewrite(tmp, at(before_uncle_pointer_changes, tmp)); close();
                                                                }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    close();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                have gparent->rb_right == tmp by { close(); }
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    close();
                                                                }
                                                            },
                                                        }
                                                            unfold(read_tag);
                                                        mark triangle_uncle_pointer;
                                                        have at(triangle_uncle_pointer, gparent->rb_right == tmp) by { close(); }
                                                        have cup == Context::Left(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup, Context::Left(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor, Color::Black);
                                                            rewrite(uid, gparent);
                                                            close();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent));
                                                            close();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor), rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor));
                                                            close();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model, RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent, cid);
                                                            rewrite(ncolor, Color::Red);
                                                            close();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Left(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        apply(ctx_insert_case2_left_exit_step(ugp, gparent, cid, nid, csib, nleft, nright, usib, uup));
                                                            let { right: nr_at, left: nl_at } = unfold(t);
                                                            match InsertParent::To(node->rb_right) {
                                                                InsertParent::To(original_outer_child) => {
                                                                    have separate(memory(((&gparent) as (uint8 *))[0..8]), memory(node->rb_left)) by close();
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_left)) by close();
                                                                    have contains(at(before_gparent_call, load_tag), statement(1).statement(2).call(0).footprint) by close();
                                                                    apply(separation::contains_refl(memory(node->rb_left)));
                                                                    apply(separation::separate_restrict(at(before_gparent_call, load_tag), memory(node->rb_left), statement(1).statement(2).call(0).footprint, memory(node->rb_left)));
                                                                    have at(statement(1).statement(2).call(0).exit, node->rb_left) == at(before_gparent_call, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(2).call(0)); }
                                                                    have separate(statement(1).statement(2).assignment(gparent, 0).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_left) == at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(2).assignment(gparent, 0)); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_left) == at(statement(1).statement(2).call(0).exit, node->rb_left) by close();
                                                                    have separate(statement(1).statement(3).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(3).exit, node->rb_left) == at(statement(1).statement(3).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(3)); }
                                                                    have at(statement(1).statement(3).entry, node->rb_left) == at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_left) by close();

                                                                    have separate(memory(((&gparent) as (uint8 *))[0..8]), memory(node->rb_right)) by close();
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(node->rb_right)) by close();
                                                                    have contains(at(before_gparent_call, load_tag), statement(1).statement(2).call(0).footprint) by close();
                                                                    apply(separation::contains_refl(memory(node->rb_right)));
                                                                    apply(separation::separate_restrict(at(before_gparent_call, load_tag), memory(node->rb_right), statement(1).statement(2).call(0).footprint, memory(node->rb_right)));
                                                                    have at(statement(1).statement(2).call(0).exit, node->rb_right) == at(before_gparent_call, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(2).call(0)); }
                                                                    have separate(statement(1).statement(2).assignment(gparent, 0).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_right) == at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(2).assignment(gparent, 0)); }
                                                                    have at(statement(1).statement(2).assignment(gparent, 0).entry, node->rb_right) == at(statement(1).statement(2).call(0).exit, node->rb_right) by close();
                                                                    have separate(statement(1).statement(3).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(3).exit, node->rb_right) == at(statement(1).statement(3).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(3)); }
                                                                    have at(statement(1).statement(3).entry, node->rb_right) == at(statement(1).statement(2).assignment(gparent, 0).exit, node->rb_right) by close();

                                                                    have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                                        rewrite(Color::Red, ncolor);
                                                                        close();
                                                                    }
                                                                    have at(triangle_before_uncle_load, node->rb_right) == at(statement(1).statement(3).exit, node->rb_right) by close();
                                                                    have node->rb_right == at(before_gparent_call, node->rb_right) by close();
                                                                    let inner_uncle = fold(insert_right_link(gparent), { link: InsertLink::To(at(triangle_uncle_pointer, tmp)) });
                                                                    let inner_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                                    step();
                                                                    step();
                                                                    step();
                                                                    have separate(statement(1).statement(4).statement(1).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(1).exit, node->rb_right) == at(statement(1).statement(4).statement(1).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(4).statement(1)); }
                                                                    have at(statement(1).statement(4).statement(1).entry, node->rb_right) == at(triangle_uncle_pointer, node->rb_right) by close();
                                                                    have separate(statement(1).statement(4).statement(1).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(1).exit, node->rb_left) == at(statement(1).statement(4).statement(1).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(4).statement(1)); }
                                                                    have separate(memory(parent->rb_right), memory(node->rb_left)) by { close(); }
                                                                    mark before_inner_parent_right;
                                                                    have at(before_inner_parent_right, parent->rb_left == parent->rb_left) by { close(); }
                                                                    have separate(memory(parent->rb_left), memory(parent->rb_right)) by { close(); }
                                                                    have separate(memory(parent->rb_left), memory(node->rb_left)) by { close(); }
                                                                    mark before_inner_node_left;
                                                                    have at(before_inner_node_left, node->rb_right == node->rb_right) by { close(); }
                                                                    have separate(memory(node->rb_right), memory(parent->rb_right)) by { close(); }
                                                                    have separate(memory(node->rb_right), memory(node->rb_left)) by { close(); }
                                                                    let inner_parent_other = fold(insert_left_link(parent), { link: InsertLink::To(parent->rb_left) });
                                                                    let inner_node_other = fold(insert_right_link(node), { link: InsertLink::To(original_outer_child) });
                                                                    match nl_at.model ensuring {
                                                                        owns bn: rb_at(tmp);
                                                                        owns inner_node_other: insert_right_link(node);
                                                                        fact inner_node_other.link == InsertLink::To(original_outer_child);
                                                                        owns inner_tag: insert_parent_tag(gparent, ugp);
                                                                        fact inner_tag.color == ucolor;
                                                                        fact bn.model == rb_reparent(nleft, cid);
                                                                        fact node->rb_left == parent;
                                                                        fact gparent->rb_right == at(triangle_uncle_pointer, tmp);

                                                                        fact parent->rb_right == tmp;
                                                                        fact parent->rb_left == at(before_inner_parent_right, parent->rb_left);
                                                                    } {
                                                                        RbTree::Empty => {
                                                                            unfold(nl_at);
                                                                            step();
                                                                            step();
                                                                            let empty_parent_focus = fold(insert_right_link(parent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let empty_node_focus = fold(insert_left_link(node), { link: InsertLink::To(parent) });
                                                                            step();
                                                                            step();
                                                                            have rb_reparent(nleft, cid) == RbTree::Empty by {
                                                                                rewrite(nleft, RbTree::Empty);
                                                                                unfold(rb_reparent(RbTree::Empty, cid)); close();
                                                                            }
                                                                            unfold(inner_parent_other);
                                                                            have parent->rb_left == at(before_inner_parent_right, parent->rb_left) by close();
                                                                            unfold(empty_parent_focus);
                                                                            have parent->rb_right == tmp by { close(); }
                                                                            unfold(inner_uncle);
                                                                            have gparent->rb_right == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(empty_node_focus);
                                                                            have node->rb_left == parent by { close(); }
                                                                            let bn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                            have bn.model == rb_reparent(nleft, cid) by {
                                                                                rewrite(rb_reparent(nleft, cid), RbTree::Empty);
                                                                                close();
                                                                            }
                                                                        },
                                                                        RbTree::Node(bx, bp, bcol, br, bl) => {
                                                                            let { right: bl_at, left: br_at } = unfold(nl_at);
                                                                            have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(bx->rb_left)) by close();
                                                                            have separate(statement(1).statement(4).statement(1).footprint, memory(bx->rb_left)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(1).exit, bx->rb_left) == at(statement(1).statement(4).statement(1).entry, bx->rb_left) by { preserve(memory(bx->rb_left), statement(1).statement(4).statement(1)); }
                                                                            have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(bx->rb_right)) by close();
                                                                            have separate(statement(1).statement(4).statement(1).footprint, memory(bx->rb_right)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(1).exit, bx->rb_right) == at(statement(1).statement(4).statement(1).entry, bx->rb_right) by { preserve(memory(bx->rb_right), statement(1).statement(4).statement(1)); }
                                                                            step();
                                                                            have separate(statement(1).statement(4).statement(2).statement(0).footprint, memory(bx->rb_left)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(2).statement(0).exit, bx->rb_left) == at(statement(1).statement(4).statement(2).statement(0).entry, bx->rb_left) by { preserve(memory(bx->rb_left), statement(1).statement(4).statement(2).statement(0)); }
                                                                            have separate(statement(1).statement(4).statement(2).statement(0).footprint, memory(bx->rb_right)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(2).statement(0).exit, bx->rb_right) == at(statement(1).statement(4).statement(2).statement(0).entry, bx->rb_right) by { preserve(memory(bx->rb_right), statement(1).statement(4).statement(2).statement(0)); }
                                                                            mark before_inner_child_links;
                                                                            have separate(memory(node->rb_left), memory(tmp->__rb_parent_color)) by { close(); }

                                                                            have separate(memory(parent->rb_right), memory(tmp->__rb_parent_color)) by { close(); }
                                                                            have at(before_inner_child_links, tmp->rb_right == bx->rb_right) by { close(); }
                                                                            have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(parent->rb_right))) by { close(); }
                                                                            have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(node->rb_left))) by { close(); }
                                                                            have at(before_inner_child_links, separate(memory(tmp->rb_right), memory(tmp->__rb_parent_color))) by { close(); }
                                                                            have at(before_inner_child_links, tmp->rb_left == bx->rb_left) by { close(); }
                                                                            have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(parent->rb_right))) by { close(); }
                                                                            have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(node->rb_left))) by { close(); }
                                                                            have at(before_inner_child_links, separate(memory(tmp->rb_left), memory(tmp->__rb_parent_color))) by { close(); }
                                                                            have rb_root_black(RbTree::Node(bx, bp, bcol, br, bl)) == 1 by {
                                                                                rewrite(RbTree::Node(bx, bp, bcol, br, bl), nleft);
                                                                                close();
                                                                            }
                                                                            have color_bit(bcol) == 1 by {
                                                                                apply(rb_root_black_node_color_bit(bx, bp, bcol, br, bl));
                                                                                close();
                                                                            }
                                                                            have rb_reparent(nleft, cid) == RbTree::Node(bx, cid, bcol, br, bl) by {
                                                                                rewrite(nleft, RbTree::Node(bx, bp, bcol, br, bl));
                                                                                unfold(rb_reparent(RbTree::Node(bx, bp, bcol, br, bl), cid)); close();
                                                                            }
                                                                            let middle_left = fold(insert_left_link(tmp), { link: InsertLink::To(bx->rb_left) });
                                                                            let middle_right = fold(insert_right_link(tmp), { link: InsertLink::To(bx->rb_right) });
                                                                            step();
                                                                            let inner_new_parent_focus = fold(insert_right_link(parent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let inner_new_node_focus = fold(insert_left_link(node), { link: InsertLink::To(parent) });
                                                                            step();
                                                                            step();
                                                                            unfold(middle_right);
                                                                            have tmp->rb_right == at(before_inner_child_links, bx->rb_right) by close();
                                                                            unfold(middle_left);
                                                                            have tmp->rb_left == at(before_inner_child_links, bx->rb_left) by close();
                                                                            unfold(inner_parent_other);
                                                                            have parent->rb_left == at(before_inner_parent_right, parent->rb_left) by close();
                                                                            unfold(inner_new_parent_focus);
                                                                            have parent->rb_right == tmp by { close(); }
                                                                            unfold(inner_uncle);
                                                                            have gparent->rb_right == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(inner_new_node_focus);
                                                                            have node->rb_left == parent by { close(); }
                                                                            have aligned(parent, 8) by { rewrite(parent, cid); close(); }
                                                                            have tmp->__rb_parent_color == (address(parent) | 1) by close();
                                                                            have (address(parent) | 1) == address(parent) + 1 by { close(); }
                                                                            have tmp->__rb_parent_color == address(parent) + 1 by close();
                                                                            have (tmp->__rb_parent_color & 1) == color_bit(bcol) by { rewrite(color_bit(bcol), 1); close(); }
                                                                            have tmp->__rb_parent_color == address(cid) + (tmp->__rb_parent_color & 1) by { rewrite(cid, parent); close(); }
                                                                            have ((tmp->__rb_parent_color & ~3) as (struct rb_node *)) == cid by { rewrite(cid, parent); close(); }
                                                                            have rb_parent_is(br, tmp) == 1 by close();
                                                                            have rb_parent_is(bl, tmp) == 1 by close();
                                                                            let bn = fold(rb_at(tmp), { model: RbTree::Node(bx, cid, bcol, br, bl), right: bl_at, left: br_at });
                                                                            have bn.model == rb_reparent(nleft, cid) by {
                                                                                rewrite(rb_reparent(nleft, cid), RbTree::Node(bx, cid, bcol, br, bl));
                                                                                close();
                                                                            }
                                                                        },
                                                                    }
                                                                    mark before_inner_parent_color;
                                                                    have at(before_inner_parent_color, node->rb_left == parent) by { close(); }
                                                                    have separate(memory(node->rb_left), memory(parent->__rb_parent_color)) by { close(); }
                                                                    have at(before_inner_parent_color, gparent->rb_right == at(triangle_uncle_pointer, tmp)) by { close(); }
                                                                    have separate(memory(gparent->rb_right), memory(parent->__rb_parent_color)) by { close(); }

                                                                    have at(before_inner_parent_color, parent->rb_right == tmp) by { close(); }

                                                                    have at(before_inner_parent_color, parent->rb_left == at(before_inner_parent_right, parent->rb_left)) by { close(); }
                                                                    have separate(memory(parent->rb_left), memory(parent->__rb_parent_color)) by { close(); }
                                                                    have separate(memory(parent->rb_right), memory(parent->__rb_parent_color)) by { close(); }
                                                                    step();

                                                                    have contains(memory(parent->__rb_parent_color), statement(1).statement(4).statement(2).statement(4).footprint) by { close(); }
                                                                    apply(separation::contains_refl(memory(parent->rb_right)));
                                                                    apply(separation::separate_restrict(memory(parent->rb_right), memory(parent->__rb_parent_color), memory(parent->rb_right), statement(1).statement(4).statement(2).statement(4).footprint));
                                                                    have parent->rb_right == at(before_inner_parent_color, parent->rb_right) by {
                                                                        preserve(memory(parent->rb_right), statement(1).statement(4).statement(2).statement(4));
                                                                    }
                                                                    have parent->rb_right == tmp by {
                                                                        rewrite(parent->rb_right, at(before_inner_parent_color, parent->rb_right));
                                                                        close();
                                                                    }
                                                                    apply(separation::contains_refl(memory(parent->rb_left)));
                                                                    apply(separation::separate_restrict(memory(parent->rb_left), memory(parent->__rb_parent_color), memory(parent->rb_left), statement(1).statement(4).statement(2).statement(4).footprint));
                                                                    have parent->rb_left == at(before_inner_parent_color, parent->rb_left) by {
                                                                        preserve(memory(parent->rb_left), statement(1).statement(4).statement(2).statement(4));
                                                                    }
                                                                    have parent->rb_left == at(before_inner_parent_right, parent->rb_left) by {
                                                                        rewrite(parent->rb_left, at(before_inner_parent_color, parent->rb_left));
                                                                        close();
                                                                    }
                                                                    apply(separation::contains_refl(memory(gparent->rb_right)));
                                                                    apply(separation::separate_restrict(memory(gparent->rb_right), memory(parent->__rb_parent_color), memory(gparent->rb_right), statement(1).statement(4).statement(2).statement(4).footprint));
                                                                    have gparent->rb_right == at(before_inner_parent_color, gparent->rb_right) by {
                                                                        preserve(memory(gparent->rb_right), statement(1).statement(4).statement(2).statement(4));
                                                                    }
                                                                    have gparent->rb_right == at(triangle_uncle_pointer, tmp) by {
                                                                        rewrite(gparent->rb_right, at(before_inner_parent_color, gparent->rb_right));
                                                                        close();
                                                                    }
                                                                    apply(separation::contains_refl(memory(node->rb_left)));
                                                                    apply(separation::separate_restrict(memory(node->rb_left), memory(parent->__rb_parent_color), memory(node->rb_left), statement(1).statement(4).statement(2).statement(4).footprint));
                                                                    have node->rb_left == at(before_inner_parent_color, node->rb_left) by {
                                                                        preserve(memory(node->rb_left), statement(1).statement(4).statement(2).statement(4));
                                                                    }
                                                                    have node->rb_left == parent by {
                                                                        rewrite(node->rb_left, at(before_inner_parent_color, node->rb_left));
                                                                        close();
                                                                    }
                                                                    have rb_parent_is(rb_reparent(nleft, cid), cid) == 1 by {
                                                                        apply(rb_reparent_parent_is(nleft, cid));
                                                                        close();
                                                                    }
                                                                    have node == nid by close();
                                                                    have aligned(node, 8) by close();
                                                                    have parent->__rb_parent_color == address(node) by close();
                                                                    have (parent->__rb_parent_color & 1) == 0 by close();
                                                                    have parent->__rb_parent_color == address(nid) + (parent->__rb_parent_color & 1) by { rewrite(nid, node); close(); }
                                                                    have ((parent->__rb_parent_color & ~3) as (struct rb_node *)) == nid by { rewrite(nid, node); close(); }
                                                                    unfold(color_bit(Color::Red));
                                                                    let pn = fold(rb_at(parent), { model: RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), right: bn, left: cs });
                                                                    mark triangle_old_parent;
                                                                    have at(triangle_old_parent, node->rb_left == parent) by { close(); }
                                                                    step();
                                                                    mark before_triangle_parent_assignment;

                                                                    step();

                                                                    unfold(inner_node_other);
                                                                    have node->rb_right == original_outer_child by close();
                                                                    mark before_outer_grandparent_tag;

                                                                    have at(before_outer_grandparent_tag, gparent->rb_right == at(triangle_uncle_pointer, tmp)) by { close(); }
                                                                    have separate(memory(gparent->rb_right), memory(gparent->rb_left)) by { close(); }
                                                                    have separate(memory(gparent->rb_right), memory(parent->rb_right)) by { close(); }
                                                                    have at(before_outer_grandparent_tag, node->rb_left == at(triangle_old_parent, parent)) by { close(); }
                                                                    have separate(memory(node->rb_left), memory(gparent->rb_left)) by { close(); }
                                                                    have separate(memory(node->rb_left), memory(parent->rb_right)) by { close(); }
                                                                    let triangle_outer_uncle = fold(insert_right_link(gparent), { link: InsertLink::To(at(triangle_uncle_pointer, tmp)) });
                                                                    let triangle_outer_other = fold(insert_left_link(node), { link: InsertLink::To(at(triangle_old_parent, parent)) });
                                                                    match nr_at.model ensuring {
                                                                        owns rn: rb_at(tmp);
                                                                        owns inner_tag: insert_parent_tag(gparent, ugp);
                                                                        fact inner_tag.color == ucolor;
                                                                        fact rn.model == rb_reparent(nright, gparent);
                                                                        fact gparent->rb_left == tmp;
                                                                        fact parent->rb_right == gparent;
                                                                        fact node->rb_left == at(triangle_old_parent, parent);
                                                                        fact gparent->rb_right == at(triangle_uncle_pointer, tmp);

                                                                    } {
                                                                        RbTree::Empty => {
                                                                            unfold(nr_at);
                                                                            step();
                                                                            step();
                                                                            let triangle_new_gparent = fold(insert_left_link(gparent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let triangle_new_parent = fold(insert_right_link(parent), { link: InsertLink::To(gparent) });
                                                                            step();
                                                                            step();
                                                                            have rb_reparent(nright, gparent) == RbTree::Empty by {
                                                                                rewrite(nright, RbTree::Empty);
                                                                                unfold(rb_reparent(RbTree::Empty, gparent)); close();
                                                                            }
                                                                            unfold(triangle_outer_uncle);
                                                                            have gparent->rb_right == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(triangle_outer_other);
                                                                            have node->rb_left == at(triangle_old_parent, parent) by close();
                                                                            unfold(triangle_new_gparent);
                                                                            have gparent->rb_left == tmp by close();
                                                                            unfold(triangle_new_parent);
                                                                            have parent->rb_right == gparent by close();
                                                                            let rn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                            have rn.model == rb_reparent(nright, gparent) by {
                                                                                rewrite(rb_reparent(nright, gparent), RbTree::Empty);
                                                                                close();
                                                                            }
                                                                        },
                                                                        RbTree::Node(rx, rp, rcol, rr, rl) => {
                                                                            let { right: rl_at, left: rr_at } = unfold(nr_at);
                                                                            have separate(memory(((&parent) as (uint8 *))[0..8]), memory(original_outer_child->rb_right)) by close();
                                                                            have separate(statement(1).statement(4).statement(2).statement(6).footprint, memory(original_outer_child->rb_right)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(2).statement(6).exit, original_outer_child->rb_right) == at(statement(1).statement(4).statement(2).statement(6).entry, original_outer_child->rb_right) by { preserve(memory(original_outer_child->rb_right), statement(1).statement(4).statement(2).statement(6)); }
                                                                            have separate(memory(((&parent) as (uint8 *))[0..8]), memory(original_outer_child->rb_left)) by close();
                                                                            have separate(statement(1).statement(4).statement(2).statement(6).footprint, memory(original_outer_child->rb_left)) by { close(); }
                                                                            have at(statement(1).statement(4).statement(2).statement(6).exit, original_outer_child->rb_left) == at(statement(1).statement(4).statement(2).statement(6).entry, original_outer_child->rb_left) by { preserve(memory(original_outer_child->rb_left), statement(1).statement(4).statement(2).statement(6)); }
                                                                            have rx == original_outer_child by close();

                                                                            let outer_child_left = fold(insert_right_link(original_outer_child), { link: InsertLink::To(original_outer_child->rb_right) });
                                                                            let outer_child_right = fold(insert_left_link(original_outer_child), { link: InsertLink::To(original_outer_child->rb_left) });
                                                                            step();

                                                                            have rb_root_black(RbTree::Node(rx, rp, rcol, rr, rl)) == 1 by {
                                                                                rewrite(RbTree::Node(rx, rp, rcol, rr, rl), nright);
                                                                                close();
                                                                            }
                                                                            have color_bit(rcol) == 1 by {
                                                                                apply(rb_root_black_node_color_bit(rx, rp, rcol, rr, rl));
                                                                                close();
                                                                            }
                                                                            have rb_reparent(nright, gparent) == RbTree::Node(rx, gparent, rcol, rr, rl) by {
                                                                                rewrite(nright, RbTree::Node(rx, rp, rcol, rr, rl));
                                                                                unfold(rb_reparent(RbTree::Node(rx, rp, rcol, rr, rl), gparent)); close();
                                                                            }
                                                                            step();
                                                                            let triangle_new_gparent = fold(insert_left_link(gparent), { link: InsertLink::To(tmp) });
                                                                            step();
                                                                            let triangle_new_parent = fold(insert_right_link(parent), { link: InsertLink::To(gparent) });
                                                                            step();
                                                                            mark before_outer_child_color;
                                                                            have separate(memory(original_outer_child->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp, original_outer_child); close(); }
                                                                            have separate(memory(original_outer_child->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp, original_outer_child); close(); }
                                                                            step();
                                                                            have separate(statement(1).statement(4).statement(5).statement(0).footprint, memory(original_outer_child->rb_right)) by { close(); }
                                                                            have original_outer_child->rb_right == at(before_outer_child_color, original_outer_child->rb_right) by { preserve(memory(original_outer_child->rb_right), statement(1).statement(4).statement(5).statement(0)); }
                                                                            have separate(statement(1).statement(4).statement(5).statement(0).footprint, memory(original_outer_child->rb_left)) by { close(); }
                                                                            have original_outer_child->rb_left == at(before_outer_child_color, original_outer_child->rb_left) by { preserve(memory(original_outer_child->rb_left), statement(1).statement(4).statement(5).statement(0)); }
                                                                            unfold(outer_child_left);
                                                                            unfold(outer_child_right);
                                                                            have tmp->rb_right == original_outer_child->rb_right by { rewrite(tmp, original_outer_child); close(); }
                                                                            have tmp->rb_left == original_outer_child->rb_left by { rewrite(tmp, original_outer_child); close(); }
                                                                            unfold(triangle_outer_uncle);
                                                                            have gparent->rb_right == at(triangle_uncle_pointer, tmp) by close();
                                                                            unfold(triangle_outer_other);
                                                                            have node->rb_left == at(triangle_old_parent, parent) by close();
                                                                            unfold(triangle_new_gparent);
                                                                            have gparent->rb_left == tmp by close();
                                                                            unfold(triangle_new_parent);
                                                                            have parent->rb_right == gparent by close();
                                                                            let rn = fold(rb_at(original_outer_child), { model: RbTree::Node(rx, gparent, rcol, rr, rl), right: rl_at, left: rr_at });
                                                                            have rn.model == rb_reparent(nright, gparent) by {
                                                                                rewrite(rb_reparent(nright, gparent), RbTree::Node(rx, gparent, rcol, rr, rl));
                                                                                close();
                                                                            }
                                                                        },
                                                                    }
                                                                    unfold(inner_tag);
                                                                    have (gparent->__rb_parent_color & 1) == 1 by {
                                                                        rewrite((gparent->__rb_parent_color & 1), color_bit(ucolor));
                                                                        rewrite(ucolor, Color::Black);
                                                                        unfold(color_bit(Color::Black));
                                                                        close();
                                                                    }
                                                                    have ctx_node_is(uu.model, ugp) == 1 by close();
                                                                    have ctx_identity(uu.model) == ugp by { apply(ctx_node_is_identity(uu.model, ugp)); }
                                                                    have gparent->__rb_parent_color == address(ugp) + 1 by close();
                                                                    apply(insert_black_context_word(uu.model, ugp));
                                                                    have ctx_parent_word(uu.model, gparent->__rb_parent_color) == 1 by { rewrite(gparent->__rb_parent_color, address(ugp) + 1); close(); }
                                                                    let final_uncle = fold(insert_right_link(gparent), { link: InsertLink::To(at(triangle_uncle_pointer, tmp)) });
                                                                    let final_other = fold(insert_left_link(node), { link: InsertLink::To(at(triangle_old_parent, parent)) });
                                                                    let final_child = fold(insert_left_link(gparent), { link: InsertLink::To(tmp) });
                                                                    let final_parent = fold(insert_right_link(parent), { link: InsertLink::To(gparent) });
                                                                    let { after: c } = step(__rb_rotate_set_parents, { c: uu });
                                                                    unfold(final_uncle);
                                                                    unfold(final_other);
                                                                    unfold(final_child);
                                                                    unfold(final_parent);
                                                                    have c.model == uup by close();
                                                                    have rb_parent_is(rb_reparent(nright, gparent), gparent) == 1 by {
                                                                        apply(rb_reparent_parent_is(nright, gparent));
                                                                        close();
                                                                    }
                                                                    have parent == nid by close();
                                                                    have aligned(nid, 8) by close();
                                                                    have gparent->__rb_parent_color == address(nid) by { rewrite(nid, parent); close(); }
                                                                    have (gparent->__rb_parent_color & 1) == 0 by {
                                                                        rewrite(gparent->__rb_parent_color, address(nid));
                                                                        close() using { aligned(nid, 8); };
                                                                    }
                                                                    have gparent->__rb_parent_color == address(nid) + (gparent->__rb_parent_color & 1) by { rewrite((gparent->__rb_parent_color & 1), 0); close(); }
                                                                    have ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == nid by { rewrite(nid, parent); close(); }
                                                                    let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), right: un, left: rn });
                                                                    have rb_parent_is(RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), nid) == 1 by {
                                                                        unfold(rb_parent_is(RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), nid));
                                                                        close();
                                                                    }
                                                                    have rb_parent_is(RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), nid) == 1 by {
                                                                        unfold(rb_parent_is(RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib), nid));
                                                                        close();
                                                                    }
                                                                    have (node->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                        unfold(color_bit(Color::Black));
                                                                        close();
                                                                    }
                                                                    let t = fold(rb_at(node), { model: RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)), right: gn, left: pn });
                                                                    have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                        rewrite(c.model, uup);
                                                                        rewrite(t.model, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                        rewrite(rb_inorder(plug(uup, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)))), rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Left(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                                        close();
                                                                    }
                                                                    have is_rb_root(plug(c.model, t.model)) == 1 by {
                                                                        rewrite(c.model, uup);
                                                                        rewrite(t.model, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                        close();
                                                                    }
                                                                    have rb_parent_consistent(plug(c.model, t.model), 0) == 1 by {
                                                                        rewrite(c.model, uup);
                                                                        rewrite(t.model, RbTree::Node(nid, ugp, Color::Black, RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid)), RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), usib)));
                                                                        close();
                                                                    }
                                                                    have rb_tree_parent_consistent(plug(c.model, t.model)) == 1 by {
                                                                        unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                                                                    }
                                                                    step();
                                                                    step();
                                                                },
                                                            }
                                                    } else {
                                                        match us.model {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                step();
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1), color_bit(uncolor));
                                                                            rewrite(uncolor, Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_left_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                            close();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                            close();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp, gparent);
                                                                            rewrite(uncolor, Color::Red);
                                                                            close();
                                                                        }
                                                                        have cup == Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup, Context::Left(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib, RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor, Color::Black);
                                                                            rewrite(uid, gparent);
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, csib, t.model)) == 1 by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup));
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(gparent, cgp);
                                                                            close();
                                                                        }
                                                                        have black_height(csib) == black_height(t.model) by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup));
                                                                            close();
                                                                        }
                                                                        apply(ctx_insert_case1_left_step(ugp, gparent, cid, unid, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright), unl, unr, uup));
                                                                        have rb_inorder(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model)), plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0) == 1 by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model)), plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))), 0), rb_parent_consistent(plug(Context::Left(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0));
                                                                            close();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr))));
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                            unfold(read_tag);
                                                                            let flip_tmp_rb_left = fold(insert_left_link(tmp), { link: InsertLink::To(tmp->rb_left) });
                                                                            let flip_tmp_rb_right = fold(insert_right_link(tmp), { link: InsertLink::To(tmp->rb_right) });
                                                                            let flip_parent_rb_left = fold(insert_left_link(parent), { link: InsertLink::To(parent->rb_left) });
                                                                            let flip_parent_rb_right = fold(insert_right_link(parent), { link: InsertLink::To(parent->rb_right) });
                                                                            let flip_gparent_rb_left = fold(insert_left_link(gparent), { link: InsertLink::To(gparent->rb_left) });
                                                                            let flip_gparent_rb_right = fold(insert_right_link(gparent), { link: InsertLink::To(gparent->rb_right) });
                                                                            let flip_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                                        step();
                                                                        step();
                                                                            unfold(flip_tmp_rb_left);
                                                                            unfold(flip_tmp_rb_right);
                                                                            have aligned(gparent, 8) by { rewrite(gparent, uid); close(); }
                                                                            have (address(gparent) | 1) == address(gparent) + 1 by {
                                                                                close() using { aligned(gparent, 8); };
                                                                            }
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                            step();
                                                                            unfold(flip_parent_rb_left);
                                                                            unfold(flip_parent_rb_right);
                                                                            have parent->__rb_parent_color == (address(gparent) | 1) by close();
                                                                            have parent->__rb_parent_color == address(gparent) + 1 by close();
                                                                            have (parent->__rb_parent_color & 1) == 1 by close();
                                                                            have parent->__rb_parent_color == address(gparent) + (parent->__rb_parent_color & 1) by close();
                                                                            have ((parent->__rb_parent_color & ~3) as (struct rb_node *)) == gparent by close();
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), left: cs, right: t });
                                                                        step();
                                                                            unfold(flip_tag);
                                                                        step();
                                                                            step();
                                                                            have parent == ugp by close();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), ugp));
                                                                            close();
                                                                        }
                                                                            unfold(flip_gparent_rb_left);
                                                                            unfold(flip_gparent_rb_right);
                                                                            have aligned(ugp, 8) by close();
                                                                            have gparent->__rb_parent_color == address(ugp) by close();
                                                                            have (gparent->__rb_parent_color & 1) == 0 by {
                                                                                rewrite(gparent->__rb_parent_color, address(ugp));
                                                                                close() using { aligned(ugp, 8); };
                                                                            }
                                                                            have gparent->__rb_parent_color == address(ugp) + (gparent->__rb_parent_color & 1) by close();
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), RbTree::Node(unid, gparent, Color::Black, unl, unr)), left: pn, right: un });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor, Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            close();
                                                                        }
                                                                        close();
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); close();
                                                                }
                                                                close();
                                                            },
                                                        }
                                                    }
                                                },
                                                Context::Right(uid, ugp, ucolor, usib, uup) => {
                                                    have ctx_node_is(Context::Right(uid, ugp, ucolor,
                                                        usib, uup), cgp) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup), cu.model);
                                                        rewrite(cu.model, cup);
                                                        close();
                                                    }
                                                    have cgp == uid by {
                                                        apply(ctx_node_is_right_identity(uid, ugp, ucolor,
                                                            usib, uup, cgp));
                                                        close();
                                                    }
                                                    have ctx_rb(Context::Right(uid, ugp, ucolor, usib, uup), black_height(t.model), Color::Red) == 1 by {
                                                        rewrite(Context::Right(uid, ugp, ucolor, usib, uup), cu.model);
                                                        close();
                                                    }
                                                    let { sibling: us, up: uu } = unfold(cu);
                                                        mark triangle_before_uncle_load;
                                                        have gparent->rb_left == uid->rb_left by { rewrite(gparent, uid); close(); }
                                                        have gparent->rb_right == parent by { rewrite(gparent, uid); rewrite(parent, cid); close(); }
                                                        let triangle_uncle_link = fold(insert_left_link(gparent), { link: InsertLink::To(uid->rb_left) });
                                                        let triangle_parent_link = fold(insert_right_link(gparent), { link: InsertLink::To(parent) });
                                                        let triangle_focus_link = fold(insert_right_link(parent), { link: InsertLink::To(node) }) by { rewrite(parent, cid); close(); }
                                                        let triangle_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                    step();
                                                        unfold(triangle_parent_link);
                                                        have tmp == parent by close();
                                                    if rb_root_black(usib) == 1 {
                                                        match us.model ensuring {
                                                            owns un: rb_at(tmp);
                                                            fact un.model == usib;
                                                                fact gparent->rb_left == tmp;
                                                                fact node->rb_right == at(triangle_before_uncle_load, node->rb_right);
                                                                fact node->rb_left == at(triangle_before_uncle_load, node->rb_left);
                                                        } {
                                                            RbTree::Node(unid, unp, uncolor, unl, unr) => {
                                                                let { left: ul, right: ur } = unfold(us);
                                                                    have unid == uid->rb_left by close();
                                                                    have unid->rb_left == uid->rb_left->rb_left by { rewrite(unid, uid->rb_left); close(); }
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(unid->rb_left)) by close();
                                                                    let triangle_saved_rb_left = fold(insert_left_link(unid), { link: InsertLink::To(unid->rb_left) });
                                                                    have unid->rb_right == uid->rb_left->rb_right by { rewrite(unid, uid->rb_left); close(); }
                                                                    have separate(memory(((&tmp) as (uint8 *))[0..8]), memory(unid->rb_right)) by close();
                                                                    let triangle_saved_rb_right = fold(insert_right_link(unid), { link: InsertLink::To(unid->rb_right) });

                                                                    let triangle_uncle_tag = fold(insert_parent_tag(uid->rb_left, unp), { color: uncolor });
                                                                    step();
                                                                    mark triangle_before_middle_load;
                                                                    step();
                                                                    unfold(triangle_uncle_tag);
                                                                have rb_root_black(RbTree::Node(unid, unp, uncolor, unl, unr)) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have color_bit(uncolor) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(unid, unp, uncolor, unl, unr));
                                                                    close();
                                                                }
                                                                have uncolor == Color::Black by {
                                                                    apply(color_bit_one_is_black(uncolor));
                                                                    close();
                                                                }
                                                                step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                    rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                    close();
                                                                }
                                                                have unp == gparent by {
                                                                    apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                    close();
                                                                }
                                                                have usib == RbTree::Node(unid, gparent, Color::Black, unl, unr) by {
                                                                    rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                    rewrite(unp, gparent);
                                                                    rewrite(uncolor, Color::Black);
                                                                    close();
                                                                }
                                                                have (tmp->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                    rewrite(Color::Black, uncolor);
                                                                    close();
                                                                }
                                                                    unfold(triangle_uncle_link);
                                                                    have gparent->rb_left == tmp by { close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(unid->rb_left)) by { close(); }
                                                                    have unid->rb_left == at(triangle_before_middle_load, unid->rb_left) by close();
                                                                    unfold(triangle_saved_rb_left);
                                                                    have tmp->rb_left == unid->rb_left by { rewrite(tmp, unid); close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(unid->rb_right)) by { close(); }
                                                                    have unid->rb_right == at(triangle_before_middle_load, unid->rb_right) by close();
                                                                    unfold(triangle_saved_rb_right);
                                                                    have tmp->rb_right == unid->rb_right by { rewrite(tmp, unid); close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_right) == at(statement(1).statement(4).statement(9).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_right) == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have node->rb_right == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_left) == at(statement(1).statement(4).statement(9).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_left) == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                    have node->rb_left == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                    let un = fold(rb_at(uid->rb_left), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Node(unid, gparent, Color::Black, unl, unr));
                                                                    close();
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                unfold(us);
                                                                step();
                                                                    step();
                                                                    step();
                                                                have ucolor == Color::Black by {
                                                                    apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                    close();
                                                                }
                                                                    unfold(triangle_uncle_link);
                                                                    have gparent->rb_left == tmp by { close(); }
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_right)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_right) == at(statement(1).statement(4).statement(9).entry, node->rb_right) by { preserve(memory(node->rb_right), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_right) == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have node->rb_right == at(triangle_before_uncle_load, node->rb_right) by close();
                                                                    have separate(statement(1).statement(4).statement(9).footprint, memory(node->rb_left)) by { close(); }
                                                                    have at(statement(1).statement(4).statement(9).exit, node->rb_left) == at(statement(1).statement(4).statement(9).entry, node->rb_left) by { preserve(memory(node->rb_left), statement(1).statement(4).statement(9)); }
                                                                    have at(statement(1).statement(4).statement(9).entry, node->rb_left) == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                    have node->rb_left == at(triangle_before_uncle_load, node->rb_left) by close();
                                                                let un = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have un.model == usib by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    close();
                                                                }
                                                            },
                                                        }
                                                            unfold(triangle_focus_link);
                                                            unfold(triangle_tag);
                                                            mark before_uncle_pointer_changes;
                                                            have at(before_uncle_pointer_changes, gparent->rb_left == tmp) by { close(); }
                                                        have cup == Context::Right(gparent, ugp, Color::Black, usib, uup) by {
                                                            rewrite(cup, Context::Right(uid, ugp, ucolor, usib, uup));
                                                            rewrite(ucolor, Color::Black);
                                                            rewrite(uid, gparent);
                                                            close();
                                                        }
                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have nparent == cid by {
                                                            apply(rb_parent_is_node_parent(nid, nparent, ncolor, nleft, nright, parent));
                                                            close();
                                                        }
                                                        have color_bit(ncolor) == 0 by {
                                                            unfold(rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(color_bit(ncolor), rb_color_bit(RbTree::Node(nid, nparent, ncolor, nleft, nright)));
                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ncolor == Color::Red by {
                                                            apply(color_bit_zero_is_red(ncolor));
                                                            close();
                                                        }
                                                        have t.model == RbTree::Node(nid, cid, Color::Red, nleft, nright) by {
                                                            rewrite(t.model, RbTree::Node(nid, nparent, ncolor, nleft, nright));
                                                            rewrite(nparent, cid);
                                                            rewrite(ncolor, Color::Red);
                                                            close();
                                                        }
                                                        have is_rb(RbTree::Node(nid, cid, Color::Red, nleft, nright)) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            close();
                                                        }
                                                        have ctx_rb(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), black_height(RbTree::Node(nid, cid, Color::Red, nleft, nright)), Color::Black) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_parent_consistent(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright)), 0) == 1 by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        have rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(RbTree::Node(nid, cid, Color::Red, nleft, nright), t.model);
                                                            rewrite(Context::Right(gparent, ugp, Color::Black, usib, uup), cup);
                                                            rewrite(gparent, cgp);
                                                            rewrite(Color::Red, ccolor);
                                                            close();
                                                        }
                                                        apply(ctx_insert_case3_right_step(ugp, gparent, cid, nid, usib, csib, nleft, nright, uup));
                                                        let { left: nl_at, right: nr_at } = unfold(t);
                                                        have (node->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                                rewrite(Color::Red, ncolor); close();
                                                        }
                                                            have node == at(before_gparent_call, node) by { close(); }
                                                            have node->rb_left == at(before_gparent_call, node)->rb_left by {
                                                                rewrite(node, at(before_gparent_call, node)); close();
                                                            }
                                                            have node->rb_right == at(before_gparent_call, node)->rb_right by {
                                                                rewrite(node, at(before_gparent_call, node)); close();
                                                            }
                                                            let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright), left: nl_at, right: nr_at });
                                                            let held_uncle_link = fold(insert_left_link(gparent), { link: InsertLink::To(at(before_uncle_pointer_changes, tmp)) });
                                                            let held_focus_link = fold(insert_right_link(parent), { link: InsertLink::To(node) });
                                                            let rotation_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                        match cs.model ensuring {
                                                            owns sn: rb_at(tmp);
                                                                owns rotation_tag: insert_parent_tag(gparent, ugp);
                                                                fact rotation_tag.color == ucolor;
                                                                fact gparent->rb_right == tmp;
                                                                fact parent->rb_left == gparent;
                                                            fact sn.model == rb_reparent(csib, gparent);
                                                            fact gparent->rb_left == at(before_uncle_pointer_changes, tmp);
                                                            fact parent->rb_right == node;
                                                        } {
                                                            RbTree::Empty => {
                                                                unfold(cs);
                                                                    have parent->rb_left == cid->rb_left by { rewrite(parent, cid); close(); }
                                                                    mark before_sibling_read;
                                                                step();
                                                                step();
                                                                    have tmp == at(before_sibling_read, cid->rb_left) by close();
                                                                step();
                                                                step();
                                                                step();
                                                                    let written_sibling_link = fold(insert_right_link(gparent), { link: InsertLink::To(tmp) });
                                                                    step();
                                                                    let written_grandparent_link = fold(insert_left_link(parent), { link: InsertLink::To(gparent) });
                                                                step();
                                                                step();
                                                                    unfold(written_sibling_link);
                                                                    unfold(written_grandparent_link);
                                                                have rb_reparent(csib, gparent) == RbTree::Empty by {
                                                                    rewrite(csib, RbTree::Empty);
                                                                    unfold(rb_reparent(RbTree::Empty, gparent)); close();
                                                                }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Empty });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent), RbTree::Empty);
                                                                    close();
                                                                }
                                                                    unfold(held_uncle_link);
                                                                    have gparent->rb_left == at(before_uncle_pointer_changes, tmp) by close();
                                                                    unfold(held_focus_link);
                                                                    have parent->rb_right == node by close();
                                                                    have gparent->rb_right == tmp by close();
                                                                    have parent->rb_left == gparent by close();
                                                            },
                                                            RbTree::Node(sx, sp, scol, sl, sr) => {
                                                                let { left: sl_at, right: sr_at } = unfold(cs);
                                                                    have sx == cid->rb_left by close();
                                                                    have sx->rb_left == cid->rb_left->rb_left by { rewrite(sx, cid->rb_left); close(); }
                                                                    have sx->rb_right == cid->rb_left->rb_right by { rewrite(sx, cid->rb_left); close(); }
                                                                    let saved_child_left = fold(insert_left_link(sx), { link: InsertLink::To(sx->rb_left) });
                                                                    let saved_child_right = fold(insert_right_link(sx), { link: InsertLink::To(sx->rb_right) });
                                                                    have parent->rb_left == cid->rb_left by { rewrite(parent, cid); close(); }
                                                                    mark before_sibling_read;
                                                                step();
                                                                step();
                                                                    have tmp == at(before_sibling_read, cid->rb_left) by close();
                                                                    have tmp == sx by close();
                                                                    let { left: node_l, right: node_r } = unfold(t);
                                                                    have separate(memory(node->__rb_parent_color), memory(sx->__rb_parent_color)) by close();
                                                                    step(); // Disjoint owned nodes rule out the triangle branch.
                                                                    let t = fold(rb_at(node), { model: RbTree::Node(nid, cid, Color::Red, nleft, nright), left: node_l, right: node_r });
                                                                have gparent == uid by { close(); }
                                                                have tmp == sx by { close(); }
                                                                have rb_root_black(RbTree::Node(sx, sp, scol, sl, sr)) == 1 by {
                                                                    rewrite(RbTree::Node(sx, sp, scol, sl, sr), csib);
                                                                    close();
                                                                }
                                                                have color_bit(scol) == 1 by {
                                                                    apply(rb_root_black_node_color_bit(sx, sp, scol, sl, sr));
                                                                    close();
                                                                }
                                                                have rb_reparent(csib, gparent) == RbTree::Node(sx, gparent, scol, sl, sr) by {
                                                                    rewrite(csib, RbTree::Node(sx, sp, scol, sl, sr));
                                                                    unfold(rb_reparent(RbTree::Node(sx, sp, scol, sl, sr), gparent)); close();
                                                                }
                                                                step();
                                                                step();
                                                                    let written_sibling_link = fold(insert_right_link(gparent), { link: InsertLink::To(tmp) });
                                                                step();
                                                                    let written_grandparent_link = fold(insert_left_link(parent), { link: InsertLink::To(gparent) });
                                                                step();
                                                                    mark before_sibling_recolor;
                                                                    have separate(memory(sx->rb_left), memory(sx->__rb_parent_color)) by close();
                                                                    have separate(memory(sx->rb_left), memory(tmp->__rb_parent_color)) by { rewrite(tmp, sx); close(); }
                                                                    have separate(memory(sx->rb_right), memory(sx->__rb_parent_color)) by close();
                                                                    have separate(memory(sx->rb_right), memory(tmp->__rb_parent_color)) by { rewrite(tmp, sx); close(); }
                                                                step();
                                                                    have separate(statement(1).statement(4).statement(15).statement(0).footprint, memory(sx->rb_left)) by { close(); }
                                                                    have sx->rb_left == at(before_sibling_recolor, sx->rb_left) by { preserve(memory(sx->rb_left), statement(1).statement(4).statement(15).statement(0)); }
                                                                    have separate(statement(1).statement(4).statement(15).statement(0).footprint, memory(sx->rb_right)) by { close(); }
                                                                    have sx->rb_right == at(before_sibling_recolor, sx->rb_right) by { preserve(memory(sx->rb_right), statement(1).statement(4).statement(15).statement(0)); }
                                                                    unfold(written_sibling_link);
                                                                    unfold(written_grandparent_link);
                                                                    unfold(saved_child_left);
                                                                    unfold(saved_child_right);
                                                                    have tmp->rb_left == sx->rb_left by { rewrite(tmp, sx); close(); }
                                                                    have tmp->rb_right == sx->rb_right by { rewrite(tmp, sx); close(); }
                                                                    have aligned(gparent, 8) by { rewrite(gparent, uid); close(); }
                                                                    have (address(gparent) | 1) == address(gparent) + 1 by { close() using { aligned(gparent, 8); }; }
                                                                let sn = fold(rb_at(tmp), { model: RbTree::Node(sx, gparent, scol, sl, sr), left: sl_at, right: sr_at });
                                                                have sn.model == rb_reparent(csib, gparent) by {
                                                                    rewrite(rb_reparent(csib, gparent), RbTree::Node(sx, gparent, scol, sl, sr));
                                                                    close();
                                                                }
                                                                    unfold(held_uncle_link);
                                                                    have gparent->rb_left == at(before_uncle_pointer_changes, tmp) by close();
                                                                    unfold(held_focus_link);
                                                                    have parent->rb_right == node by close();
                                                                    have gparent->rb_right == tmp by close();
                                                                    have parent->rb_left == gparent by close();
                                                            },
                                                        }
                                                            unfold(rotation_tag);
                                                            have ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == ugp by close();
                                                        have (gparent->__rb_parent_color & 1) == 1 by {
                                                            rewrite((gparent->__rb_parent_color & 1), color_bit(ucolor));
                                                            rewrite(ucolor, Color::Black);
                                                            unfold(color_bit(Color::Black));
                                                            close();
                                                        }
                                                            have ctx_node_is(uu.model, ugp) == 1 by close();
                                                            have ctx_identity(uu.model) == ugp by { apply(ctx_node_is_identity(uu.model, ugp)); }
                                                            have gparent->__rb_parent_color == address(ugp) + 1 by close();
                                                            apply(insert_black_context_word(uu.model, ugp));
                                                            have ctx_parent_word(uu.model, gparent->__rb_parent_color) == 1 by {
                                                                rewrite(gparent->__rb_parent_color, address(ugp) + 1);
                                                                close();
                                                            }
                                                            let outer_uncle_link = fold(insert_left_link(gparent), { link: InsertLink::To(at(before_uncle_pointer_changes, tmp)) });
                                                            let outer_focus_link = fold(insert_right_link(parent), { link: InsertLink::To(node) });
                                                            let moved_sibling_link = fold(insert_right_link(gparent), { link: InsertLink::To(tmp) });
                                                            let moved_grandparent_link = fold(insert_left_link(parent), { link: InsertLink::To(gparent) });
                                                            let { after: uu } = step(__rb_rotate_set_parents, { c: uu });
                                                            unfold(moved_sibling_link);
                                                            unfold(moved_grandparent_link);
                                                            unfold(outer_uncle_link);
                                                            unfold(outer_focus_link);
                                                            have rb_parent_is(rb_reparent(csib, gparent), gparent) == 1 by {
                                                                apply(rb_reparent_parent_is(csib, gparent));
                                                                close();
                                                            }
                                                            have parent == cid by close();
                                                            have aligned(cid, 8) by close();
                                                            have gparent->__rb_parent_color == address(cid) by { rewrite(cid, parent); close(); }
                                                            have (gparent->__rb_parent_color & 1) == 0 by {
                                                                rewrite(gparent->__rb_parent_color, address(cid));
                                                                close() using { aligned(cid, 8); };
                                                            }
                                                            have gparent->__rb_parent_color == address(cid) + (gparent->__rb_parent_color & 1) by { rewrite((gparent->__rb_parent_color & 1), 0); close(); }
                                                            have ((gparent->__rb_parent_color & ~3) as (struct rb_node *)) == cid by { rewrite(cid, parent); close(); }
                                                            unfold(color_bit(Color::Red));
                                                            let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), left: un, right: sn });
                                                            have rb_parent_is(RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), cid) == 1 by {
                                                                unfold(rb_parent_is(RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), cid));
                                                                close();
                                                            }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                                close();
                                                            }
                                                        let c = fold(ctx_at(node, root), { model: Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup), sibling: gn, up: uu });
                                                        have rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                            rewrite(c.model, Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup));
                                                            rewrite(t.model, RbTree::Node(nid, cid, Color::Red, nleft, nright));
                                                            rewrite(rb_inorder(plug(Context::Right(cid, ugp, Color::Black, RbTree::Node(gparent, cid, Color::Red, usib, rb_reparent(csib, gparent)), uup), RbTree::Node(nid, cid, Color::Red, nleft, nright))), rb_inorder(plug(Context::Right(cid, gparent, Color::Red, csib, Context::Right(gparent, ugp, Color::Black, usib, uup)), RbTree::Node(nid, cid, Color::Red, nleft, nright))));
                                                            close();
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
                                                                    unfold(triangle_uncle_link);
                                                                    unfold(triangle_tag);
                                                                    unfold(triangle_focus_link);
                                                                match uncolor {
                                                                    Color::Red => {
                                                                        have (tmp->__rb_parent_color & 1) == 0 by {
                                                                            rewrite((tmp->__rb_parent_color & 1), color_bit(uncolor));
                                                                            rewrite(uncolor, Color::Red);
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have ucolor == Color::Black by {
                                                                            apply(ctx_rb_right_red_focus_black(uid, ugp, ucolor, usib, uup, black_height(t.model)));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, unp, uncolor, unl, unr), gparent) == 1 by {
                                                                            rewrite(RbTree::Node(unid, unp, uncolor, unl, unr), usib);
                                                                            close();
                                                                        }
                                                                        have unp == gparent by {
                                                                            apply(rb_parent_is_node_parent(unid, unp, uncolor, unl, unr, gparent));
                                                                            close();
                                                                        }
                                                                        have usib == RbTree::Node(unid, gparent, Color::Red, unl, unr) by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(unp, gparent);
                                                                            rewrite(uncolor, Color::Red);
                                                                            close();
                                                                        }
                                                                        have cup == Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup) by {
                                                                            rewrite(cup, Context::Right(uid, ugp, ucolor, usib, uup));
                                                                            rewrite(usib, RbTree::Node(unid, gparent, Color::Red, unl, unr));
                                                                            rewrite(ucolor, Color::Black);
                                                                            rewrite(uid, gparent);
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, cgp, Color::Red, csib, t.model)) == 1 by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup));
                                                                            close();
                                                                        }
                                                                        have almost_rb_insert(RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(gparent, cgp);
                                                                            close();
                                                                        }
                                                                        have black_height(csib) == black_height(t.model) by {
                                                                            apply(ctx_insert_cursor_right_parent(cid, cgp, t.model, csib, cup));
                                                                            close();
                                                                        }
                                                                        apply(ctx_insert_case1_right_step(ugp, gparent, cid, unid, unl, unr, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright), uup));
                                                                        have rb_inorder(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == rb_inorder(plug(old(c.model), RbTree::Node(identity, node_parent, color, left_model, right_model))) by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model)), plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0) == 1 by {
                                                                            apply(plug_right_frame(cid, cgp, ccolor, csib, cup, t.model));
                                                                            rewrite(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), cup);
                                                                            rewrite(gparent, cgp);
                                                                            rewrite(Color::Red, ccolor);
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            rewrite(plug(cup, RbTree::Node(cid, cgp, ccolor, csib, t.model)), plug(Context::Right(cid, cgp, ccolor, csib, cup), t.model));
                                                                            close();
                                                                        }
                                                                        have rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))), 0) == 1 by {
                                                                            rewrite(rb_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))), 0), rb_parent_consistent(plug(Context::Right(gparent, ugp, Color::Black, RbTree::Node(unid, gparent, Color::Red, unl, unr), uup), RbTree::Node(cid, gparent, Color::Red, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), 0));
                                                                            close();
                                                                        }
                                                                        have rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))))) == 1 by {
                                                                            unfold(rb_tree_parent_consistent(plug(uup, RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))))));
                                                                        }
                                                                        have rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))) == 0 by {
                                                                            unfold(rb_color_bit(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)))));
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(nid, nparent, ncolor, nleft, nright), parent) == 1 by {
                                                                            rewrite(RbTree::Node(nid, nparent, ncolor, nleft, nright), t.model);
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Black) == 1 by {
                                                                            unfold(color_bit(Color::Black));
                                                                            close();
                                                                        }
                                                                        have color_bit(Color::Red) == 0 by {
                                                                            unfold(color_bit(Color::Red));
                                                                            close();
                                                                        }
                                                                            let flip_tmp_rb_left = fold(insert_left_link(tmp), { link: InsertLink::To(tmp->rb_left) });
                                                                            let flip_tmp_rb_right = fold(insert_right_link(tmp), { link: InsertLink::To(tmp->rb_right) });
                                                                            let flip_parent_rb_left = fold(insert_left_link(parent), { link: InsertLink::To(parent->rb_left) });
                                                                            let flip_parent_rb_right = fold(insert_right_link(parent), { link: InsertLink::To(parent->rb_right) });
                                                                            let flip_gparent_rb_left = fold(insert_left_link(gparent), { link: InsertLink::To(gparent->rb_left) });
                                                                            let flip_gparent_rb_right = fold(insert_right_link(gparent), { link: InsertLink::To(gparent->rb_right) });
                                                                            let flip_tag = fold(insert_parent_tag(gparent, ugp), { color: ucolor });
                                                                        step();
                                                                        step();
                                                                            unfold(flip_tmp_rb_left);
                                                                            unfold(flip_tmp_rb_right);
                                                                            have aligned(gparent, 8) by { rewrite(gparent, uid); close(); }
                                                                            have (address(gparent) | 1) == address(gparent) + 1 by {
                                                                                close() using { aligned(gparent, 8); };
                                                                            }
                                                                        let un = fold(rb_at(tmp), { model: RbTree::Node(unid, gparent, Color::Black, unl, unr), left: ul, right: ur });
                                                                            step();
                                                                            unfold(flip_parent_rb_left);
                                                                            unfold(flip_parent_rb_right);
                                                                            have parent->__rb_parent_color == (address(gparent) | 1) by close();
                                                                            have parent->__rb_parent_color == address(gparent) + 1 by close();
                                                                            have (parent->__rb_parent_color & 1) == 1 by close();
                                                                            have parent->__rb_parent_color == address(gparent) + (parent->__rb_parent_color & 1) by close();
                                                                            have ((parent->__rb_parent_color & ~3) as (struct rb_node *)) == gparent by close();
                                                                        let pn = fold(rb_at(parent), { model: RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), left: cs, right: t });
                                                                        step();
                                                                            unfold(flip_tag);
                                                                        step();
                                                                            step();
                                                                            have parent == ugp by close();
                                                                        step();
                                                                        have rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright)), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(unid, gparent, Color::Black, unl, unr), gparent));
                                                                            close();
                                                                        }
                                                                        have rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), ugp) == 1 by {
                                                                            unfold(rb_parent_is(RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), ugp));
                                                                            close();
                                                                        }
                                                                            unfold(flip_gparent_rb_left);
                                                                            unfold(flip_gparent_rb_right);
                                                                            have aligned(ugp, 8) by close();
                                                                            have gparent->__rb_parent_color == address(ugp) by close();
                                                                            have (gparent->__rb_parent_color & 1) == 0 by {
                                                                                rewrite(gparent->__rb_parent_color, address(ugp));
                                                                                close() using { aligned(ugp, 8); };
                                                                            }
                                                                            have gparent->__rb_parent_color == address(ugp) + (gparent->__rb_parent_color & 1) by close();
                                                                        let gn = fold(rb_at(gparent), { model: RbTree::Node(gparent, ugp, Color::Red, RbTree::Node(unid, gparent, Color::Black, unl, unr), RbTree::Node(cid, gparent, Color::Black, csib, RbTree::Node(nid, nparent, ncolor, nleft, nright))), left: un, right: pn });
                                                                    },
                                                                    Color::Black => {
                                                                        have rb_root_black(usib) == 1 by {
                                                                            rewrite(usib, RbTree::Node(unid, unp, uncolor, unl, unr));
                                                                            rewrite(uncolor, Color::Black);
                                                                            apply(rb_root_black_black_node(unid, unp, unl, unr));
                                                                            close();
                                                                        }
                                                                        close();
                                                                    },
                                                                }
                                                            },
                                                            RbTree::Empty => {
                                                                have rb_root_black(usib) == 1 by {
                                                                    rewrite(usib, RbTree::Empty);
                                                                    unfold(rb_root_black(RbTree::Empty)); close();
                                                                }
                                                                close();
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
                rewrite(old(t.model), RbTree::Node(identity, node_parent, color, left_model, right_model));
                close();
            }
            mark refold;
            let { whole: tree } = refold_to_root(node, root, { c: c, t: t });
            have rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model))) by {
                rewrite(tree.model, at(refold, plug(c.model, t.model)));
                close();
            }
            have is_rb_root(tree.model) == 1 by {
                rewrite(tree.model, at(refold, plug(c.model, t.model)));
                close();
            }
            have rb_tree_parent_consistent(tree.model) == 1 by {
                rewrite(tree.model, at(refold, plug(c.model, t.model)));
                close();
            }
            step();
            close();
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
    apply(dummy_rotate_is_augment_rotate());
    let { tree: tree } = step(__rb_insert, { c: c, t: t });
    step();
    close();
}
