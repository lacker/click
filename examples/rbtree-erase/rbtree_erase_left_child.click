verifying "rb_erase.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_one_child.click";
import "../rbtree-model/rbtree_context_depth.click";
import "../rbtree-model/rbtree_spine_model.click";

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    views augment->propagate;
    views augment->copy;
    views augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

# A node at any position whose only child is on the left; colors follow from validity.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_right;
    produces node->rb_left;
    produces replacement: rb_at(old(node->rb_left));
    produces remaining: ctx_at(old(node->rb_left), root);
    ensures replacement.model == rb_erase_one_child_model(old(tree.model));
    ensures remaining.model == old(up.model);
    ensures is_rb_root(plug(remaining.model, replacement.model)) == 1;
    ensures ctx_consistent(remaining.model, replacement.model, 0) == 1;
    ensures rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model)));
    ensures result == 0;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(id, parent, color, child, empty) => {
            have empty == RbTree::Empty by {
                unfold(rb_right(RbTree::Node(id, parent, color, child, empty)));
                rewrite(empty == rb_right(RbTree::Node(id, parent, color, child, empty)));
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            have child != RbTree::Empty by {
                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                rewrite(child == rb_left(RbTree::Node(id, parent, color, child, empty)));
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            have is_rb(RbTree::Node(id, parent, color, child, RbTree::Empty)) == 1 by {
                rewrite(RbTree::Empty == empty);
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            have ctx_rb(up.model, black_height(RbTree::Node(id, parent, color, child, RbTree::Empty)),
                rb_color(RbTree::Node(id, parent, color, child, RbTree::Empty))) == 1 by {
                rewrite(RbTree::Empty == empty);
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            apply(rb_erase_only_left_child(id, parent, color, child, up.model));
            have color == Color::Black by { extract(color == Color::Black); assumption(); }
            have is_rb_root(plug(up.model, rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
                extract(is_rb_root(plug(up.model, rb_reparent(rb_recolor(child, Color::Black), parent))) == 1); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                rewrite(RbTree::Node(id, parent, color, child, empty) == tree.model); assumption();
            }
            match child {
                RbTree::Empty => { contradiction(child == RbTree::Empty); },
                RbTree::Node(cid, cp, cc, cl, cr) => {
                    let { left: r, right: l } = unfold(tree);
                    unfold(l);
                    let { left: child_left, right: child_right } = unfold(r);
                    have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
                    have (node->__rb_parent_color & 1) == 1 by {
                        rewrite((node->__rb_parent_color & 1) == color_bit(color));
                        rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                    }
                    have rb_reparent(rb_recolor(child, Color::Black), parent)
                        == RbTree::Node(cid, parent, Color::Black, cl, cr) by {
                        rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                        unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                        unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), parent)); normalize();
                    }
                    match up.model {
                        Context::Top => {
                            have ctx_consistent(Context::Top, RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                                rewrite(Context::Top == up.model); assumption();
                            }
                            apply(ctx_consistent_top(RbTree::Node(id, parent, color, child, empty), 0));
                            apply(rb_parent_consistent_node_fixes_parent(id, parent, color, child, empty, 0));
                            apply(rb_parent_consistent_node_left(id, parent, color, child, empty, 0));
                            apply(rb_erase_child_keeps_parents(up.model, id, parent, color, child, empty, child));
                            have is_rb_root(plug(Context::Top, RbTree::Node(cid, parent, Color::Black, cl, cr))) == 1 by {
                                rewrite(Context::Top == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            have ctx_consistent(Context::Top, RbTree::Node(cid, parent, Color::Black, cl, cr), 0) == 1 by {
                                rewrite(Context::Top == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            unfold(up);
                            open(erase_callbacks(augment)) { execute(); }
                            have cid->__rb_parent_color == node->__rb_parent_color;
                            have cid->__rb_parent_color == address(parent) + (cid->__rb_parent_color & 1);
                            have address(parent) + (cid->__rb_parent_color & 1) == (cid->__rb_parent_color & 1) by {
                                rewrite(parent == 0); normalize();
                            }
                            have cid->__rb_parent_color == (cid->__rb_parent_color & 1);
                            let replacement = fold(rb_at(cid), {
                                model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                            }, { left: child_left, right: child_right });
                            let remaining = fold(ctx_at(cid, root), { model: Context::Top });
                            have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                rewrite(empty == RbTree::Empty);
                                rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                simp();
                            }
                            have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            simp();
                        },
                        Context::Left(pid, gp, pc, sibling_model, above_model) => {
                            have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                            }
                            apply(ctx_consistent_left_focus(pid, gp, pc, sibling_model, above_model,
                                RbTree::Node(id, parent, color, child, empty), 0));
                            apply(rb_parent_consistent_node_fixes_parent(id, parent, color, child, empty, pid));
                            apply(rb_parent_consistent_node_left(id, parent, color, child, empty, pid));
                            apply(rb_erase_child_keeps_parents(up.model, id, parent, color, child, empty, child));
                            have is_rb_root(plug(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr))) == 1 by {
                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr), 0) == 1 by {
                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            let { sibling: sibling, up: above } = unfold(up);
                            open(erase_callbacks(augment)) { execute(); }
                            let replacement = fold(rb_at(cid), {
                                model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                            }, { left: child_left, right: child_right });
                            let remaining = fold(ctx_at(cid, root), { model: Context::Left(pid, gp, pc, sibling_model, above_model) },
                                { sibling: sibling, up: above });
                            have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                rewrite(empty == RbTree::Empty);
                                rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                simp();
                            }
                            have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            simp();
                        },
                        Context::Right(pid, gp, pc, sibling_model, above_model) => {
                            have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(id, parent, color, child, empty), 0) == 1 by {
                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                            }
                            apply(ctx_consistent_right_focus(pid, gp, pc, sibling_model, above_model,
                                RbTree::Node(id, parent, color, child, empty), 0));
                            apply(rb_parent_consistent_node_fixes_parent(id, parent, color, child, empty, pid));
                            apply(rb_parent_consistent_node_left(id, parent, color, child, empty, pid));
                            apply(rb_erase_child_keeps_parents(up.model, id, parent, color, child, empty, child));
                            have is_rb_root(plug(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr))) == 1 by {
                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(cid, parent, Color::Black, cl, cr), 0) == 1 by {
                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model);
                                rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                assumption();
                            }
                            let { sibling: sibling, up: above } = unfold(up);
                            match sibling.model {
                                RbTree::Empty => {
                                    unfold(sibling);
                                    open(erase_callbacks(augment)) { execute(); }
                                    let sibling = fold(rb_at(0), { model: RbTree::Empty });
                                    let replacement = fold(rb_at(cid), {
                                        model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                                    }, { left: child_left, right: child_right });
                                    let remaining = fold(ctx_at(cid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) },
                                        { sibling: sibling, up: above });
                                    have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(empty == RbTree::Empty);
                                        rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                        unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                        rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                        rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                        simp();
                                    }
                                    have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                        assumption();
                                    }
                                    simp();
                                },
                                RbTree::Node(sid, sp, sc, sl, sr) => {
                                    let { left: sl_tree, right: sr_tree } = unfold(sibling);
                                    open(erase_callbacks(augment)) { execute(); }
                                    let sibling = fold(rb_at(sid), { model: RbTree::Node(sid, sp, sc, sl, sr) }, { left: sl_tree, right: sr_tree });
                                    let replacement = fold(rb_at(cid), {
                                        model: RbTree::Node(cid, parent, Color::Black, cl, cr)
                                    }, { left: child_left, right: child_right });
                                    let remaining = fold(ctx_at(cid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) },
                                        { sibling: sibling, up: above });
                                    have replacement.model == rb_erase_one_child_model(old(tree.model)) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        unfold(rb_erase_one_child_model(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(empty == RbTree::Empty);
                                        rewrite(child == RbTree::Node(cid, cp, cc, cl, cr));
                                        unfold(rb_erase_root_child(RbTree::Node(id, parent, color, RbTree::Node(cid, cp, cc, cl, cr), RbTree::Empty)));
                                        rewrite(RbTree::Node(cid, cp, cc, cl, cr) == child);
                                        rewrite(rb_reparent(rb_recolor(child, Color::Black), parent) == RbTree::Node(cid, parent, Color::Black, cl, cr));
                                        simp();
                                    }
                                    have rb_inorder(replacement.model) == rb_inorder(rb_left(old(tree.model))) by {
                                        rewrite(old(tree.model) == RbTree::Node(id, parent, color, child, empty));
                                        unfold(rb_left(RbTree::Node(id, parent, color, child, empty)));
                                        rewrite(RbTree::Node(cid, parent, Color::Black, cl, cr) == rb_reparent(rb_recolor(child, Color::Black), parent));
                                        assumption();
                                    }
                                    simp();
                                },
                            }
                        },
                    }
                },
            }
        },
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
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model)));
                normalize();
            }
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Top);
                rewrite(plug(Context::Top, old(t.model)) == old(t.model));
                simp();
            }
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, up_model) == c.model);
                have rb_parent_consistent(plug(c.model, t.model), 0)
                == rb_tree_parent_consistent(plug(c.model, t.model)) by {
                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                    normalize();
                }
                rewrite(rb_parent_consistent(plug(c.model, t.model), 0)
                == rb_tree_parent_consistent(plug(c.model, t.model)));
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(ctx_depth_is_nonnegative(up_model));
            have 0 <= ctx_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { ctx_depth(old(c.model)) == ctx_depth(up_model) + 1; }
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                normalize();
            }
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) == plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                simp();
            }
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                rewrite(Context::Right(identity, grandparent, color, sibling_model, up_model) == c.model);
                have rb_parent_consistent(plug(c.model, t.model), 0)
                == rb_tree_parent_consistent(plug(c.model, t.model)) by {
                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                    normalize();
                }
                rewrite(rb_parent_consistent(plug(c.model, t.model), 0)
                == rb_tree_parent_consistent(plug(c.model, t.model)));
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)) }, { left: s, right: t });
            apply(ctx_depth_is_nonnegative(up_model));
            have 0 <= ctx_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { ctx_depth(old(c.model)) == ctx_depth(up_model) + 1; }
            }
            have plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) by {
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                normalize();
            }
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)));
                rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) == plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                rewrite(Context::Right(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                rewrite(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))));
                simp();
            }
        },
    }
}


void dummy_propagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
} by { execute(); normalize(); }
void dummy_copy(struct rb_node* old, struct rb_node* new) {
    requires old != 0;
    requires new != 0;
    ensures 1 == 1;
} by { execute(); normalize(); }
void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
} by { execute(); normalize(); }

theorem dummy_propagate_contract() {
    ensures ErasePropagate(&dummy_propagate) by { unfold(ErasePropagate); simp(); }
}
theorem dummy_copy_contract() {
    ensures EraseCopy(&dummy_copy) by { unfold(EraseCopy); simp(); }
}
theorem dummy_rotate_contract() {
    ensures AugmentRotate(&dummy_rotate) by { unfold(AugmentRotate); simp(); }
}

void rb_erase(struct rb_node* node, struct rb_root* root) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == plug(old(up.model), rb_erase_one_child_model(old(tree.model)));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(up.model), rb_left(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step();
    let { replacement: replacement, remaining: remaining } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    have rebalance == 0;
    have remaining.model == old(up.model);
    have replacement.model == rb_erase_one_child_model(old(tree.model));
    apply(plug_parent_consistent_transport(remaining.model, replacement.model, 0));
    have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
        unfold(rb_tree_parent_consistent(plug(remaining.model, replacement.model))); assumption();
    }
    mark balanced;
    let { whole: whole } = refold_to_root(old(node->rb_left), root, { c: remaining, t: replacement });
    have whole.model == plug(old(up.model), rb_erase_one_child_model(old(tree.model))) by {
        rewrite(whole.model == plug(at(balanced, remaining.model), at(balanced, replacement.model)));
        rewrite(at(balanced, remaining.model) == old(up.model));
        rewrite(at(balanced, replacement.model) == rb_erase_one_child_model(old(tree.model))); normalize();
    }
    have is_rb_root(whole.model) == 1 by {
        rewrite(whole.model == plug(at(balanced, remaining.model), at(balanced, replacement.model))); assumption();
    }
    have rb_tree_parent_consistent(whole.model) == 1 by {
        rewrite(whole.model == plug(at(balanced, remaining.model), at(balanced, replacement.model))); assumption();
    }
    have rb_inorder(whole.model) == rb_inorder(plug(old(up.model), rb_left(old(tree.model)))) by {
        rewrite(whole.model == plug(at(balanced, remaining.model), at(balanced, replacement.model)));
        rewrite(old(up.model) == at(balanced, remaining.model));
        apply(plug_inorder_transport(at(balanced, remaining.model), at(balanced, replacement.model), rb_left(old(tree.model))));
        assumption();
    }
    execute(); simp();
}
