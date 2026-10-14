verifying "rb_erase.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_child.click";

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

// Non-root immediate successor with a nonempty replacement child.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model != Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) == RbTree::Empty;
    requires rb_right(rb_right(tree.model)) != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces replacement: rb_at(old(node->rb_right));
    produces remaining: ctx_at(old(node->rb_right), root);
    ensures replacement.model == rb_erase_immediate_child_model(old(tree.model));
    ensures remaining.model == old(up.model);
    ensures is_rb_root(plug(remaining.model, replacement.model)) == 1;
    ensures ctx_consistent(remaining.model, replacement.model, 0) == 1;
    ensures rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == 0;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            have rb_left(tree.model) == left_model by {
                rewrite(tree.model == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_left(RbTree::Node(identity, parent, color, left_model, right_model))); normalize();
            }
            have rb_right(tree.model) == right_model by {
                rewrite(tree.model == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_right(RbTree::Node(identity, parent, color, left_model, right_model))); normalize();
            }
            have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
            have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_left(right_model) == RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_right(right_model) != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have is_rb(RbTree::Node(identity, parent, color, left_model, right_model)) == 1 by auto;
            have ctx_rb(up.model, black_height(RbTree::Node(identity, parent, color, left_model, right_model)),
                rb_color(RbTree::Node(identity, parent, color, left_model, right_model))) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by auto;
            apply(ctx_consistent_node_children(up.model, identity, parent, color, left_model, right_model, 0));
            apply(rb_node_is_reflexive(parent));
            apply(rb_parent_consistent_node(identity, parent, color, left_model, right_model, parent));
            have ctx_rb(up.model, black_height(RbTree::Node(identity, parent, color, left_model, right_model)), color)
                == ctx_rb(up.model, black_height(RbTree::Node(identity, parent, color, left_model, right_model)),
                    rb_color(RbTree::Node(identity, parent, color, left_model, right_model))) by {
                unfold(rb_color(RbTree::Node(identity, parent, color, left_model, right_model))); normalize();
            }
            let { left: l, right: r } = unfold(tree);
            have color_bit(Color::Black) == 1 by auto;
            match right_model {
                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    have sl == RbTree::Empty by auto;
                    have sr != RbTree::Empty by {
                        unfold(rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sr == rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have rb_parent_is(RbTree::Node(sid, sp, sc, sl, sr), identity) == 1 by {
                        rewrite(identity == node);
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    apply(rb_parent_is_node_parent(sid, sp, sc, sl, sr, identity));
                    have is_rb(RbTree::Node(identity, parent, color, left_model,
                        RbTree::Node(sid, identity, sc, RbTree::Empty, sr))) == 1 by {
                        rewrite(identity == sp);
                        rewrite(RbTree::Empty == sl);
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                        rewrite(sp == identity); assumption();
                    }
                    have rb_parent_consistent(RbTree::Node(identity, parent, color, left_model,
                        RbTree::Node(sid, identity, sc, RbTree::Empty, sr)), parent) == 1 by {
                        rewrite(identity == sp); rewrite(RbTree::Empty == sl);
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                        rewrite(sp == identity); assumption();
                    }
                    have ctx_rb(up.model, black_height(RbTree::Node(identity, parent, color, left_model,
                        RbTree::Node(sid, identity, sc, RbTree::Empty, sr))), color) == 1 by {
                        rewrite(identity == sp); rewrite(RbTree::Empty == sl);
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                        rewrite(sp == identity); assumption();
                    }
                    apply(rb_erase_immediate_successor_child(identity, sid, parent, color, left_model, sc, sr, up.model));
                    apply(ctx_consistent_swap(up.model, identity, parent, color, left_model, right_model,
                        rb_immediate_successor_child(sid, parent, color, left_model, sr), 0));
                    have rb_erase_immediate_child_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                        == rb_immediate_successor_child(sid, parent, color, left_model, sr) by {
                        unfold(rb_erase_immediate_child_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))); normalize();
                    }
                    let { left: sleft, right: sright } = unfold(r);
                    unfold(sleft);
                    match sr {
                        RbTree::Empty => { contradiction(sr == RbTree::Empty); },
                        RbTree::Node(cid, cp, cc, cl, cr) => {
                            let { left: cleft, right: cright } = unfold(sright);
                            match left_model {
                                RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                                RbTree::Node(lid, lp, lc, ll, lr) => {
                                    have rb_immediate_successor_child(sid, parent, color, left_model, sr)
                                        == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) by {
                                        unfold(rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                        rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                        rewrite(sr == RbTree::Node(cid, cp, cc, cl, cr));
                                        unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid));
                                        unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                                        unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), sid));
                                        normalize();
                                    }
                                    let { left: lleft, right: lright } = unfold(l);
                                    match up.model {
                                        Context::Top => { contradiction(up.model == Context::Top); },
                                        Context::Left(pid, gp, pc, sibling_model, above_model) => {
                                            have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                            }
                                            apply(ctx_consistent_left_focus(pid, gp, pc, sibling_model, above_model,
                                                RbTree::Node(identity, parent, color, left_model, right_model), 0));
                                            apply(rb_parent_consistent_node_fixes_parent(identity, parent, color, left_model, right_model, pid));
                                            have is_rb_root(plug(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)))) == 1 by {
                                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                            }
                                            have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)), 0) == 1 by {
                                                rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                            }
                                            let { sibling: sibling, up: above } = unfold(up);
                                            open(erase_callbacks(augment)) { execute(); }
                                            let moved_left = fold(rb_at(lid), { model: RbTree::Node(lid, sid, lc, ll, lr) }, { left: lleft, right: lright });
                                            let moved_right = fold(rb_at(cid), { model: RbTree::Node(cid, sid, Color::Black, cl, cr) }, { left: cleft, right: cright });
                                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid)); normalize(); }
                                            have rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid)); normalize(); }
                                            let replacement = fold(rb_at(sid), { model: RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) }, { left: moved_left, right: moved_right });
                                            let remaining = fold(ctx_at(sid, root), { model: Context::Left(pid, gp, pc, sibling_model, above_model) }, { sibling: sibling, up: above });
                                            have replacement.model == rb_immediate_successor_child(sid, parent, color, left_model, sr) by { rewrite(rb_immediate_successor_child(sid, parent, color, left_model, sr) == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr))); normalize(); }
                                            have replacement.model == rb_erase_immediate_child_model(old(tree.model)) by {
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(rb_erase_immediate_child_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr))) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                            }
                                            have rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                rewrite(replacement.model == rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(sl == RbTree::Empty); rewrite(sp == identity); assumption();
                                            }
                                            simp();
                                        },
                                        Context::Right(pid, gp, pc, sibling_model, above_model) => {
                                            have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                            }
                                            apply(ctx_consistent_right_focus(pid, gp, pc, sibling_model, above_model,
                                                RbTree::Node(identity, parent, color, left_model, right_model), 0));
                                            apply(rb_parent_consistent_node_fixes_parent(identity, parent, color, left_model, right_model, pid));
                                            have is_rb_root(plug(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)))) == 1 by {
                                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                            }
                                            have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)), 0) == 1 by {
                                                rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); rewrite(RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                            }
                                            let { sibling: sibling, up: above } = unfold(up);
                                            match sibling.model {
                                                RbTree::Empty => {
                                                    unfold(sibling);
                                                    open(erase_callbacks(augment)) { execute(); }
                                                    let sibling = fold(rb_at(0), { model: RbTree::Empty });
                                                    let moved_left = fold(rb_at(lid), { model: RbTree::Node(lid, sid, lc, ll, lr) }, { left: lleft, right: lright });
                                                    let moved_right = fold(rb_at(cid), { model: RbTree::Node(cid, sid, Color::Black, cl, cr) }, { left: cleft, right: cright });
                                                    have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid)); normalize(); }
                                                    have rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid)); normalize(); }
                                                    let replacement = fold(rb_at(sid), { model: RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) }, { left: moved_left, right: moved_right });
                                                    let remaining = fold(ctx_at(sid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) }, { sibling: sibling, up: above });
                                                    have replacement.model == rb_immediate_successor_child(sid, parent, color, left_model, sr) by { rewrite(rb_immediate_successor_child(sid, parent, color, left_model, sr) == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr))); normalize(); }
                                                    have replacement.model == rb_erase_immediate_child_model(old(tree.model)) by {
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                        rewrite(rb_erase_immediate_child_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr))) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                                    }
                                                    have rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(replacement.model == rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                                        rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                        rewrite(sl == RbTree::Empty); rewrite(sp == identity); assumption();
                                                    }
                                                    simp();
                                                },
                                                RbTree::Node(sbid, sbp, sbc, sbl, sbr) => {
                                                    let { left: sb_left, right: sb_right } = unfold(sibling);
                                                    open(erase_callbacks(augment)) { execute(); }
                                                    let sibling = fold(rb_at(sbid), { model: RbTree::Node(sbid, sbp, sbc, sbl, sbr) }, { left: sb_left, right: sb_right });
                                                    let moved_left = fold(rb_at(lid), { model: RbTree::Node(lid, sid, lc, ll, lr) }, { left: lleft, right: lright });
                                                    let moved_right = fold(rb_at(cid), { model: RbTree::Node(cid, sid, Color::Black, cl, cr) }, { left: cleft, right: cright });
                                                    have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid)); normalize(); }
                                                    have rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid)); normalize(); }
                                                    let replacement = fold(rb_at(sid), { model: RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) }, { left: moved_left, right: moved_right });
                                                    let remaining = fold(ctx_at(sid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) }, { sibling: sibling, up: above });
                                                    have replacement.model == rb_immediate_successor_child(sid, parent, color, left_model, sr) by { rewrite(rb_immediate_successor_child(sid, parent, color, left_model, sr) == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr))); normalize(); }
                                                    have replacement.model == rb_erase_immediate_child_model(old(tree.model)) by {
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                        rewrite(rb_erase_immediate_child_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr))) == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                                    }
                                                    have rb_inorder(replacement.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(replacement.model == rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                                        rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                        rewrite(sl == RbTree::Empty); rewrite(sp == identity); assumption();
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
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
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
    requires up.model != Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) == RbTree::Empty;
    requires rb_right(rb_right(tree.model)) != RbTree::Empty;
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
    ensures whole.model == plug(old(up.model), rb_erase_immediate_child_model(old(tree.model)));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(rb_erase_immediate_child_model(old(tree.model))) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step();
    let { replacement: replacement, remaining: remaining } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    have rebalance == 0;
    have remaining.model == old(up.model);
    have replacement.model == rb_erase_immediate_child_model(old(tree.model));
    apply(plug_parent_consistent_transport(remaining.model, replacement.model, 0));
    have rb_tree_parent_consistent(plug(remaining.model, replacement.model)) == 1 by {
        unfold(rb_tree_parent_consistent(plug(remaining.model, replacement.model))); assumption();
    }
    mark balanced;
    let { whole: whole } = refold_to_root(old(node->rb_right), root, { c: remaining, t: replacement });
    have whole.model == plug(old(up.model), rb_erase_immediate_child_model(old(tree.model))) by {
        rewrite(whole.model == plug(at(balanced, remaining.model), at(balanced, replacement.model)));
        rewrite(at(balanced, remaining.model) == old(up.model));
        rewrite(at(balanced, replacement.model) == rb_erase_immediate_child_model(old(tree.model))); normalize();
    }
    have is_rb_root(whole.model) == 1 by {
        rewrite(whole.model == plug(at(balanced, remaining.model), at(balanced, replacement.model))); assumption();
    }
    have rb_tree_parent_consistent(whole.model) == 1 by auto;
    execute(); simp();
}
