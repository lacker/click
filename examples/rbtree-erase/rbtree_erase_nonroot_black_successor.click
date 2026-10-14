verifying "rb_erase.c";
import "rbtree_erase_callbacks.click";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_splice.click";

// Immediate black-leaf successor below the root: preserve the deficit for fixup.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model != Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) == RbTree::Empty;
    requires rb_right(rb_right(tree.model)) == RbTree::Empty;
    requires rb_color(rb_right(tree.model)) == Color::Black;
    requires is_rb(tree.model) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces hole: rb_at(0);
    produces deficit: ctx_at(0, root);
    ensures hole.model == RbTree::Empty;
    ensures deficit.model == rb_erase_immediate_black_context(old(tree.model), old(up.model));
    ensures ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
    ensures ctx_consistent(deficit.model, hole.model, 0) == 1;
    ensures plug(deficit.model, hole.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model)));
    ensures result == old(node->rb_right);
    ensures result != 0;
    ensures deficit.model != Context::Top;
    ensures ctx_node_is(deficit.model, result) == 1;
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
            have rb_left(right_model) == RbTree::Empty by auto;
            have rb_right(right_model) == RbTree::Empty by auto;
            have rb_color(right_model) == Color::Black by auto;
            have is_rb(RbTree::Node(identity, parent, color, left_model, right_model)) == 1 by auto;
            have ctx_rb(up.model, black_height(RbTree::Node(identity, parent, color, left_model, right_model)),
                rb_color(RbTree::Node(identity, parent, color, left_model, right_model))) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by auto;
            let { left: l, right: r } = unfold(tree);
            match right_model {
                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    have sl == RbTree::Empty by auto;
                    have sr == RbTree::Empty by {
                        unfold(rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sr == rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have sc == Color::Black by auto;
                    have rb_minimum(right_model) == RbMinimum::Found(sid, Color::Black, RbTree::Empty) by auto;
                    have rb_erase_immediate_leaf_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                        == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)) by {
                        unfold(rb_erase_immediate_leaf_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))); normalize();
                    }
                    apply(rb_erase_black_successor_splice(identity, sid, parent, color, left_model, right_model, up.model, 0));
                    let { left: sleft, right: sright } = unfold(r);
                    unfold(sleft); unfold(sright);
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            have rb_successor_splice(sid, parent, color, left_model, right_model)
                                == RbTree::Node(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) by {
                                unfold(rb_successor_splice(sid, parent, color, left_model, right_model));
                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                rewrite(sl == RbTree::Empty); rewrite(sr == RbTree::Empty);
                                unfold(rb_remove_min(RbTree::Node(sid, sp, sc, RbTree::Empty, RbTree::Empty)));
                                unfold(rb_reparent(RbTree::Empty, sp)); unfold(rb_reparent(RbTree::Empty, sid));
                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid));
                                normalize();
                            }
                            let { left: lleft, right: lright } = unfold(l);
                            have (sid->__rb_parent_color & 1) == 1 by {
                                rewrite((sid->__rb_parent_color & 1) == color_bit(sc));
                                rewrite(sc == Color::Black); unfold(color_bit(Color::Black)); normalize();
                            }
                            have rb_successor_context(sid, parent, color, left_model, right_model, up.model)
                                == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), up.model) by {
                                unfold(rb_successor_context(sid, parent, color, left_model, right_model, up.model));
                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                unfold(rb_reparent(RbTree::Node(sid, sp, sc, sl, sr), sid));
                                rewrite(sl == RbTree::Empty);
                                unfold(rb_min_context(RbTree::Node(sid, sid, sc, RbTree::Empty, sr),
                                    Context::Right(sid, parent, color, rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid), up.model)));
                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid)); normalize();
                            }
                            have rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), up.model)
                                == rb_successor_context(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr), up.model) by {
                                unfold(rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), up.model)); normalize();
                            }
                            match up.model {
                                Context::Top => { contradiction(up.model == Context::Top); },
                                Context::Left(pid, gp, pc, sibling_model, above_model) => {
                                    have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    apply(ctx_consistent_left_focus(pid, gp, pc, sibling_model, above_model,
                                        RbTree::Node(identity, parent, color, left_model, right_model), 0));
                                    apply(rb_parent_consistent_node_fixes_parent(identity, parent, color, left_model, right_model, pid));
                                    have rb_successor_context(sid, parent, color, left_model, right_model, Context::Left(pid, gp, pc, sibling_model, above_model)) == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)) by auto;
                                    have rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), Context::Left(pid, gp, pc, sibling_model, above_model))
                                        == rb_successor_context(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr), Context::Left(pid, gp, pc, sibling_model, above_model)) by {
                                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    have ctx_rb(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                        rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Left(pid, gp, pc, sibling_model, above_model))); rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    have ctx_consistent(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)), RbTree::Empty, 0) == 1 by {
                                        rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Left(pid, gp, pc, sibling_model, above_model))); rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    have plug(rb_successor_context(sid, parent, color, left_model, right_model, Context::Left(pid, gp, pc, sibling_model, above_model)), RbTree::Empty) == plug(Context::Left(pid, gp, pc, sibling_model, above_model), rb_successor_splice(sid, parent, color, left_model, right_model)) by {
                                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    let { sibling: sibling, up: above } = unfold(up);
                                    open(erase_callbacks(augment)) { execute(); }
                                    let moved_left = fold(rb_at(lid), { model: RbTree::Node(lid, sid, lc, ll, lr) }, { left: lleft, right: lright });
                                    let hole = fold(rb_at(0), { model: RbTree::Empty });
                                    let outer = fold(ctx_at(sid, root), { model: Context::Left(pid, gp, pc, sibling_model, above_model) }, { sibling: sibling, up: above });
                                    have ctx_node_is(Context::Left(pid, gp, pc, sibling_model, above_model), parent) == 1 by {
                                        rewrite(parent == pid); unfold(ctx_node_is(Context::Left(pid, gp, pc, sibling_model, above_model), pid)); normalize();
                                    }
                                    have Context::Left(pid, gp, pc, sibling_model, above_model) == ctx_reroot(Context::Left(pid, gp, pc, sibling_model, above_model), parent) by {
                                        rewrite(parent == pid); unfold(ctx_reroot(Context::Left(pid, gp, pc, sibling_model, above_model), pid)); normalize();
                                    }
                                    have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), old(node->rb_right)) == 1 by {
                                        rewrite(sid == old(node->rb_right));
                                        unfold(rb_parent_is(RbTree::Node(lid, old(node->rb_right), lc, ll, lr), old(node->rb_right))); normalize();
                                    }
                                    let deficit = fold(ctx_at(0, root), { model: Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)) }, { sibling: moved_left, up: outer });
                                    have result == sid;
                                    have ctx_node_is(deficit.model, result) == 1 by {
                                        rewrite(deficit.model == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model))); rewrite(result == sid);
                                        unfold(ctx_node_is(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)), sid)); normalize();
                                    }
                                    have deficit.model == rb_erase_immediate_black_context(old(tree.model), old(up.model)) by {
                                        rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                        rewrite(old(up.model) == Context::Left(pid, gp, pc, sibling_model, above_model));
                                        rewrite(rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), Context::Left(pid, gp, pc, sibling_model, above_model))
                                            == rb_successor_context(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr), Context::Left(pid, gp, pc, sibling_model, above_model)));
                                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                                        rewrite(rb_successor_context(sid, parent, color, left_model, right_model, Context::Left(pid, gp, pc, sibling_model, above_model)) == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model))); normalize();
                                    }
                                    have plug(deficit.model, hole.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                        rewrite(old(up.model) == Context::Left(pid, gp, pc, sibling_model, above_model));
                                        rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                        rewrite(rb_erase_immediate_leaf_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                                            == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)));
                                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                                        rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Left(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Left(pid, gp, pc, sibling_model, above_model)));
                                        rewrite(hole.model == RbTree::Empty); assumption();
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
                                    have rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model)) == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) by { rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption(); }
                                    have rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), Context::Right(pid, gp, pc, sibling_model, above_model))
                                        == rb_successor_context(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr), Context::Right(pid, gp, pc, sibling_model, above_model)) by {
                                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    have ctx_rb(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                        rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model))); rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    have ctx_consistent(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)), RbTree::Empty, 0) == 1 by {
                                        rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model))); rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    have plug(rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model)), RbTree::Empty) == plug(Context::Right(pid, gp, pc, sibling_model, above_model), rb_successor_splice(sid, parent, color, left_model, right_model)) by {
                                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                                    }
                                    let { sibling: sibling, up: above } = unfold(up);
                                    match sibling.model {
                                        RbTree::Empty => {
                                            unfold(sibling);
                                            open(erase_callbacks(augment)) { execute(); }
                                            let sibling = fold(rb_at(0), { model: RbTree::Empty });
                                            let moved_left = fold(rb_at(lid), { model: RbTree::Node(lid, sid, lc, ll, lr) }, { left: lleft, right: lright });
                                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                                            let outer = fold(ctx_at(sid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) }, { sibling: sibling, up: above });
                                            have ctx_node_is(Context::Right(pid, gp, pc, sibling_model, above_model), parent) == 1 by {
                                                rewrite(parent == pid); unfold(ctx_node_is(Context::Right(pid, gp, pc, sibling_model, above_model), pid)); normalize();
                                            }
                                            have Context::Right(pid, gp, pc, sibling_model, above_model) == ctx_reroot(Context::Right(pid, gp, pc, sibling_model, above_model), parent) by {
                                                rewrite(parent == pid); unfold(ctx_reroot(Context::Right(pid, gp, pc, sibling_model, above_model), pid)); normalize();
                                            }
                                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), old(node->rb_right)) == 1 by {
                                                rewrite(sid == old(node->rb_right));
                                                unfold(rb_parent_is(RbTree::Node(lid, old(node->rb_right), lc, ll, lr), old(node->rb_right))); normalize();
                                            }
                                            let deficit = fold(ctx_at(0, root), { model: Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) }, { sibling: moved_left, up: outer });
                                            have result == sid;
                                            have ctx_node_is(deficit.model, result) == 1 by {
                                                rewrite(deficit.model == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model))); rewrite(result == sid);
                                                unfold(ctx_node_is(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)), sid)); normalize();
                                            }
                                            have deficit.model == rb_erase_immediate_black_context(old(tree.model), old(up.model)) by {
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(old(up.model) == Context::Right(pid, gp, pc, sibling_model, above_model));
                                                rewrite(rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), Context::Right(pid, gp, pc, sibling_model, above_model))
                                                    == rb_successor_context(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr), Context::Right(pid, gp, pc, sibling_model, above_model)));
                                                rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                                                rewrite(rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model)) == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model))); normalize();
                                            }
                                            have plug(deficit.model, hole.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                rewrite(old(up.model) == Context::Right(pid, gp, pc, sibling_model, above_model));
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(rb_erase_immediate_leaf_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                                                    == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)));
                                                rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                                                rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model)));
                                                rewrite(hole.model == RbTree::Empty); assumption();
                                            }
                                            simp();
                                        },
                                        RbTree::Node(sbid, sbp, sbc, sbl, sbr) => {
                                            let { left: sb_left, right: sb_right } = unfold(sibling);
                                            open(erase_callbacks(augment)) { execute(); }
                                            let sibling = fold(rb_at(sbid), { model: RbTree::Node(sbid, sbp, sbc, sbl, sbr) }, { left: sb_left, right: sb_right });
                                            let moved_left = fold(rb_at(lid), { model: RbTree::Node(lid, sid, lc, ll, lr) }, { left: lleft, right: lright });
                                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                                            let outer = fold(ctx_at(sid, root), { model: Context::Right(pid, gp, pc, sibling_model, above_model) }, { sibling: sibling, up: above });
                                            have ctx_node_is(Context::Right(pid, gp, pc, sibling_model, above_model), parent) == 1 by {
                                                rewrite(parent == pid); unfold(ctx_node_is(Context::Right(pid, gp, pc, sibling_model, above_model), pid)); normalize();
                                            }
                                            have Context::Right(pid, gp, pc, sibling_model, above_model) == ctx_reroot(Context::Right(pid, gp, pc, sibling_model, above_model), parent) by {
                                                rewrite(parent == pid); unfold(ctx_reroot(Context::Right(pid, gp, pc, sibling_model, above_model), pid)); normalize();
                                            }
                                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), old(node->rb_right)) == 1 by {
                                                rewrite(sid == old(node->rb_right));
                                                unfold(rb_parent_is(RbTree::Node(lid, old(node->rb_right), lc, ll, lr), old(node->rb_right))); normalize();
                                            }
                                            let deficit = fold(ctx_at(0, root), { model: Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) }, { sibling: moved_left, up: outer });
                                            have result == sid;
                                            have deficit.model == rb_erase_immediate_black_context(old(tree.model), old(up.model)) by {
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(old(up.model) == Context::Right(pid, gp, pc, sibling_model, above_model));
                                                rewrite(rb_erase_immediate_black_context(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)), Context::Right(pid, gp, pc, sibling_model, above_model))
                                                    == rb_successor_context(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr), Context::Right(pid, gp, pc, sibling_model, above_model)));
                                                rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                                                rewrite(rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model)) == Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model))); normalize();
                                            }
                                            have plug(deficit.model, hole.model) == plug(old(up.model), rb_erase_immediate_leaf_model(old(tree.model))) by {
                                                rewrite(old(up.model) == Context::Right(pid, gp, pc, sibling_model, above_model));
                                                rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                                rewrite(rb_erase_immediate_leaf_model(RbTree::Node(identity, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)))
                                                    == rb_successor_splice(sid, parent, color, left_model, RbTree::Node(sid, sp, sc, sl, sr)));
                                                rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model);
                                                rewrite(Context::Right(sid, parent, color, RbTree::Node(lid, sid, lc, ll, lr), Context::Right(pid, gp, pc, sibling_model, above_model)) == rb_successor_context(sid, parent, color, left_model, right_model, Context::Right(pid, gp, pc, sibling_model, above_model)));
                                                rewrite(hole.model == RbTree::Empty); assumption();
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
}
