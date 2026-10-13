verifying "rb_erase.c";
import "rbtree_erase_callbacks.click";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_splice.click";

// Immediate black-leaf successor: retain the deficit for erase fixup.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model == Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_parent_is(tree.model, 0) == 1;
    requires rb_color(tree.model) == Color::Black;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) == RbTree::Empty;
    requires rb_right(rb_right(tree.model)) == RbTree::Empty;
    requires rb_color(rb_right(tree.model)) == Color::Black;
    requires is_rb(tree.model) == 1;
    requires rb_parent_consistent(tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces hole: rb_at(0);
    produces deficit: ctx_at(0, root);
    ensures hole.model == RbTree::Empty;
    ensures deficit.model == rb_successor_context(old(node->rb_right), 0, Color::Black,
        rb_left(old(tree.model)), rb_right(old(tree.model)), Context::Top);
    ensures ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
    ensures ctx_consistent(deficit.model, hole.model, 0) == 1;
    ensures rb_inorder(plug(deficit.model, hole.model)) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == old(node->rb_right);
    ensures result != 0;
    ensures deficit.model != Context::Top;
    ensures ctx_node_is(deficit.model, result) == 1;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            have rb_parent_is(RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            apply(rb_parent_is_node_parent(identity, parent, color, left_model, right_model, 0));
            have color == Color::Black by {
                unfold(rb_color(RbTree::Node(identity, parent, color, left_model, right_model)));
                rewrite(color == rb_color(RbTree::Node(identity, parent, color, left_model, right_model)));
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
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
            have rb_right(right_model) == RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_color(right_model) == Color::Black by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have is_rb(RbTree::Node(identity, parent, color, left_model, right_model)) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent, color, left_model, right_model)),
                rb_color(RbTree::Node(identity, parent, color, left_model, right_model))) == 1 by {
                unfold(rb_color(RbTree::Node(identity, parent, color, left_model, right_model)));
                rewrite(color == Color::Black);
                unfold(ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent, Color::Black, left_model, right_model)), Color::Black)); unfold(color_black(Color::Black)); normalize();
            }
            have ctx_consistent(Context::Top, RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                unfold(ctx_consistent(Context::Top, RbTree::Node(identity, parent, color, left_model, right_model), 0));
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model);
                rewrite(rb_parent_consistent(tree.model, 0) == 1); normalize();
            }
            unfold(up);
            let { left: l, right: r } = unfold(tree);
            have color_bit(Color::Black) == 1 by { unfold(color_bit(Color::Black)); normalize(); }
            have (node->__rb_parent_color & 1) == 1 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(color));
                rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
            }
            have node->__rb_parent_color == 1;
            match right_model {
                RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    have sl == RbTree::Empty by {
                        unfold(rb_left(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sl == rb_left(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have sr == RbTree::Empty by {
                        unfold(rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sr == rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have sc == Color::Black by {
                        unfold(rb_color(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sc == rb_color(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have rb_minimum(right_model) == RbMinimum::Found(sid, Color::Black, RbTree::Empty) by {
                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                        rewrite(sl == RbTree::Empty); rewrite(sr == RbTree::Empty); rewrite(sc == Color::Black);
                        unfold(rb_minimum(RbTree::Node(sid, sp, Color::Black, RbTree::Empty, RbTree::Empty))); normalize();
                    }
                    apply(rb_erase_black_successor_splice(identity, sid, parent, color, left_model, right_model, Context::Top, 0));
                    let { left: sleft, right: sright } = unfold(r);
                    unfold(sleft); unfold(sright);
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            have rb_successor_context(sid, parent, color, left_model, right_model, Context::Top)
                                == Context::Right(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), Context::Top) by {
                                unfold(rb_successor_context(sid, parent, color, left_model, right_model, Context::Top));
                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                unfold(rb_reparent(RbTree::Node(sid, sp, sc, sl, sr), sid));
                                rewrite(sl == RbTree::Empty);
                                unfold(rb_min_context(RbTree::Node(sid, sid, sc, RbTree::Empty, sr),
                                    Context::Right(sid, parent, color, rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid), Context::Top)));
                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid));
                                rewrite(parent == 0); rewrite(color == Color::Black); normalize();
                            }
                            have rb_successor_context(sid, 0, Color::Black, left_model, right_model, Context::Top)
                                == rb_successor_context(sid, parent, color, left_model, right_model, Context::Top) by {
                                rewrite(parent == 0); rewrite(color == Color::Black); normalize();
                            }
                            let { left: lleft, right: lright } = unfold(l);
                            have (sid->__rb_parent_color & 1) == 1 by {
                                rewrite((sid->__rb_parent_color & 1) == color_bit(sc));
                                rewrite(sc == Color::Black); unfold(color_bit(Color::Black)); normalize();
                            }
                            open(erase_callbacks(augment)) { execute(); }
                            let moved_left = fold(rb_at(lid), {
                                model: RbTree::Node(lid, sid, lc, ll, lr)
                            }, { left: lleft, right: lright });
                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                            let root_context = fold(ctx_at(sid, root), { model: Context::Top });
                            have ctx_node_is(Context::Top, 0) == 1 by { unfold(ctx_node_is(Context::Top, 0)); normalize(); }
                            have Context::Top == ctx_reroot(Context::Top, 0) by { unfold(ctx_reroot(Context::Top, 0)); normalize(); }
                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), old(node->rb_right)) == 1 by {
                                rewrite(sid == old(node->rb_right));
                                unfold(rb_parent_is(RbTree::Node(lid, old(node->rb_right), lc, ll, lr), old(node->rb_right))); normalize();
                            }
                            let deficit = fold(ctx_at(0, root), {
                                model: Context::Right(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), Context::Top)
                            }, { sibling: moved_left, up: root_context });
                            have deficit.model == rb_successor_context(sid, parent, color, left_model, right_model, Context::Top) by {
                                rewrite(rb_successor_context(sid, parent, color, left_model, right_model, Context::Top)
                                    == Context::Right(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), Context::Top)); normalize();
                            }
                            have deficit.model == rb_successor_context(old(node->rb_right), 0, Color::Black,
                                rb_left(old(tree.model)), rb_right(old(tree.model)), Context::Top) by {
                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                rewrite(old(node->rb_right) == sid);
                                rewrite(rb_successor_context(sid, 0, Color::Black, left_model, right_model, Context::Top)
                                    == rb_successor_context(sid, parent, color, left_model, right_model, Context::Top)); assumption();
                            }
                            have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                rewrite(deficit.model == rb_successor_context(sid, parent, color, left_model, right_model, Context::Top)); assumption();
                            }
                            have ctx_consistent(deficit.model, hole.model, 0) == 1 by {
                                rewrite(deficit.model == rb_successor_context(sid, parent, color, left_model, right_model, Context::Top));
                                rewrite(hole.model == RbTree::Empty); assumption();
                            }
                            have rb_inorder(plug(deficit.model, hole.model)) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(deficit.model == rb_successor_context(sid, parent, color, left_model, right_model, Context::Top));
                                rewrite(hole.model == RbTree::Empty);
                                rewrite(plug(rb_successor_context(sid, parent, color, left_model, right_model, Context::Top), RbTree::Empty)
                                    == plug(Context::Top, rb_successor_splice(sid, parent, color, left_model, right_model)));
                                unfold(plug(Context::Top, rb_successor_splice(sid, parent, color, left_model, right_model)));
                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
                            }
                            have result == sid;
                            have ctx_node_is(deficit.model, result) == 1 by {
                                rewrite(deficit.model == Context::Right(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), Context::Top));
                                rewrite(result == sid);
                                unfold(ctx_node_is(Context::Right(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), Context::Top), sid)); normalize();
                            }
                            simp();
                        },
                    }
                },
            }
        },
    }
}
