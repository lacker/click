verifying "rb_erase.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_child.click";

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

// Immediate successor with a nonempty replacement child at the root.
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
    requires rb_right(rb_right(tree.model)) != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires rb_parent_consistent(tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces remaining: rb_root_at(root);
    ensures remaining.model == rb_immediate_successor_child(old(node->rb_right), 0, Color::Black,
        rb_left(old(tree.model)), rb_right(rb_right(old(tree.model))));
    ensures is_rb_root(remaining.model) == 1;
    ensures rb_parent_consistent(remaining.model, 0) == 1;
    ensures rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == 0;
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
            have left_model != RbTree::Empty by auto;
            have right_model != RbTree::Empty by auto;
            have rb_left(right_model) == RbTree::Empty by auto;
            have rb_right(right_model) != RbTree::Empty by auto;
            have is_rb(RbTree::Node(identity, parent, color, left_model, right_model)) == 1 by auto;
            have ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent, color, left_model, right_model)),
                rb_color(RbTree::Node(identity, parent, color, left_model, right_model))) == 1 by {
                unfold(rb_color(RbTree::Node(identity, parent, color, left_model, right_model)));
                rewrite(color == Color::Black);
                unfold(ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent, Color::Black, left_model, right_model)), Color::Black)); unfold(color_black(Color::Black)); normalize();
            }
            have rb_parent_consistent(RbTree::Node(identity, parent, color, left_model, right_model), parent) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model);
                rewrite(parent == 0); assumption();
            }
            unfold(up);
            let { left: l, right: r } = unfold(tree);
            have color_bit(Color::Black) == 1 by auto;
            have (node->__rb_parent_color & 1) == 1 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(color));
                rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
            }
            have node->__rb_parent_color == 1;
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
                    have ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent, color, left_model,
                        RbTree::Node(sid, identity, sc, RbTree::Empty, sr))), color) == 1 by {
                        unfold(ctx_rb(Context::Top, black_height(RbTree::Node(identity, parent, color, left_model,
                            RbTree::Node(sid, identity, sc, RbTree::Empty, sr))), color));
                        rewrite(color == Color::Black); unfold(color_black(Color::Black)); normalize();
                    }
                    apply(rb_erase_immediate_successor_child(identity, sid, parent, color, left_model, sc, sr, Context::Top));
                    have rb_parent_consistent(rb_immediate_successor_child(sid, parent, color, left_model, sr), parent)
                        == rb_parent_consistent(rb_immediate_successor_child(sid, parent, color, left_model, sr), 0) by {
                        rewrite(parent == 0); normalize();
                    }
                    have rb_immediate_successor_child(sid, 0, Color::Black, left_model, sr)
                        == rb_immediate_successor_child(sid, parent, color, left_model, sr) by {
                        rewrite(parent == 0); rewrite(color == Color::Black); normalize();
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
                                        == RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr)) by {
                                        unfold(rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                        rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                        rewrite(sr == RbTree::Node(cid, cp, cc, cl, cr));
                                        unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid));
                                        unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                                        unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), sid));
                                        rewrite(parent == 0); rewrite(color == Color::Black); normalize();
                                    }
                                    unfold(plug(Context::Top, rb_immediate_successor_child(sid, parent, color, left_model, sr)));
                                    let { left: lleft, right: lright } = unfold(l);
                                    open(erase_callbacks(augment)) { execute(); }
                                    let moved_left = fold(rb_at(lid), {
                                        model: RbTree::Node(lid, sid, lc, ll, lr)
                                    }, { left: lleft, right: lright });
                                    let moved_right = fold(rb_at(cid), { model: RbTree::Node(cid, sid, Color::Black, cl, cr) }, { left: cleft, right: cright });
                                    have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by {
                                        unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid));
                                        normalize();
                                    }
                                    have rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid) == 1 by { unfold(rb_parent_is(RbTree::Node(cid, sid, Color::Black, cl, cr), sid)); normalize(); }
                                    let result_tree = fold(rb_at(sid), {
                                        model: RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr))
                                    }, { left: moved_left, right: moved_right });
                                    let remaining = fold(rb_root_at(root), {
                                        model: RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Node(cid, sid, Color::Black, cl, cr))
                                    }, { tree: result_tree });
                                    have remaining.model == rb_immediate_successor_child(sid, parent, color, left_model, sr) by auto;
                                    have remaining.model == rb_immediate_successor_child(old(node->rb_right), 0, Color::Black,
                                        rb_left(old(tree.model)), rb_right(rb_right(old(tree.model)))) by {
                                        rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                        unfold(rb_right(RbTree::Node(sid, sp, sc, sl, sr)));
                                        rewrite(old(node->rb_right) == sid);
                                        rewrite(rb_immediate_successor_child(sid, 0, Color::Black, left_model, sr)
                                            == rb_immediate_successor_child(sid, parent, color, left_model, sr)); assumption();
                                    }
                                    have is_rb_root(remaining.model) == 1 by {
                                        rewrite(remaining.model == rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                        rewrite(rb_immediate_successor_child(sid, parent, color, left_model, sr)
                                            == plug(Context::Top, rb_immediate_successor_child(sid, parent, color, left_model, sr))); assumption();
                                    }
                                    have rb_parent_consistent(remaining.model, 0) == 1 by {
                                        rewrite(remaining.model == rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                        assumption();
                                    }
                                    have rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                        rewrite(remaining.model == rb_immediate_successor_child(sid, parent, color, left_model, sr));
                                        rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                        rewrite(sp == identity); rewrite(sl == RbTree::Empty); assumption();
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
    requires up.model == Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_parent_is(tree.model, 0) == 1;
    requires rb_color(tree.model) == Color::Black;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) == RbTree::Empty;
    requires rb_right(rb_right(tree.model)) != RbTree::Empty;
    requires is_rb(tree.model) == 1;
    requires rb_parent_consistent(tree.model, 0) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == rb_immediate_successor_child(old(node->rb_right), 0, Color::Black,
        rb_left(old(tree.model)), rb_right(rb_right(old(tree.model))));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_parent_consistent(whole.model, 0) == 1;
    ensures rb_inorder(whole.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step();
    let { remaining: whole } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    execute(); simp();
}
