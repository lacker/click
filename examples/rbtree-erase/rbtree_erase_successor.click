verifying "rb_erase.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_splice.click";

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

# Immediate red-leaf successor at the root.
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
    requires rb_color(rb_right(tree.model)) == Color::Red;
    requires is_rb(tree.model) == 1;
    requires rb_parent_consistent(tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces remaining: rb_root_at(root);
    ensures remaining.model == rb_successor_splice(old(node->rb_right), 0, Color::Black,
        rb_left(old(tree.model)), rb_right(old(tree.model)));
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
            have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
            have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_left(right_model) == RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_right(right_model) == RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have rb_color(right_model) == Color::Red by { rewrite(right_model == rb_right(tree.model)); assumption(); }
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
                    have sc == Color::Red by {
                        unfold(rb_color(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(sc == rb_color(RbTree::Node(sid, sp, sc, sl, sr)));
                        rewrite(RbTree::Node(sid, sp, sc, sl, sr) == right_model); assumption();
                    }
                    have rb_minimum(right_model) == RbMinimum::Found(sid, Color::Red, RbTree::Empty) by {
                        rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                        rewrite(sl == RbTree::Empty); rewrite(sr == RbTree::Empty); rewrite(sc == Color::Red);
                        unfold(rb_minimum(RbTree::Node(sid, sp, Color::Red, RbTree::Empty, RbTree::Empty))); normalize();
                    }
                    have rb_successor_splice(sid, 0, Color::Black, left_model, right_model)
                        == rb_successor_splice(sid, parent, color, left_model, right_model) by {
                        rewrite(parent == 0); rewrite(color == Color::Black); normalize();
                    }
                    apply(rb_erase_red_successor_splice(identity, sid, parent, color, left_model, right_model, Context::Top, 0));
                    let { left: sleft, right: sright } = unfold(r);
                    unfold(sleft); unfold(sright);
                    match left_model {
                        RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                        RbTree::Node(lid, lp, lc, ll, lr) => {
                            have rb_successor_splice(sid, parent, color, left_model, right_model)
                                == RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty) by {
                                unfold(rb_successor_splice(sid, parent, color, left_model, right_model));
                                rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                rewrite(right_model == RbTree::Node(sid, sp, sc, sl, sr));
                                rewrite(sl == RbTree::Empty); rewrite(sr == RbTree::Empty);
                                unfold(rb_remove_min(RbTree::Node(sid, sp, sc, RbTree::Empty, RbTree::Empty)));
                                unfold(rb_reparent(RbTree::Empty, sp)); unfold(rb_reparent(RbTree::Empty, sid));
                                unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), sid));
                                rewrite(parent == 0); rewrite(color == Color::Black); normalize();
                            }
                            unfold(plug(Context::Top, rb_successor_splice(sid, parent, color, left_model, right_model)));
                            let { left: lleft, right: lright } = unfold(l);
                            have (sid->__rb_parent_color & 1) == 0 by {
                                rewrite((sid->__rb_parent_color & 1) == color_bit(sc));
                                rewrite(sc == Color::Red); unfold(color_bit(Color::Red)); normalize();
                            }
                            open(erase_callbacks(augment)) { execute(); }
                            let moved_left = fold(rb_at(lid), {
                                model: RbTree::Node(lid, sid, lc, ll, lr)
                            }, { left: lleft, right: lright });
                            let empty_right = fold(rb_at(0), { model: RbTree::Empty });
                            have rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid) == 1 by {
                                unfold(rb_parent_is(RbTree::Node(lid, sid, lc, ll, lr), sid));
                                normalize();
                            }
                            have rb_parent_is(RbTree::Empty, sid) == 1 by { unfold(rb_parent_is(RbTree::Empty, sid)); normalize(); }
                            let result_tree = fold(rb_at(sid), {
                                model: RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty)
                            }, { left: moved_left, right: empty_right });
                            let remaining = fold(rb_root_at(root), {
                                model: RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty)
                            }, { tree: result_tree });
                            have remaining.model == rb_successor_splice(sid, parent, color, left_model, right_model) by {
                                rewrite(rb_successor_splice(sid, parent, color, left_model, right_model)
                                    == RbTree::Node(sid, 0, Color::Black, RbTree::Node(lid, sid, lc, ll, lr), RbTree::Empty));
                                normalize();
                            }
                            have remaining.model == rb_successor_splice(old(node->rb_right), 0, Color::Black,
                                rb_left(old(tree.model)), rb_right(old(tree.model))) by {
                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model);
                                rewrite(old(node->rb_right) == sid);
                                rewrite(rb_successor_splice(sid, 0, Color::Black, left_model, right_model)
                                    == rb_successor_splice(sid, parent, color, left_model, right_model)); assumption();
                            }
                            have is_rb_root(remaining.model) == 1 by {
                                rewrite(remaining.model == rb_successor_splice(sid, parent, color, left_model, right_model));
                                rewrite(rb_successor_splice(sid, parent, color, left_model, right_model)
                                    == plug(Context::Top, rb_successor_splice(sid, parent, color, left_model, right_model))); assumption();
                            }
                            have rb_parent_consistent(remaining.model, 0) == 1 by {
                                rewrite(remaining.model == rb_successor_splice(sid, parent, color, left_model, right_model));
                                rewrite(rb_successor_splice(sid, parent, color, left_model, right_model)
                                    == plug(Context::Top, rb_successor_splice(sid, parent, color, left_model, right_model))); assumption();
                            }
                            have rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                rewrite(remaining.model == rb_successor_splice(sid, parent, color, left_model, right_model));
                                rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
                            }
                            simp();
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
    requires rb_right(rb_right(tree.model)) == RbTree::Empty;
    requires rb_color(rb_right(tree.model)) == Color::Red;
    requires is_rb(tree.model) == 1;
    requires rb_parent_consistent(tree.model, 0) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == rb_successor_splice(old(node->rb_right), 0, Color::Black,
        rb_left(old(tree.model)), rb_right(old(tree.model)));
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
    have rebalance == 0;
    execute(); simp();
}
