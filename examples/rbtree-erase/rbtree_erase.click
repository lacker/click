verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_root.click";

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
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

// Zero- and one-child deletion at the root; general contexts follow.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires up.model == Context::Top;
    requires tree.model != RbTree::Empty;
    requires rb_parent_is(tree.model, 0) == 1;
    requires rb_color(tree.model) == Color::Black;
    requires rb_left(tree.model) == RbTree::Empty or rb_right(tree.model) == RbTree::Empty;
    requires is_rb(tree.model) == 1;
    views erase_callbacks(augment);
    requires separate(memory(*augment), memory(*root));
    requires node->rb_right != 0 implies separate(memory(*augment), memory(node->rb_right->__rb_parent_color));
    requires node->rb_left != 0 implies separate(memory(*augment), memory(node->rb_left->__rb_parent_color));
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces remaining: rb_root_at(root);
    ensures remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0);
    ensures is_rb_root(remaining.model) == 1;
    ensures rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == 0;
} by {
    apply(rb_erase_root_no_deficit(tree.model));
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent, color, left_model, right_model) => {
            have rb_parent_is(RbTree::Node(identity, parent, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            have rb_color(RbTree::Node(identity, parent, color, left_model, right_model)) == Color::Black by {
                rewrite(RbTree::Node(identity, parent, color, left_model, right_model) == tree.model); assumption();
            }
            unfold(rb_color(RbTree::Node(identity, parent, color, left_model, right_model)));
            apply(rb_parent_is_node_parent(identity, parent, color, left_model, right_model, 0));
            have color == Color::Black by {
                rewrite(color == rb_color(RbTree::Node(identity, parent, color, left_model, right_model)));
                assumption();
            }
            have rb_left(tree.model) == left_model by {
                rewrite(tree.model == RbTree::Node(identity, parent, color, left_model, right_model));
                unfold(rb_left(RbTree::Node(identity, parent, color, left_model, right_model))); normalize();
            }
            have rb_right(tree.model) == right_model by auto;
            have left_model == RbTree::Empty or right_model == RbTree::Empty by auto;
            unfold(up);
            let { left: l, right: r } = unfold(tree);
            have color_bit(Color::Black) == 1 by auto;
            have (node->__rb_parent_color & 1) == 1 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(color));
                rewrite(color == Color::Black);
                unfold(color_bit(Color::Black)); normalize();
            }
            if left_model == RbTree::Empty {
                unfold(l);
                have node->rb_left == 0;
                have rb_erase_root_child(old(tree.model)) == right_model by auto;
                match right_model {
                    RbTree::Empty => {
                        unfold(r);
                        open(erase_callbacks(augment)) { execute(); }
                        let result_tree = fold(rb_at(0), { model: RbTree::Empty });
                        let remaining = fold(rb_root_at(root), { model: RbTree::Empty }, { tree: result_tree });
                        have remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0) by {
                            rewrite(rb_erase_root_child(old(tree.model)) == right_model);
                            rewrite(right_model == RbTree::Empty);
                            unfold(rb_recolor(RbTree::Empty, Color::Black));
                            unfold(rb_reparent(RbTree::Empty, 0));
                            assumption();
                        }
                        have is_rb_root(remaining.model) == 1 by {
                            rewrite(remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0));
                            assumption();
                        }
                        have rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                            rewrite(remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0));
                            assumption();
                        }
                        simp();
                    },
                    RbTree::Node(child_id, child_parent, child_color, child_left, child_right) => {
                        let { left: cl, right: cr } = unfold(r);
                        have node->rb_right != 0 by auto;
                        have separate(memory(*augment), memory(node->rb_right->__rb_parent_color)) by auto;
                        open(erase_callbacks(augment)) { execute(); }
                        let result_tree = fold(rb_at(child_id), {
                            model: RbTree::Node(child_id, 0, Color::Black, child_left, child_right)
                        }, { left: cl, right: cr });
                        let remaining = fold(rb_root_at(root), {
                            model: RbTree::Node(child_id, 0, Color::Black, child_left, child_right)
                        }, { tree: result_tree });
                        have remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0) by {
                            rewrite(rb_erase_root_child(old(tree.model)) == right_model);
                            rewrite(right_model == RbTree::Node(child_id, child_parent, child_color, child_left, child_right));
                            unfold(rb_recolor(RbTree::Node(child_id, child_parent, child_color, child_left, child_right), Color::Black));
                            unfold(rb_reparent(RbTree::Node(child_id, child_parent, Color::Black, child_left, child_right), 0));
                            assumption();
                        }
                        have is_rb_root(remaining.model) == 1 by {
                            rewrite(remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0));
                            assumption();
                        }
                        have rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                            rewrite(remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0));
                            assumption();
                        }
                        simp();
                    },
                }
            } else {
                have right_model == RbTree::Empty by {
                    cases {
                        left_model == RbTree::Empty => { contradiction(left_model == RbTree::Empty); }
                        right_model == RbTree::Empty => { assumption(); }
                    }
                }
                unfold(r);
                have node->rb_right == 0;
                match left_model {
                    RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                    RbTree::Node(child_id, child_parent, child_color, child_left, child_right) => {
                        have rb_erase_root_child(old(tree.model)) == left_model by {
                            rewrite(old(tree.model) == RbTree::Node(identity, parent, color, left_model, right_model));
                            rewrite(left_model == RbTree::Node(child_id, child_parent, child_color, child_left, child_right));
                            unfold(rb_erase_root_child(RbTree::Node(identity, parent, color, RbTree::Node(child_id, child_parent, child_color, child_left, child_right), right_model)));
                            normalize();
                        }
                        let { left: cl, right: cr } = unfold(l);
                        have separate(memory(*augment), memory(node->rb_left->__rb_parent_color)) by auto;
                        open(erase_callbacks(augment)) { execute(); }
                        let result_tree = fold(rb_at(child_id), {
                            model: RbTree::Node(child_id, 0, Color::Black, child_left, child_right)
                        }, { left: cl, right: cr });
                        let remaining = fold(rb_root_at(root), {
                            model: RbTree::Node(child_id, 0, Color::Black, child_left, child_right)
                        }, { tree: result_tree });
                        have remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0) by {
                            rewrite(rb_erase_root_child(old(tree.model)) == left_model);
                            rewrite(left_model == RbTree::Node(child_id, child_parent, child_color, child_left, child_right));
                            unfold(rb_recolor(RbTree::Node(child_id, child_parent, child_color, child_left, child_right), Color::Black));
                            unfold(rb_reparent(RbTree::Node(child_id, child_parent, Color::Black, child_left, child_right), 0));
                            assumption();
                        }
                        have is_rb_root(remaining.model) == 1 by {
                            rewrite(remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0));
                            assumption();
                        }
                        have rb_inorder(remaining.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                            rewrite(remaining.model == rb_reparent(rb_recolor(rb_erase_root_child(old(tree.model)), Color::Black), 0));
                            assumption();
                        }
                        simp();
                    },
                }
            }
        },
    }
}
