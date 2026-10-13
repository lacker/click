verifying "rb_erase_augmented.c";
import "../rbtree-erase/rbtree_erase_leaf_wrapper.click";
import "rbtree_erase_color.click";

void rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                        const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) == RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_leaf_result(old(up.model), rb_color(old(tree.model)));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(up.model), RbTree::Empty));
} by {
    step(); // Declare rebalance before its initializer call.
    let { hole: hole, remaining: deficit } = step(__rb_erase_augmented(node, root, augment), { tree: tree, up: up });
    have deficit.model == old(up.model);
    have ctx_consistent(deficit.model, RbTree::Empty, 0) == 1 by { rewrite(RbTree::Empty == hole.model); assumption(); }
    apply(plug_parent_consistent_transport(deficit.model, RbTree::Empty, 0));
    have rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty)) == 1 by {
        unfold(rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty))); assumption();
    }
    if rebalance != 0 {
        have deficit.model != Context::Top;
        have ctx_node_is(deficit.model, rebalance) == 1;
        have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
        have ctx_rb(deficit.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by {
            unfold(black_height(RbTree::Empty)); assumption();
        }
        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(deficit.model, RbTree::Empty);
        unfold(hole);
        step(); // Select the nonnull rebalance branch.
        open(erase_callbacks(augment)) {
            mark repair;
            let { whole: whole } = step(__rb_erase_color(rebalance, root, augment->rotate), { c: deficit });
            have whole.model == erase_leaf_result(old(up.model), rb_color(old(tree.model))) by {
                rewrite(whole.model == erase_flips_red_all_result(at(repair, deficit.model), RbTree::Empty));
                rewrite(erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(at(repair, deficit.model), RbTree::Empty)); normalize();
            }
            have rb_inorder(whole.model) == rb_inorder(plug(old(up.model), RbTree::Empty)) by {
                rewrite(old(up.model) == at(repair, deficit.model)); assumption();
            }
            execute(); simp();
        }
    } else {
        have rebalance == 0;
        have is_rb_root(plug(deficit.model, RbTree::Empty)) == 1;
        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(deficit.model, RbTree::Empty);
        have rb_tree_parent_consistent(plug(deficit.model, hole.model)) == 1 by { rewrite(hole.model == RbTree::Empty); assumption(); }
        mark balanced;
        let { whole: whole } = refold_to_root(0, root, { c: deficit, t: hole });
        have whole.model == plug(old(up.model), RbTree::Empty) by {
            rewrite(whole.model == plug(at(balanced, deficit.model), at(balanced, hole.model)));
            rewrite(at(balanced, hole.model) == RbTree::Empty);
            rewrite(at(balanced, deficit.model) == old(up.model)); normalize();
        }
        have whole.model == erase_leaf_result(old(up.model), rb_color(old(tree.model))) by {
            rewrite(whole.model == plug(old(up.model), RbTree::Empty));
            rewrite(erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(at(balanced, deficit.model), RbTree::Empty));
            rewrite(old(up.model) == at(balanced, deficit.model)); normalize();
        }
        have is_rb_root(whole.model) == 1 by {
            rewrite(whole.model == plug(old(up.model), RbTree::Empty));
            rewrite(old(up.model) == at(balanced, deficit.model)); assumption();
        }
        have rb_tree_parent_consistent(whole.model) == 1 by {
            rewrite(whole.model == plug(old(up.model), RbTree::Empty));
            rewrite(old(up.model) == at(balanced, deficit.model)); assumption();
        }
        have rb_inorder(whole.model) == rb_inorder(plug(old(up.model), RbTree::Empty)) by { rewrite(whole.model == plug(old(up.model), RbTree::Empty)); normalize(); }
        execute(); simp();
    }
}
