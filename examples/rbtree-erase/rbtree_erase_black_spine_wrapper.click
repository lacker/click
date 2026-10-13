verifying "rb_erase.c";
import "rbtree_erase_black_spine.click";
import "rbtree_erase_color_flips_red_all.click";

void rb_erase(struct rb_node* node, struct rb_root* root) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    requires erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty;
    requires erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires is_rb(tree.model) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_flips_red_all_result(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty);
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(up.model), erase_deep_model(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step();
    let { hole: hole, deficit: deficit } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    have deficit.model == erase_deep_context(old(tree.model), old(up.model));
    have ctx_consistent(deficit.model, RbTree::Empty, 0) == 1 by {
        rewrite(RbTree::Empty == hole.model); assumption();
    }
    apply(plug_parent_consistent_transport(deficit.model, RbTree::Empty, 0));
    have rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty)) == 1 by {
        unfold(rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty))); assumption();
    }
    have ctx_rb(deficit.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by {
        unfold(black_height(RbTree::Empty)); assumption();
    }
    have plug(deficit.model, RbTree::Empty) == plug(old(up.model), erase_deep_model(old(tree.model))) by {
        rewrite(RbTree::Empty == hole.model); assumption();
    }
    have rb_inorder(plug(deficit.model, RbTree::Empty)) == rb_inorder(plug(old(up.model), erase_deep_model(old(tree.model)))) by {
        rewrite(plug(deficit.model, RbTree::Empty) == plug(old(up.model), erase_deep_model(old(tree.model)))); normalize();
    }
    unfold(hole);
    step();
    mark repair;
    let { whole: whole } = step(____rb_erase_color(rebalance, root, dummy_rotate), { c: deficit });
    have whole.model == erase_flips_red_all_result(erase_deep_context(old(tree.model), old(up.model)), RbTree::Empty) by {
        rewrite(whole.model == erase_flips_red_all_result(at(repair, deficit.model), RbTree::Empty));
        rewrite(at(repair, deficit.model) == erase_deep_context(old(tree.model), old(up.model))); normalize();
    }
    have rb_inorder(whole.model) == rb_inorder(plug(old(up.model), erase_deep_model(old(tree.model)))) by {
        rewrite(rb_inorder(whole.model) == rb_inorder(plug(at(repair, deficit.model), RbTree::Empty))); assumption();
    }
    execute(); simp();
}
