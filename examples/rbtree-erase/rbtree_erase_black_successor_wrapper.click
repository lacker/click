verifying "rb_erase.c";
import "rbtree_erase_black_successor.click";
import "rbtree_erase_color_flips_red_all.click";

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
    requires rb_color(rb_right(tree.model)) == Color::Black;
    requires is_rb(tree.model) == 1;
    requires rb_parent_consistent(tree.model, 0) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_flips_red_all_result(rb_successor_context(old(node->rb_right), 0, Color::Black, rb_left(old(tree.model)), rb_right(old(tree.model)), Context::Top), RbTree::Empty);
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step();
    let { hole: hole, deficit: deficit } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    have deficit.model == rb_successor_context(old(node->rb_right), 0, Color::Black, rb_left(old(tree.model)), rb_right(old(tree.model)), Context::Top);
    have ctx_consistent(deficit.model, RbTree::Empty, 0) == 1 by {
        rewrite(RbTree::Empty == hole.model); assumption();
    }
    apply(plug_parent_consistent_transport(deficit.model, RbTree::Empty, 0));
    have rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty)) == 1 by auto;
    have ctx_rb(deficit.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by {
        unfold(black_height(RbTree::Empty)); assumption();
    }
    have rb_inorder(plug(deficit.model, RbTree::Empty)) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
        rewrite(RbTree::Empty == hole.model); assumption();
    }
    unfold(hole);
    step();
    mark repair;
    let { whole: whole } = step(____rb_erase_color(rebalance, root, dummy_rotate), { c: deficit });
    execute(); simp();
}
