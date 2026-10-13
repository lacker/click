verifying "rb_erase_augmented.c";
import "../rbtree-erase/rbtree_erase_color_flips_red_all.click";

void __rb_erase_color(struct rb_node* parent, struct rb_root* root,
void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
    consumes c: ctx_at(0, root);
    requires AugmentRotate(augment_rotate);
    requires c.model != Context::Top;
    requires ctx_node_is(c.model, parent) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_tree_parent_consistent(plug(c.model, RbTree::Empty)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_flips_red_all_result(old(c.model), RbTree::Empty);
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by {
    let { whole: whole } = step(____rb_erase_color(parent, root, augment_rotate), { c: c });
    execute(); simp();
}
