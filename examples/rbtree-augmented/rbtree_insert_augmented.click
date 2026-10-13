verifying "rb_insert_augmented.c";
import "../rbtree-insert/rbtree_insert.click";

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    requires AugmentRotate(augment_rotate);
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces tree: rb_root_at(root);
    ensures rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(tree.model) == 1;
    ensures rb_tree_parent_consistent(tree.model) == 1;
} by {
    let { tree: tree } = step(__rb_insert(node, root, augment_rotate), { c: c, t: t });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                 const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    requires AugmentRotate(augment->rotate);
    consumes c: ctx_at(node, root);
    consumes t: rb_at(node);
    requires t.model != RbTree::Empty;
    requires rb_color_bit(t.model) == 0;
    requires ctx_holds(c.model, t.model) == 1;
    requires is_rb(t.model) == 1;
    requires ctx_almost_rb_insert(c.model, black_height(t.model)) == 1;
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces tree: rb_root_at(root);
    ensures rb_inorder(tree.model) == rb_inorder(plug(old(c.model), old(t.model)));
    ensures is_rb_root(tree.model) == 1;
    ensures rb_tree_parent_consistent(tree.model) == 1;
} by {
    let { tree: tree } = step(__rb_insert_augmented(node, root, augment->rotate), { c: c, t: t });
    execute(); simp();
}
