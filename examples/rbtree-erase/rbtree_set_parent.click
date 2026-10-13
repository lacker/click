verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_resources.click";

void rb_set_parent(struct rb_node* rb, struct rb_node* p) {
    consumes before: rb_at(rb);
    requires rb != 0;
    requires aligned(p, 8);
    produces after: rb_at(rb);
    ensures after.model == rb_reparent(old(before.model), p);
} by {
    match before.model {
        RbTree::Empty => {
            unfold(before);
            contradiction(rb != 0);
        },
        RbTree::Node(node, parent, color, lm, rm) => {
            let { left: left, right: right } = unfold(before);
            match color {
                Color::Red => {
                    execute();
                    let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm) }, { left: left, right: right });
                    simp();
                },
                Color::Black => {
                    execute();
                    let after = fold(rb_at(rb), { model: RbTree::Node(node, p, color, lm, rm) }, { left: left, right: right });
                    simp();
                },
            }
        },
    }
}
