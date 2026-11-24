import click::integer;
// Regression for post-return imported lemmas with struct-pointer/model arguments.
// The links have already rotated; only the two root summaries are stale.
verifying "../../../examples/rbtree/rbtree-augmented/rbtree_size_rotate.c";
verifying "../../../examples/rbtree/rbtree-augmented/rbtree_size_compute.c";
verifying "../../../examples/rbtree/rbtree-augmented/rbtree_size_copy.c";
import "../../../examples/rbtree/rbtree-augmented/rbtree_size_rotate.click";
import "../../../examples/rbtree/rbtree-augmented/rbtree_size_recompute_model.click";

// Ownership of the demoted prefix and promoted metadata supplies the frame.
tactic rotation_target_separation(node: struct sized_node*, promoted: struct rb_node*) {
    owns node->rb;
    owns metadata: size_metadata(promoted);
    ensures metadata.value == old(metadata.value);
    ensures separate(memory(node->rb.__rb_parent_color), memory((promoted as (uint8 *) as (struct sized_node *))->size));
    ensures separate(memory(node->rb.rb_left), memory((promoted as (uint8 *) as (struct sized_node *))->size));
    ensures separate(memory(node->rb.rb_right), memory((promoted as (uint8 *) as (struct sized_node *))->size));
} by {
    unfold(metadata);
    have separate(memory(node->rb.__rb_parent_color), memory((promoted as (uint8 *) as (struct sized_node *))->size)) by { close(); }
    have separate(memory(node->rb.rb_left), memory((promoted as (uint8 *) as (struct sized_node *))->size)) by { close(); }
    have separate(memory(node->rb.rb_right), memory((promoted as (uint8 *) as (struct sized_node *))->size)) by { close(); }
    fold(metadata);
}

resource sized_rotation_left_at(rb_old: struct rb_node*, rb_new: struct rb_node*) {
    field model: SizedTree;
    match model {
        SizedTree::Empty => { fact rb_new == 0; },
        SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
            owns rb_new->__rb_parent_color;
            owns rb_new->rb_left;
            owns rb_new->rb_right;
            owns metadata: size_metadata(rb_new);
            owns demoted: sized_recompute_at(rb_new->rb_left);
            owns other: sized_at(rb_new->rb_right);
            fact metadata.value == value;
            fact rb_new != 0;
            fact rb_new == identity;
            fact rb_new->rb_left != rb_new;
            fact rb_new->rb_right != rb_new;
            fact aligned(rb_new, 8);
            fact aligned(parent, 8);
            fact rb_new->__rb_parent_color == address(parent) + (rb_new->__rb_parent_color & 1);
            fact ((rb_new->__rb_parent_color & ~3) as (struct rb_node *)) == parent;
            fact (rb_new->__rb_parent_color & 1) == color_bit(color);
            fact sized_parent_is(left_model, rb_new) == 1;
            fact sized_parent_is(right_model, rb_new) == 1;

            fact rb_old == rb_new->rb_left;
            fact demoted.model == left_model;
            fact other.model == right_model;
            fact to_integer(sized_value(left_model)) == 2 + to_integer(sized_value(sized_left(left_model))) + to_integer(sized_value(sized_right(left_model))) + to_integer(sized_value(right_model));
        },
    }
}

contract void RotateTreeLeft(struct rb_node* rb_old, struct rb_node* rb_new) {
    consumes tree: sized_rotation_left_at(rb_old, rb_new);
    produces checked: sized_at(rb_new);
    requires rb_old != 0;
    requires rb_new != 0;
    requires rb_old != rb_new;
    requires 0 <= sized_value(sized_left(sized_left(tree.model)));
    requires 0 <= sized_value(sized_right(sized_left(tree.model)));
    requires sized_value(sized_right(sized_left(tree.model))) <= 2147483646;
    requires sized_value(sized_left(sized_left(tree.model))) <= 2147483646 - sized_value(sized_right(sized_left(tree.model)));
    ensures sized_shape(checked.model) == sized_shape(old(tree.model));
    ensures to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model));
}

theorem sized_rotate_restores_subtree_size_left()
executes sized_rotate(struct rb_node* rb_old, struct rb_node* rb_new) {
    ensures RotateTreeLeft(&sized_rotate) as { tree: tree, checked: checked } by {
        match tree.model {
            SizedTree::Empty => { unfold(tree); contradiction(rb_new == 0); },
            SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right) => {
                let { metadata: promoted_metadata, demoted: demoted, other: other } = unfold(tree);
                let { checked: other } = certify_size(rb_new->rb_right, { tree: other });
                have to_integer(sized_value(promoted_right)) == rb_subtree_size(sized_shape(promoted_right)) by { rewrite(promoted_right, other.model); close(); }
                unfold(sized_left(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                match demoted.model {
                    SizedTree::Empty => {
                        unfold(demoted);
                        have rb_old == 0 by { close(); }
                        contradiction(rb_old == 0);
                    },
                    SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
                        have promoted_left == SizedTree::Node(identity, parent, color, value, left_model, right_model) by { close(); }
                        unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                        have sized_value(promoted_left) == value by {
                            rewrite(promoted_left, SizedTree::Node(identity, parent, color, value, left_model, right_model));
                            unfold(sized_value(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                            normalize();
                        }
                        have sized_left(promoted_left) == left_model by {
                            rewrite(promoted_left, SizedTree::Node(identity, parent, color, value, left_model, right_model));
                            unfold(sized_left(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                            normalize();
                        }
                        have sized_right(promoted_left) == right_model by {
                            rewrite(promoted_left, SizedTree::Node(identity, parent, color, value, left_model, right_model));
                            unfold(sized_right(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                            normalize();
                        }
                        have to_integer(value) == 2 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) + to_integer(sized_value(promoted_right)) by {
                            rewrite(value, sized_value(promoted_left));
                            rewrite(left_model, sized_left(promoted_left));
                            rewrite(right_model, sized_right(promoted_left));
                            close();
                        }
                        let { metadata: metadata, left: left, right: right } = unfold(demoted);
                        rotation_target_separation(rb_old as (uint8 *) as (struct sized_node *), rb_new, { metadata: promoted_metadata });
                        rotation_target_separation(rb_old as (uint8 *) as (struct sized_node *), rb_old, { metadata: metadata });
                        rotation_target_separation(rb_new as (uint8 *) as (struct sized_node *), rb_old, { metadata: metadata });
                        have sized_left(old(tree.model)) == promoted_left by {
                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                            unfold(sized_left(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                            normalize();
                        }
                        have 0 <= sized_value(left_model) by {
                            rewrite(left_model, sized_left(promoted_left));
                            rewrite(promoted_left, sized_left(old(tree.model)));
                            close();
                        }
                        have 0 <= sized_value(right_model) by {
                            rewrite(right_model, sized_right(promoted_left));
                            rewrite(promoted_left, sized_left(old(tree.model)));
                            close();
                        }
                        have sized_value(right_model) <= 2147483646 by {
                            rewrite(right_model, sized_right(promoted_left));
                            rewrite(promoted_left, sized_left(old(tree.model)));
                            close();
                        }
                        have defined(2147483646 - sized_value(right_model));
                        have sized_value(left_model) <= 2147483646 - sized_value(right_model) by {
                            rewrite(left_model, sized_left(promoted_left));
                            rewrite(right_model, sized_right(promoted_left));
                            rewrite(promoted_left, sized_left(old(tree.model)));
                            close();
                        }
                        let { checked: left } = certify_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left, { tree: left });
                        let { checked: right } = certify_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right, { tree: right });
                        have to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model)) by { rewrite(left_model, left.model); close(); }
                        have to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model)) by { rewrite(right_model, right.model); close(); }
                        have to_integer(value) == rb_subtree_size(sized_shape(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right))) by {
                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                            unfold(rb_subtree_size(RbTree::Node(promoted, above, promoted_color, sized_shape(promoted_left), sized_shape(promoted_right))));
                            rewrite(promoted_left, SizedTree::Node(identity, parent, color, value, left_model, right_model));
                            unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                            unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                            close() using {
                                to_integer(value) == 2 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) + to_integer(sized_value(promoted_right));
                                to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                to_integer(sized_value(promoted_right)) == rb_subtree_size(sized_shape(promoted_right));
                            };
                        }
                        unfold(sized_left(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                        unfold(sized_right(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                        match left.model {
                            SizedTree::Empty => {
                                unfold(left);
                                unfold(sized_value(SizedTree::Empty));
                                have (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left == 0 by { close(); }
                                let l = fold(optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { value: 0 });
                                match right.model {
                                    SizedTree::Empty => {
                                        unfold(right);
                                        unfold(sized_value(SizedTree::Empty));
                                        have (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 by { close(); }
                                        let r = fold(optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { value: 0 });
                                        have 0 <= l.value by { close(); }
                                        have 0 <= r.value by { close(); }
                                        have r.value <= 2147483646 by { close(); }
                                        have l.value <= 2147483646 - r.value by { close(); }
                                        apply(size_sum_defined(l.value, r.value));
                                        apply(size_sum_as_integer(l.value, r.value));
                                        have ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent by { rewrite(rb_old, rb_new->rb_left); close(); }
                                        mark before_rotate;
                                        step(sized_rotate, { source: metadata, target: promoted_metadata, left: l, right: r });
                                        have metadata.value == 1 + l.value + r.value by { close(); }
                                        have l.value == 0 by { close(); }
                                        have r.value == 0 by { close(); }
                                        have metadata.value == 1 by {
                                            rewrite(metadata.value, 1 + l.value + r.value);
                                            rewrite(l.value, 0);
                                            rewrite(r.value, 0);
                                            normalize();
                                        }
                                        unfold(l);
                                        let left = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { model: SizedTree::Empty });
                                        unfold(r);
                                        let right = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { model: SizedTree::Empty });
                                        have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(metadata.value, 1);
                                            rewrite(left_model, SizedTree::Empty);
                                            rewrite(right_model, SizedTree::Empty);
                                            unfold(sized_value(SizedTree::Empty));
                                            normalize();
                                        }
                                        have to_integer(1) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(left_model, SizedTree::Empty);
                                            rewrite(right_model, SizedTree::Empty);
                                            unfold(sized_value(SizedTree::Empty));
                                            normalize();
                                        }
                                        have rb_old == rb_new->rb_left by { close(); }
                                        have rb_old->__rb_parent_color == old(rb_old->__rb_parent_color) by { rewrite(rb_old, rb_new->rb_left); close(); }
                                        have old(rb_old->__rb_parent_color) == address(parent) + (old(rb_old->__rb_parent_color) & 1) by { close(); }
                                        have rb_old->__rb_parent_color == address(parent) + (rb_old->__rb_parent_color & 1) by { close(); }
                                        transport(at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent) using {
                                            at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent;
                                            rb_old == at(before_rotate, rb_new->rb_left);
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_old as (uint8 *) as (struct sized_node *))->size));
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
                                        };
                                        let demoted_checked = fold(sized_at(rb_old), { model: SizedTree::Node(identity, parent, color, 1, left_model, right_model), metadata: metadata, left: left, right: right });
                                        have sized_shape(demoted_checked.model) == sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1, left_model, right_model));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            normalize();
                                        }
                                        have to_integer(sized_value(demoted_checked.model)) == rb_subtree_size(sized_shape(demoted_checked.model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1, left_model, right_model));
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                            unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                            close() using {
                                                to_integer(1) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                                to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                                to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                            };
                                        }

                                        have to_integer(sized_value(SizedTree::Node(identity, parent, color, 1, left_model, right_model))) == rb_subtree_size(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model))) by {
                                            rewrite(SizedTree::Node(identity, parent, color, 1, left_model, right_model), demoted_checked.model);
                                            close();
                                        }
                                        apply(sized_parent_is_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model), rb_new));
                                        apply(sized_parent_is_shape(promoted_left, rb_new));
                                        have sized_parent_is(SizedTree::Node(identity, parent, color, 1, left_model, right_model), rb_new) == 1 by {
                                            rewrite(sized_parent_is(SizedTree::Node(identity, parent, color, 1, left_model, right_model), rb_new), rb_parent_is(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)), rb_new));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            rewrite(rb_parent_is(sized_shape(promoted_left), rb_new), sized_parent_is(promoted_left, rb_new));
                                            close();
                                        }

                                        have sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right)) == sized_shape(old(tree.model)) by {
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right)));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            normalize();
                                        }
                                        have to_integer(value) == 1 + to_integer(sized_value(SizedTree::Node(identity, parent, color, 1, left_model, right_model))) + to_integer(sized_value(promoted_right)) by {
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1, left_model, right_model)));
                                            close() using {
                                                to_integer(value) == 2 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) + to_integer(sized_value(promoted_right));
                                                to_integer(1) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                            };
                                        }
                                        have to_integer(value) == rb_subtree_size(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right))) by {
                                            rewrite(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right)), sized_shape(old(tree.model)));
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            close();
                                        }
                                        let checked = fold(sized_at(rb_new), { model: SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right), metadata: promoted_metadata, left: demoted_checked, right: other });
                                        have sized_shape(checked.model) == sized_shape(old(tree.model)) by { close(); }
                                        have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                            rewrite(checked.model, SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right));
                                            unfold(sized_value(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1, left_model, right_model), promoted_right)));
                                            close();
                                        }
                                        close();
                                    },
                                    SizedTree::Node(rid, rp, rc, rv, rl, rr) => {
                                        let { metadata: rm, left: rleft, right: rright } = unfold(right);
                                        unfold(rm);
                                        unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                        have sized_value(right_model) == rv by {
                                            have right_model == SizedTree::Node(rid, rp, rc, rv, rl, rr) by { close(); }
                                            rewrite(right_model, SizedTree::Node(rid, rp, rc, rv, rl, rr));
                                            unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                            normalize();
                                        }
                                        let r = fold(optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { value: rv });
                                        have 0 <= l.value by { close(); }
                                        have 0 <= r.value by { close(); }
                                        have r.value <= 2147483646 by { close(); }
                                        have l.value <= 2147483646 - r.value by { close(); }
                                        apply(size_sum_defined(l.value, r.value));
                                        apply(size_sum_as_integer(l.value, r.value));
                                        child_size_separation(rb_old as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right, { metadata: r });
                                        child_size_separation(rb_new as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right, { metadata: r });
                                        have ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent by { rewrite(rb_old, rb_new->rb_left); close(); }
                                        mark before_rotate;
                                        step(sized_rotate, { source: metadata, target: promoted_metadata, left: l, right: r });
                                        have l.value == 0 by { close(); }
                                        have r.value == rv by { close(); }
                                        have metadata.value == 1 + l.value + r.value by { close(); }
                                        have metadata.value == 1 + rv by {
                                            rewrite(metadata.value, 1 + l.value + r.value);
                                            rewrite(l.value, 0);
                                            rewrite(r.value, rv);
                                            normalize();
                                        }
                                        have to_integer(1 + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(left_model, SizedTree::Empty);
                                            unfold(sized_value(SizedTree::Empty));
                                            rewrite(sized_value(right_model), rv);
                                            close();
                                        }
                                        unfold(l);
                                        let left = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { model: SizedTree::Empty });
                                        unfold(r);
                                        let rm = fold(size_metadata((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { value: rv });
                                        let right = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { model: SizedTree::Node(rid, rp, rc, rv, rl, rr), metadata: rm, left: rleft, right: rright });
                                        have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(metadata.value, 1 + rv);
                                            close();
                                        }
                                        have rb_old == rb_new->rb_left by { close(); }
                                        have rb_old->__rb_parent_color == old(rb_old->__rb_parent_color) by { normalize(); }
                                        have old(rb_old->__rb_parent_color) == address(parent) + (old(rb_old->__rb_parent_color) & 1) by { close(); }
                                        have rb_old->__rb_parent_color == address(parent) + (rb_old->__rb_parent_color & 1) by { close(); }
                                        transport(at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent) using {
                                            at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent;
                                            rb_old == at(before_rotate, rb_new->rb_left);
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_old as (uint8 *) as (struct sized_node *))->size));
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
                                        };
                                        let demoted_checked = fold(sized_at(rb_old), { model: SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), metadata: metadata, left: left, right: right });
                                        have sized_shape(demoted_checked.model) == sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            normalize();
                                        }
                                        have to_integer(sized_value(demoted_checked.model)) == rb_subtree_size(sized_shape(demoted_checked.model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model));
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                            unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                            close() using {
                                                to_integer(1 + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                                to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                                to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                            };
                                        }

                                        have to_integer(sized_value(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model))) == rb_subtree_size(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model))) by {
                                            rewrite(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), demoted_checked.model);
                                            close();
                                        }
                                        apply(sized_parent_is_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), rb_new));
                                        apply(sized_parent_is_shape(promoted_left, rb_new));
                                        have sized_parent_is(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), rb_new) == 1 by {
                                            rewrite(sized_parent_is(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), rb_new), rb_parent_is(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)), rb_new));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            rewrite(rb_parent_is(sized_shape(promoted_left), rb_new), sized_parent_is(promoted_left, rb_new));
                                            close();
                                        }

                                        have sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right)) == sized_shape(old(tree.model)) by {
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right)));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            normalize();
                                        }
                                        have to_integer(value) == 1 + to_integer(sized_value(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model))) + to_integer(sized_value(promoted_right)) by {
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model)));
                                            close() using {
                                                to_integer(value) == 2 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) + to_integer(sized_value(promoted_right));
                                                to_integer(1 + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                            };
                                        }
                                        have to_integer(value) == rb_subtree_size(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right))) by {
                                            rewrite(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right)), sized_shape(old(tree.model)));
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            close();
                                        }
                                        let checked = fold(sized_at(rb_new), { model: SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right), metadata: promoted_metadata, left: demoted_checked, right: other });
                                        have sized_shape(checked.model) == sized_shape(old(tree.model)) by { close(); }
                                        have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                            rewrite(checked.model, SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right));
                                            unfold(sized_value(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + rv, left_model, right_model), promoted_right)));
                                            close();
                                        }
                                        close();
                                    },
                                }
                            },
                            SizedTree::Node(lid, lp, lc, lv, ll, lr) => {
                                let { metadata: lm, left: lleft, right: lright } = unfold(left);
                                unfold(lm);
                                unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                                have sized_value(left_model) == lv by {
                                    have left_model == SizedTree::Node(lid, lp, lc, lv, ll, lr) by { close(); }
                                    rewrite(left_model, SizedTree::Node(lid, lp, lc, lv, ll, lr));
                                    unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                                    normalize();
                                }
                                let l = fold(optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { value: lv });
                                match right.model {
                                    SizedTree::Empty => {
                                        unfold(right);
                                        unfold(sized_value(SizedTree::Empty));
                                        have (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right == 0 by { close(); }
                                        let r = fold(optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { value: 0 });
                                        have 0 <= l.value by { close(); }
                                        have 0 <= r.value by { close(); }
                                        have r.value <= 2147483646 by { close(); }
                                        have sized_value(right_model) == r.value by { close(); }
                                        have sized_value(left_model) == l.value by { close(); }
                                        have 2147483646 - sized_value(right_model) == 2147483646 - r.value by {
                                            rewrite(sized_value(right_model), r.value);
                                            normalize();
                                        }
                                        have l.value <= 2147483646 - r.value by {
                                            rewrite(l.value, sized_value(left_model));
                                            rewrite(2147483646 - r.value, 2147483646 - sized_value(right_model));
                                            close();
                                        }
                                        apply(size_sum_defined(l.value, r.value));
                                        apply(size_sum_as_integer(l.value, r.value));
                                        child_size_separation(rb_old as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left, { metadata: l });
                                        child_size_separation(rb_new as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left, { metadata: l });
                                        have ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent by { rewrite(rb_old, rb_new->rb_left); close(); }
                                        mark before_rotate;
                                        step(sized_rotate, { source: metadata, target: promoted_metadata, left: l, right: r });
                                        have l.value == lv by { close(); }
                                        have r.value == 0 by { close(); }
                                        have metadata.value == 1 + lv by { close(); }
                                        unfold(l);
                                        let lm = fold(size_metadata((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { value: lv });
                                        let left = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { model: SizedTree::Node(lid, lp, lc, lv, ll, lr), metadata: lm, left: lleft, right: lright });
                                        unfold(r);
                                        let right = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { model: SizedTree::Empty });
                                        have to_integer(1 + lv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(left_model, SizedTree::Node(lid, lp, lc, lv, ll, lr));
                                            unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                                            rewrite(right_model, SizedTree::Empty);
                                            unfold(sized_value(SizedTree::Empty));
                                            normalize();
                                            close();
                                        }
                                        have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(metadata.value, 1 + lv);
                                            close();
                                        }
                                        have rb_old == rb_new->rb_left by { close(); }
                                        have rb_old->__rb_parent_color == old(rb_old->__rb_parent_color) by { normalize(); }
                                        have old(rb_old->__rb_parent_color) == address(parent) + (old(rb_old->__rb_parent_color) & 1) by { close(); }
                                        have rb_old->__rb_parent_color == address(parent) + (rb_old->__rb_parent_color & 1) by { close(); }
                                        transport(at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent) using {
                                            at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent;
                                            rb_old == at(before_rotate, rb_new->rb_left);
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_old as (uint8 *) as (struct sized_node *))->size));
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
                                        };
                                        let demoted_checked = fold(sized_at(rb_old), { model: SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), metadata: metadata, left: left, right: right });
                                        have sized_shape(demoted_checked.model) == sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            normalize();
                                        }
                                        have to_integer(sized_value(demoted_checked.model)) == rb_subtree_size(sized_shape(demoted_checked.model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model));
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                            unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                            close() using {
                                                to_integer(1 + lv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                                to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                                to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                            };
                                        }

                                        have to_integer(sized_value(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model))) == rb_subtree_size(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model))) by {
                                            rewrite(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), demoted_checked.model);
                                            close();
                                        }
                                        apply(sized_parent_is_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), rb_new));
                                        apply(sized_parent_is_shape(promoted_left, rb_new));
                                        have sized_parent_is(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), rb_new) == 1 by {
                                            rewrite(sized_parent_is(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), rb_new), rb_parent_is(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)), rb_new));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            rewrite(rb_parent_is(sized_shape(promoted_left), rb_new), sized_parent_is(promoted_left, rb_new));
                                            close();
                                        }

                                        have sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right)) == sized_shape(old(tree.model)) by {
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right)));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            normalize();
                                        }
                                        have to_integer(value) == 1 + to_integer(sized_value(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model))) + to_integer(sized_value(promoted_right)) by {
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model)));
                                            close() using {
                                                to_integer(value) == 2 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) + to_integer(sized_value(promoted_right));
                                                to_integer(1 + lv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                            };
                                        }
                                        have to_integer(value) == rb_subtree_size(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right))) by {
                                            rewrite(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right)), sized_shape(old(tree.model)));
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            close();
                                        }
                                        let checked = fold(sized_at(rb_new), { model: SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right), metadata: promoted_metadata, left: demoted_checked, right: other });
                                        have sized_shape(checked.model) == sized_shape(old(tree.model)) by { close(); }
                                        have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                            rewrite(checked.model, SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right));
                                            unfold(sized_value(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv, left_model, right_model), promoted_right)));
                                            close();
                                        }
                                        close();
                                    },
                                    SizedTree::Node(rid, rp, rc, rv, rl, rr) => {
                                        let { metadata: rm, left: rleft, right: rright } = unfold(right);
                                        unfold(rm);
                                        unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                        have sized_value(right_model) == rv by {
                                            have right_model == SizedTree::Node(rid, rp, rc, rv, rl, rr) by { close(); }
                                            rewrite(right_model, SizedTree::Node(rid, rp, rc, rv, rl, rr));
                                            unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                            normalize();
                                        }
                                        let r = fold(optional_size((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { value: rv });
                                        have 0 <= l.value by { close(); }
                                        have 0 <= r.value by { close(); }
                                        have r.value <= 2147483646 by { close(); }
                                        have l.value <= 2147483646 - r.value by { close(); }
                                        apply(size_sum_defined(l.value, r.value));
                                        apply(size_sum_as_integer(l.value, r.value));
                                        child_size_separation(rb_old as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left, { metadata: l });
                                        child_size_separation(rb_new as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left, { metadata: l });
                                        child_size_separation(rb_old as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right, { metadata: r });
                                        child_size_separation(rb_new as (uint8 *) as (struct sized_node *), (rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right, { metadata: r });
                                        have ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent by { rewrite(rb_old, rb_new->rb_left); close(); }
                                        mark before_rotate;
                                        step(sized_rotate, { source: metadata, target: promoted_metadata, left: l, right: r });
                                        have l.value == lv by { close(); }
                                        have r.value == rv by { close(); }
                                        have metadata.value == 1 + l.value + r.value by { close(); }
                                        have metadata.value == 1 + lv + rv by {
                                            rewrite(metadata.value, 1 + l.value + r.value);
                                            rewrite(l.value, lv);
                                            rewrite(r.value, rv);
                                            normalize();
                                        }
                                        unfold(l);
                                        let lm = fold(size_metadata((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { value: lv });
                                        let left = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_left), { model: SizedTree::Node(lid, lp, lc, lv, ll, lr), metadata: lm, left: lleft, right: lright });
                                        unfold(r);
                                        let rm = fold(size_metadata((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { value: rv });
                                        let right = fold(sized_at((rb_old as (uint8 *) as (struct sized_node *))->rb.rb_right), { model: SizedTree::Node(rid, rp, rc, rv, rl, rr), metadata: rm, left: rleft, right: rright });
                                        have to_integer(1 + lv + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(left_model, SizedTree::Node(lid, lp, lc, lv, ll, lr));
                                            unfold(sized_value(SizedTree::Node(lid, lp, lc, lv, ll, lr)));
                                            rewrite(right_model, SizedTree::Node(rid, rp, rc, rv, rl, rr));
                                            unfold(sized_value(SizedTree::Node(rid, rp, rc, rv, rl, rr)));
                                            normalize();
                                            close();
                                        }
                                        have to_integer(metadata.value) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) by {
                                            rewrite(metadata.value, 1 + lv + rv);
                                            close();
                                        }
                                        have rb_old == rb_new->rb_left by { close(); }
                                        have rb_old->__rb_parent_color == old(rb_old->__rb_parent_color) by { normalize(); }
                                        have old(rb_old->__rb_parent_color) == address(parent) + (old(rb_old->__rb_parent_color) & 1) by { close(); }
                                        have rb_old->__rb_parent_color == address(parent) + (rb_old->__rb_parent_color & 1) by { close(); }
                                        transport(at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *)) == parent) using {
                                            at(before_rotate, ((rb_old->__rb_parent_color & ~3) as (struct rb_node *))) == parent;
                                            rb_old == at(before_rotate, rb_new->rb_left);
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_old as (uint8 *) as (struct sized_node *))->size));
                                            separate(memory(rb_old->__rb_parent_color), memory((rb_new as (uint8 *) as (struct sized_node *))->size));
                                        };
                                        let demoted_checked = fold(sized_at(rb_old), { model: SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), metadata: metadata, left: left, right: right });
                                        have sized_shape(demoted_checked.model) == sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), SizedTree::Node(identity, parent, color, value, left_model, right_model));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            normalize();
                                        }
                                        have to_integer(sized_value(demoted_checked.model)) == rb_subtree_size(sized_shape(demoted_checked.model)) by {
                                            rewrite(demoted_checked.model, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model));
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                            unfold(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                            unfold(rb_subtree_size(RbTree::Node(identity, parent, color, sized_shape(left_model), sized_shape(right_model))));
                                            close() using {
                                                to_integer(1 + lv + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                                to_integer(sized_value(left_model)) == rb_subtree_size(sized_shape(left_model));
                                                to_integer(sized_value(right_model)) == rb_subtree_size(sized_shape(right_model));
                                            };
                                        }

                                        have to_integer(sized_value(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model))) == rb_subtree_size(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model))) by {
                                            rewrite(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), demoted_checked.model);
                                            close();
                                        }
                                        apply(sized_parent_is_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), rb_new));
                                        apply(sized_parent_is_shape(promoted_left, rb_new));
                                        have sized_parent_is(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), rb_new) == 1 by {
                                            rewrite(sized_parent_is(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), rb_new), rb_parent_is(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)), rb_new));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            rewrite(rb_parent_is(sized_shape(promoted_left), rb_new), sized_parent_is(promoted_left, rb_new));
                                            close();
                                        }

                                        have sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right)) == sized_shape(old(tree.model)) by {
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right)));
                                            unfold(sized_shape(SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right)));
                                            rewrite(sized_shape(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)), sized_shape(SizedTree::Node(identity, parent, color, value, left_model, right_model)));
                                            rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), promoted_left);
                                            normalize();
                                        }
                                        have to_integer(value) == 1 + to_integer(sized_value(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model))) + to_integer(sized_value(promoted_right)) by {
                                            unfold(sized_value(SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model)));
                                            close() using {
                                                to_integer(value) == 2 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model)) + to_integer(sized_value(promoted_right));
                                                to_integer(1 + lv + rv) == 1 + to_integer(sized_value(left_model)) + to_integer(sized_value(right_model));
                                            };
                                        }
                                        have to_integer(value) == rb_subtree_size(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right))) by {
                                            rewrite(sized_shape(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right)), sized_shape(old(tree.model)));
                                            rewrite(old(tree.model), SizedTree::Node(promoted, above, promoted_color, stale, promoted_left, promoted_right));
                                            close();
                                        }
                                        let checked = fold(sized_at(rb_new), { model: SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right), metadata: promoted_metadata, left: demoted_checked, right: other });
                                        have sized_shape(checked.model) == sized_shape(old(tree.model)) by { close(); }
                                        have to_integer(sized_value(checked.model)) == rb_subtree_size(sized_shape(checked.model)) by {
                                            rewrite(checked.model, SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right));
                                            unfold(sized_value(SizedTree::Node(promoted, above, promoted_color, value, SizedTree::Node(identity, parent, color, 1 + lv + rv, left_model, right_model), promoted_right)));
                                            close();
                                        }
                                        close();
                                    },
                                }
                            },
                        }

                    },
                }
            },
        }
    }
}
