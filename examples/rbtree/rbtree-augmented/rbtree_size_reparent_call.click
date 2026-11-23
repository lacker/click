import click::integer;
// The insertion middle child keeps its caches and children when reparented.
verifying "rb_insert_augmented.c" as insert;
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_reparent.click";

void insert::rb_set_parent_color(struct rb_node* rb, struct rb_node* p, int32 color) {
    consumes tree: sized_at(rb);
    produces after: sized_at(rb);
    requires rb != 0;
    requires aligned(p, 8);
    requires color == 1;
    ensures after.model == sized_recolor(sized_reparent(old(tree.model), p), Color::Black);
} by {
    match tree.model {
        SizedTree::Empty => {
            unfold(tree);
            contradiction(rb != 0);
        },
        SizedTree::Node(identity, before, shade, value, left_model, right_model) => {
            let { metadata: metadata, left: left, right: right } = unfold(tree);
            have 0 <= color by { rewrite(color, 1); normalize(); }
            have color <= 1 by { rewrite(color, 1); normalize(); }
            step();
            have rb->__rb_parent_color == address(p) + 1 by {
                rewrite(color, 1);
                solve() using { aligned(p, 8); };
            }
            have (rb->__rb_parent_color & ~3) == address(p) by {
                apply(integer::uint64_mask_subset(address(p), 7u64, 3u64));
                apply(integer::uint64_mask_add_clear(address(p), 1u64, 18446744073709551612u64));
                rewrite(rb->__rb_parent_color, address(p) + 1u64);
                known();
            }
            have ((rb->__rb_parent_color & ~3) as (struct rb_node *)) == p by {
                known();
            }
            have (rb->__rb_parent_color & 1) == 1 by {
                rewrite(rb->__rb_parent_color, address(p) + 1);
                solve() using { aligned(p, 8); };
            }
            have rb->__rb_parent_color == address(p) + (rb->__rb_parent_color & 1) by {
                rewrite((rb->__rb_parent_color & 1), 1);
                known();
            }
            unfold(color_bit(Color::Black));
            let after = fold(sized_at(rb), {
                model: SizedTree::Node(identity, p, Color::Black, value, left_model, right_model),
                metadata: metadata, left: left, right: right
            });
            unfold(sized_reparent(SizedTree::Node(identity, before, shade, value, left_model, right_model), p));
            unfold(sized_recolor(SizedTree::Node(identity, p, shade, value, left_model, right_model), Color::Black));
            step_until(function.exit);
        },
    }
}
