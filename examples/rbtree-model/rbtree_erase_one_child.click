import "rbtree_erase_child.click";

function rb_erase_one_child_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            rb_reparent(rb_recolor(rb_erase_root_child(tree), Color::Black), parent),
    }
}

// A node with only a nonempty right child is itself the subtree minimum.
theorem rb_erase_only_right_child(node: struct rb_node*, parent: struct rb_node*,
    color: Color, child: RbTree, up: Context) {
    requires is_rb(RbTree::Node(node, parent, color, RbTree::Empty, child)) == 1;
    requires child != RbTree::Empty;
    requires ctx_rb(up, black_height(RbTree::Node(node, parent, color, RbTree::Empty, child)),
        rb_color(RbTree::Node(node, parent, color, RbTree::Empty, child))) == 1;

    ensures color == Color::Black by {
        have rb_minimum(RbTree::Node(node, parent, color, RbTree::Empty, child))
            == RbMinimum::Found(node, color, child) by {
            unfold(rb_minimum(RbTree::Node(node, parent, color, RbTree::Empty, child))); normalize();
        }
        apply(rb_minimum_nonempty_child_parent_color(
            RbTree::Node(node, parent, color, RbTree::Empty, child), node, color, child));
        assumption();
    }
    ensures is_rb_root(plug(up, rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
        have rb_minimum(RbTree::Node(node, parent, color, RbTree::Empty, child))
            == RbMinimum::Found(node, color, child) by {
            unfold(rb_minimum(RbTree::Node(node, parent, color, RbTree::Empty, child))); normalize();
        }
        apply(rb_minimum_child_blackens_without_deficit(
            RbTree::Node(node, parent, color, RbTree::Empty, child), up, node, color, child, parent));
        unfold(rb_min_context(RbTree::Node(node, parent, color, RbTree::Empty, child), up));
        rewrite(up == rb_min_context(RbTree::Node(node, parent, color, RbTree::Empty, child), up));
        assumption();
    }
}

theorem rb_erase_child_keeps_parents(up: Context, node: struct rb_node*, parent: struct rb_node*,
    color: Color, left: RbTree, right: RbTree, child: RbTree) {
    requires ctx_consistent(up, RbTree::Node(node, parent, color, left, right), 0) == 1;
    requires rb_parent_consistent(child, node) == 1;
    ensures ctx_consistent(up, rb_reparent(rb_recolor(child, Color::Black), parent), 0) == 1 by {
        apply(rb_recolor_parent_consistent(child, Color::Black, node));
        apply(rb_reparent_parent_consistent(rb_recolor(child, Color::Black), node, parent));
        apply(ctx_consistent_swap(up, node, parent, color, left, right,
            rb_reparent(rb_recolor(child, Color::Black), parent), 0));
        assumption();
    }
    ensures rb_inorder(rb_reparent(rb_recolor(child, Color::Black), parent)) == rb_inorder(child) by {
        apply(rb_reparent_preserves_inorder(rb_recolor(child, Color::Black), parent));
        apply(rb_recolor_preserves_inorder(child, Color::Black));
        rewrite(rb_inorder(rb_reparent(rb_recolor(child, Color::Black), parent))
            == rb_inorder(rb_recolor(child, Color::Black)));
        assumption();
    }
}

// Local symmetry lets both one-child directions use the same balance argument.
theorem rb_swap_children_valid(node: struct rb_node*, parent: struct rb_node*, color: Color,
    left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;
    ensures is_rb(RbTree::Node(node, parent, color, right, left)) == 1 by {
        induct(color) as ih {
            Color::Red => {
                apply(is_rb_node_left(node, parent, Color::Red, left, right));
                apply(is_rb_node_right(node, parent, Color::Red, left, right));
                apply(is_rb_node_black_heights(node, parent, Color::Red, left, right));
                apply(is_rb_red_node_children_are_black(node, parent, left, right));
                apply(is_rb_red_node_right_child_is_black(node, parent, left, right));
                have black_height(right) == black_height(left) by {
                    rewrite(black_height(right) == black_height(left)); normalize();
                }
                apply(is_rb_red_node(node, parent, right, left)); assumption();
            }
            Color::Black => {
                apply(is_rb_node_left(node, parent, Color::Black, left, right));
                apply(is_rb_node_right(node, parent, Color::Black, left, right));
                apply(is_rb_node_black_heights(node, parent, Color::Black, left, right));
                have black_height(right) == black_height(left) by {
                    rewrite(black_height(right) == black_height(left)); normalize();
                }
                apply(is_rb_black_node(node, parent, right, left)); assumption();
            }
        }
    }
    ensures black_height(RbTree::Node(node, parent, color, right, left))
        == black_height(RbTree::Node(node, parent, color, left, right)) by {
        apply(is_rb_node_black_heights(node, parent, color, left, right));
        apply(black_height_node_frame(node, parent, color, right, left));
        apply(black_height_node_frame(node, parent, color, left, right));
        rewrite(black_height(RbTree::Node(node, parent, color, right, left))
            == frame_black_height(color, black_height(right)));
        rewrite(black_height(RbTree::Node(node, parent, color, left, right))
            == frame_black_height(color, black_height(left)));
        rewrite(black_height(right) == black_height(left)); normalize();
    }
}

theorem rb_erase_only_left_child(node: struct rb_node*, parent: struct rb_node*,
    color: Color, child: RbTree, up: Context) {
    requires is_rb(RbTree::Node(node, parent, color, child, RbTree::Empty)) == 1;
    requires child != RbTree::Empty;
    requires ctx_rb(up, black_height(RbTree::Node(node, parent, color, child, RbTree::Empty)),
        rb_color(RbTree::Node(node, parent, color, child, RbTree::Empty))) == 1;
    ensures color == Color::Black and
        is_rb_root(plug(up, rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
        apply(rb_swap_children_valid(node, parent, color, child, RbTree::Empty));
        have rb_color(RbTree::Node(node, parent, color, RbTree::Empty, child))
            == rb_color(RbTree::Node(node, parent, color, child, RbTree::Empty)) by {
            unfold(rb_color(RbTree::Node(node, parent, color, RbTree::Empty, child)));
            unfold(rb_color(RbTree::Node(node, parent, color, child, RbTree::Empty))); normalize();
        }
        have ctx_rb(up, black_height(RbTree::Node(node, parent, color, RbTree::Empty, child)),
            rb_color(RbTree::Node(node, parent, color, RbTree::Empty, child))) == 1 by {
            rewrite(black_height(RbTree::Node(node, parent, color, RbTree::Empty, child))
                == black_height(RbTree::Node(node, parent, color, child, RbTree::Empty)));
            rewrite(rb_color(RbTree::Node(node, parent, color, RbTree::Empty, child))
                == rb_color(RbTree::Node(node, parent, color, child, RbTree::Empty))); assumption();
        }
        apply(rb_erase_only_right_child(node, parent, color, child, up)); assumption();
    }
}
