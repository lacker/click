import "../rbtree-model/rbtree_model.click";

// Mathematical sizes; a C representation must separately prove its range bound.
function rb_subtree_size(tree: RbTree) -> Integer
    decreases tree
{
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(node, parent, color, left, right) =>
            rb_subtree_size(left) + rb_subtree_size(right) + 1,
    }
}

theorem rb_subtree_size_nonnegative(tree: RbTree) {
    ensures rb_subtree_size(tree) >= 0 by {
        induct(tree) as ih {
            RbTree::Empty => { unfold(rb_subtree_size(RbTree::Empty)); normalize(); },
            RbTree::Node(node, parent, color, left, right) => {
                apply(ih(left)); apply(ih(right));
                unfold(rb_subtree_size(RbTree::Node(node, parent, color, left, right)));
                arithmetic() using { rb_subtree_size(left) >= 0; rb_subtree_size(right) >= 0; }
            },
        }
    }
}

theorem rb_subtree_size_reparent(tree: RbTree, parent: struct rb_node*) {
    ensures rb_subtree_size(rb_reparent(tree, parent)) == rb_subtree_size(tree) by {
        induct(tree) as ih {
            RbTree::Empty => { unfold(rb_reparent(RbTree::Empty, parent)); normalize(); },
            RbTree::Node(node, before, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, before, color, left, right), parent));
                unfold(rb_subtree_size(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_subtree_size(RbTree::Node(node, before, color, left, right)));
                normalize();
            },
        }
    }
}

// The promoted node copies the old root's summary; the demoted node recomputes.
theorem rb_subtree_size_rotate_left(node: struct rb_node*, parent: struct rb_node*,
    pivot: struct rb_node*, color: Color, pivot_color: Color,
    a: RbTree, b: RbTree, c: RbTree) {
    ensures rb_subtree_size(rb_rotate_left(RbTree::Node(node, parent, color, a, RbTree::Node(pivot, node, pivot_color, b, c)))) == rb_subtree_size(RbTree::Node(node, parent, color, a, RbTree::Node(pivot, node, pivot_color, b, c))) by {
        unfold(rb_rotate_left(RbTree::Node(node, parent, color, a, RbTree::Node(pivot, node, pivot_color, b, c))));
        unfold(rb_subtree_size(RbTree::Node(pivot, parent, pivot_color, RbTree::Node(node, pivot, color, a, rb_reparent(b, node)), c)));
        unfold(rb_subtree_size(RbTree::Node(node, pivot, color, a, rb_reparent(b, node))));
        unfold(rb_subtree_size(RbTree::Node(node, parent, color, a, RbTree::Node(pivot, node, pivot_color, b, c))));
        unfold(rb_subtree_size(RbTree::Node(pivot, node, pivot_color, b, c)));
        apply(rb_subtree_size_reparent(b, node));
        rewrite(rb_subtree_size(rb_reparent(b, node)) == rb_subtree_size(b));
        arithmetic();
    }
    ensures rb_subtree_size(rb_left(rb_rotate_left(RbTree::Node(node, parent, color, a, RbTree::Node(pivot, node, pivot_color, b, c))))) == rb_subtree_size(a) + rb_subtree_size(b) + 1 by {
        unfold(rb_rotate_left(RbTree::Node(node, parent, color, a, RbTree::Node(pivot, node, pivot_color, b, c))));
        unfold(rb_left(RbTree::Node(pivot, parent, pivot_color, RbTree::Node(node, pivot, color, a, rb_reparent(b, node)), c)));
        unfold(rb_subtree_size(RbTree::Node(node, pivot, color, a, rb_reparent(b, node))));
        apply(rb_subtree_size_reparent(b, node));
        rewrite(rb_subtree_size(rb_reparent(b, node)) == rb_subtree_size(b));
        normalize();
    }
}

// The promoted node copies the old root's summary; the demoted node recomputes.
theorem rb_subtree_size_rotate_right(node: struct rb_node*, parent: struct rb_node*,
    pivot: struct rb_node*, color: Color, pivot_color: Color,
    a: RbTree, b: RbTree, c: RbTree) {
    ensures rb_subtree_size(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Node(pivot, node, pivot_color, a, b), c))) == rb_subtree_size(RbTree::Node(node, parent, color, RbTree::Node(pivot, node, pivot_color, a, b), c)) by {
        unfold(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Node(pivot, node, pivot_color, a, b), c)));
        unfold(rb_subtree_size(RbTree::Node(pivot, parent, pivot_color, a, RbTree::Node(node, pivot, color, rb_reparent(b, node), c))));
        unfold(rb_subtree_size(RbTree::Node(node, pivot, color, rb_reparent(b, node), c)));
        unfold(rb_subtree_size(RbTree::Node(node, parent, color, RbTree::Node(pivot, node, pivot_color, a, b), c)));
        unfold(rb_subtree_size(RbTree::Node(pivot, node, pivot_color, a, b)));
        apply(rb_subtree_size_reparent(b, node));
        rewrite(rb_subtree_size(rb_reparent(b, node)) == rb_subtree_size(b));
        arithmetic();
    }
    ensures rb_subtree_size(rb_right(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Node(pivot, node, pivot_color, a, b), c)))) == rb_subtree_size(b) + rb_subtree_size(c) + 1 by {
        unfold(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Node(pivot, node, pivot_color, a, b), c)));
        unfold(rb_right(RbTree::Node(pivot, parent, pivot_color, a, RbTree::Node(node, pivot, color, rb_reparent(b, node), c))));
        unfold(rb_subtree_size(RbTree::Node(node, pivot, color, rb_reparent(b, node), c)));
        apply(rb_subtree_size_reparent(b, node));
        rewrite(rb_subtree_size(rb_reparent(b, node)) == rb_subtree_size(b));
        normalize();
    }
}
