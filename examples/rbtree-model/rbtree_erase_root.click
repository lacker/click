import "rbtree_model.click";

function rb_erase_root_child(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(identity, parent, color, left, right) =>
        match left {
            RbTree::Empty => right,
            RbTree::Node(child, above, child_color, child_left, child_right) => left,
        },
    }
}

theorem rb_erase_root_child_nonempty_left(node: struct rb_node*, parent: struct rb_node*, color: Color,
    left: RbTree, right: RbTree) {
    requires not(left == RbTree::Empty);
    ensures rb_erase_root_child(RbTree::Node(node, parent, color, left, right)) == left by {
        induct(left) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_erase_root_child(RbTree::Node(node, parent, color, RbTree::Node(a, b, c, l, r),
                    right))); normalize();
            }
        }
    }
}

theorem rb_erase_root_child_no_right(node: struct rb_node*, parent: struct rb_node*, color: Color, left:
    RbTree) {
    ensures rb_erase_root_child(RbTree::Node(node, parent, color, left, RbTree::Empty)) == left by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_erase_root_child(RbTree::Node(node, parent, color, RbTree::Empty,
                    RbTree::Empty))); normalize();
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_erase_root_child(RbTree::Node(node, parent, color, RbTree::Node(a, b, c, l, r),
                    RbTree::Empty))); normalize();
            }
        }
    }
}

theorem rb_erase_root_child_is_rb(tree: RbTree) {
    requires is_rb(tree) == 1;
    ensures is_rb(rb_erase_root_child(tree)) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_erase_root_child(RbTree::Empty)); assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(is_rb_node_left(node, parent, color, left, right));
                apply(is_rb_node_right(node, parent, color, left, right));
                if left == RbTree::Empty {
                    rewrite(left == RbTree::Empty);
                    unfold(rb_erase_root_child(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    assumption();
                } else {
                    apply(rb_erase_root_child_nonempty_left(node, parent, color, left, right));
                    rewrite(rb_erase_root_child(RbTree::Node(node, parent, color, left, right)) == left);
                    assumption();
                }
            }
        }
    }
}

theorem rb_blacken_reparent_is_rb_root(tree: RbTree, parent: struct rb_node*) {
    requires is_rb(tree) == 1;
    ensures is_rb_root(rb_reparent(rb_recolor(tree, Color::Black), parent)) == 1 by {
        apply(is_rb_is_almost_rb_insert(tree));
        apply(rb_blacken_root_restores_rb(tree));
        apply(is_rb_root_is_rb(rb_recolor(tree, Color::Black)));
        apply(is_rb_root_root_black(rb_recolor(tree, Color::Black)));
        apply(rb_reparent_preserves_is_rb(rb_recolor(tree, Color::Black), parent));
        apply(rb_reparent_preserves_rb_root_black(rb_recolor(tree, Color::Black), parent));
        unfold(is_rb_root(rb_reparent(rb_recolor(tree, Color::Black), parent)));
        rewrite(is_rb(rb_reparent(rb_recolor(tree, Color::Black), parent)) == is_rb(rb_recolor(tree,
            Color::Black)));
        rewrite(rb_root_black(rb_reparent(rb_recolor(tree, Color::Black), parent)) ==
            rb_root_black(rb_recolor(tree, Color::Black)));
        normalize() using {
            is_rb(rb_recolor(tree, Color::Black)) == 1;
            rb_root_black(rb_recolor(tree, Color::Black)) == 1;
        }
    }
}

theorem rb_erase_root_child_inorder(tree: RbTree) {
    requires rb_left(tree) == RbTree::Empty or rb_right(tree) == RbTree::Empty;
    ensures rb_inorder(rb_erase_root_child(tree))
    == list_append(rb_inorder(rb_left(tree)), rb_inorder(rb_right(tree))) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_erase_root_child(RbTree::Empty));
                unfold(rb_left(RbTree::Empty)); unfold(rb_right(RbTree::Empty));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_append(List<struct rb_node*>::Nil, List<struct rb_node*>::Nil));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_left(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_right(RbTree::Node(node, parent, color, left, right)));
                cases {
                    rb_left(RbTree::Node(node, parent, color, left, right)) == RbTree::Empty => {
                        have left == RbTree::Empty by auto;
                        rewrite(left == RbTree::Empty);
                        unfold(rb_erase_root_child(RbTree::Node(node, parent, color, RbTree::Empty,
                            right)));
                        unfold(rb_left(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                        unfold(rb_right(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                        unfold(rb_inorder(RbTree::Empty));
                        unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(right)));
                        normalize();
                    }
                    rb_right(RbTree::Node(node, parent, color, left, right)) == RbTree::Empty => {
                        have right == RbTree::Empty by auto;
                        rewrite(right == RbTree::Empty);
                        unfold(rb_left(RbTree::Node(node, parent, color, left, RbTree::Empty)));
                        unfold(rb_right(RbTree::Node(node, parent, color, left, RbTree::Empty)));
                        unfold(rb_inorder(RbTree::Empty));
                        apply(list_append_right_identity(rb_inorder(left)));
                        rewrite(list_append(rb_inorder(left), List<struct rb_node*>::Nil) ==
                            rb_inorder(left));
                        apply(rb_erase_root_child_no_right(node, parent, color, left));
                        rewrite(rb_erase_root_child(RbTree::Node(node, parent, color, left, RbTree::Empty))
                            == left);
                        normalize();
                    }
                }
            }
        }
    }
}

theorem rb_erase_root_no_deficit(tree: RbTree) {
    requires is_rb(tree) == 1;
    requires rb_left(tree) == RbTree::Empty or rb_right(tree) == RbTree::Empty;
    ensures is_rb_root(rb_reparent(rb_recolor(rb_erase_root_child(tree), Color::Black), 0)) == 1 by {
        apply(rb_erase_root_child_is_rb(tree));
        apply(rb_blacken_reparent_is_rb_root(rb_erase_root_child(tree), 0));
        assumption();
    }
    ensures rb_inorder(rb_reparent(rb_recolor(rb_erase_root_child(tree), Color::Black), 0))
    == list_append(rb_inorder(rb_left(tree)), rb_inorder(rb_right(tree))) by {
        apply(rb_erase_root_child_inorder(tree));
        apply(rb_recolor_preserves_inorder(rb_erase_root_child(tree), Color::Black));
        apply(rb_reparent_preserves_inorder(rb_recolor(rb_erase_root_child(tree), Color::Black), 0));
        rewrite(rb_inorder(rb_reparent(rb_recolor(rb_erase_root_child(tree), Color::Black), 0)) ==
            rb_inorder(rb_recolor(rb_erase_root_child(tree), Color::Black)));
        rewrite(rb_inorder(rb_recolor(rb_erase_root_child(tree), Color::Black)) ==
            rb_inorder(rb_erase_root_child(tree)));
        assumption();
    }
}
