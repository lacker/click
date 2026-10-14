spec enum Color {
    Red,
    Black,
}

spec enum RbTree {
    Empty,
    Node(struct rb_node*, struct rb_node*, Color, RbTree, RbTree),
}

spec enum Context {
    Top,
    Left(struct rb_node*, struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, struct rb_node*, Color, RbTree, Context),
}

function rb_inorder(tree: RbTree) -> List<struct rb_node*>
    decreases tree
{
    match tree {
        RbTree::Empty => List<struct rb_node*>::Nil,
        RbTree::Node(node, parent, color, left, right) =>
            list_append(rb_inorder(left),
                List<struct rb_node*>::Cons(node, rb_inorder(right))),
    }
}

function rb_member(tree: RbTree, target: struct rb_node*) -> bool
    decreases tree
{
    match tree {
        RbTree::Empty => false,
        RbTree::Node(node, parent, color, left, right) =>
            if node == target {
                true
            } else {
                if rb_member(left, target) {
                    true
                } else {
                    rb_member(right, target)
                }
            },
    }
}

theorem rb_member_is_inorder_membership(tree: RbTree, target: struct rb_node*) {
    ensures rb_member(tree, target) == list_contains(rb_inorder(tree), target) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_member(RbTree::Empty, target));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_contains(List<struct rb_node*>::Nil, target));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(ih(left, target));
                apply(ih(right, target));
                unfold(rb_member(RbTree::Node(node, parent, color, left, right), target));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                apply(list_contains_append(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(right)), target));
                rewrite(list_contains(list_append(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))), target)
                    == if list_contains(rb_inorder(left), target) {
                        true
                    } else {
                        list_contains(List<struct rb_node*>::Cons(node, rb_inorder(right)), target)
                    });
                apply(list_contains_cons(node, rb_inorder(right), target));
                rewrite(list_contains(List<struct rb_node*>::Cons(node, rb_inorder(right)), target)
                    == if node == target {
                        true
                    } else {
                        list_contains(rb_inorder(right), target)
                    });
                rewrite(rb_member(left, target) == list_contains(rb_inorder(left), target));
                rewrite(rb_member(right, target) == list_contains(rb_inorder(right), target));
                if node == target {
                    normalize() using { node == target; }
                } else {
                    normalize() using { not(node == target); }
                }
            }
        }
    }
}

function black_height(tree: RbTree) -> Nat
    decreases tree
{
    match tree {
        RbTree::Empty => Nat::Zero,
        RbTree::Node(node, parent, color, left, right) => match color {
            Color::Red => black_height(left),
            Color::Black => Nat::Succ(black_height(left)),
        },
    }
}

function rb_root_black(tree: RbTree) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) => match color {
            Color::Red => 0,
            Color::Black => 1,
        },
    }
}

function is_rb(tree: RbTree) -> int32
    decreases tree
{
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if is_rb(left) == 1 {
                if is_rb(right) == 1 {
                    if black_height(left) == black_height(right) {
                        match color {
                            Color::Red =>
                                if rb_root_black(left) == 1 {
                                    rb_root_black(right)
                                } else {
                                    0
                                },
                            Color::Black => 1,
                        }
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function rb_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => left,
    }
}

function rb_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => right,
    }
}

function rb_color(tree: RbTree) -> Color {
    match tree {
        RbTree::Empty => Color::Black,
        RbTree::Node(node, parent, color, left, right) => color,
    }
}

function rb_reparent(tree: RbTree, new_parent: struct rb_node*) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            RbTree::Node(node, new_parent, color, left, right),
    }
}

theorem rb_reparent_preserves_inorder(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_inorder(rb_reparent(tree, new_parent)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(rb_inorder(RbTree::Node(node, new_parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_is_rb(tree: RbTree, new_parent: struct rb_node*) {
    ensures is_rb(rb_reparent(tree, new_parent)) == is_rb(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(is_rb(RbTree::Node(node, new_parent, color, left, right)));
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_black_height(tree: RbTree, new_parent: struct rb_node*) {
    ensures black_height(rb_reparent(tree, new_parent)) == black_height(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(black_height(RbTree::Node(node, new_parent, color, left, right)));
                unfold(black_height(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_rb_root_black(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_root_black(rb_reparent(tree, new_parent)) == rb_root_black(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(rb_root_black(RbTree::Node(node, new_parent, color, left, right)));
                unfold(rb_root_black(RbTree::Node(node, parent, color, left, right)));
                normalize();
            }
        }
    }
}

function rb_rotate_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match right {
            RbTree::Empty => tree,
            RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right) =>
                RbTree::Node(pivot, parent, pivot_color,
                    RbTree::Node(node, pivot, color, left, rb_reparent(middle, node)),
                    far_right),
        },
    }
}

function rb_rotate_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => tree,
            RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle) =>
                RbTree::Node(pivot, parent, pivot_color, far_left,
                    RbTree::Node(node, pivot, color, rb_reparent(middle, node), right)),
        },
    }
}

theorem rb_rotate_left_node_preserves_inorder(node: struct rb_node*, parent: struct rb_node*,
                                              color: Color, left: RbTree, right: RbTree) {
    ensures rb_inorder(rb_rotate_left(RbTree::Node(node, parent, color, left, right)))
        == rb_inorder(RbTree::Node(node, parent, color, left, right)) by {
        induct(right) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left, RbTree::Empty)));
                normalize();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right) => {
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right))));
                unfold(rb_inorder(RbTree::Node(pivot, parent, pivot_color,
                    RbTree::Node(node, pivot, color, left, rb_reparent(middle, node)),
                    far_right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right))));
                unfold(rb_inorder(RbTree::Node(node, pivot, color, left,
                    rb_reparent(middle, node))));
                unfold(rb_inorder(RbTree::Node(pivot, pivot_parent, pivot_color,
                    middle, far_right)));
                apply(rb_reparent_preserves_inorder(middle, node));
                rewrite(rb_inorder(rb_reparent(middle, node)) == rb_inorder(middle));
                apply(list_append_associative(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(far_right))));
                rewrite(list_append(list_append(rb_inorder(left),
                    List<struct rb_node*>::Cons(node, rb_inorder(middle))),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(far_right)))
                    == list_append(rb_inorder(left),
                        list_append(List<struct rb_node*>::Cons(node, rb_inorder(middle)),
                            List<struct rb_node*>::Cons(pivot, rb_inorder(far_right)))));
                unfold(list_append(List<struct rb_node*>::Cons(node, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(far_right))));
                normalize();
            }
        }
    }
}

theorem rb_rotate_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_left(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_left_node_preserves_inorder(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

theorem rb_rotate_right_node_preserves_inorder(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree, right: RbTree) {
    ensures rb_inorder(rb_rotate_right(RbTree::Node(node, parent, color, left, right)))
        == rb_inorder(RbTree::Node(node, parent, color, left, right)) by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                normalize();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle) => {
                unfold(rb_rotate_right(RbTree::Node(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right)));
                unfold(rb_inorder(RbTree::Node(pivot, parent, pivot_color, far_left,
                    RbTree::Node(node, pivot, color, rb_reparent(middle, node), right))));
                unfold(rb_inorder(RbTree::Node(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right)));
                unfold(rb_inorder(RbTree::Node(node, pivot, color,
                    rb_reparent(middle, node), right)));
                unfold(rb_inorder(RbTree::Node(pivot, pivot_parent, pivot_color,
                    far_left, middle)));
                apply(rb_reparent_preserves_inorder(middle, node));
                rewrite(rb_inorder(rb_reparent(middle, node)) == rb_inorder(middle));
                apply(list_append_associative(rb_inorder(far_left),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                rewrite(list_append(list_append(rb_inorder(far_left),
                    List<struct rb_node*>::Cons(pivot, rb_inorder(middle))),
                    List<struct rb_node*>::Cons(node, rb_inorder(right)))
                    == list_append(rb_inorder(far_left),
                        list_append(List<struct rb_node*>::Cons(pivot, rb_inorder(middle)),
                            List<struct rb_node*>::Cons(node, rb_inorder(right)))));
                unfold(list_append(List<struct rb_node*>::Cons(pivot, rb_inorder(middle)),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                normalize();
            }
        }
    }
}

theorem rb_rotate_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_right(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_right_node_preserves_inorder(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

function rb_recolor(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, old_color, left, right) =>
            RbTree::Node(node, parent, color, left, right),
    }
}

function rb_recolor_left(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, old_color, left, right) =>
            RbTree::Node(node, parent, old_color, rb_recolor(left, color), right),
    }
}

function rb_recolor_right(tree: RbTree, color: Color) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, old_color, left, right) =>
            RbTree::Node(node, parent, old_color, left, rb_recolor(right, color)),
    }
}

function rb_rotate_left_at_left(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            RbTree::Node(node, parent, color, rb_rotate_left(left), right),
    }
}

function rb_rotate_right_at_right(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) =>
            RbTree::Node(node, parent, color, left, rb_rotate_right(right)),
    }
}

theorem rb_recolor_preserves_inorder(tree: RbTree, color: Color) {
    ensures rb_inorder(rb_recolor(tree, color)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_recolor_left_preserves_inorder(tree: RbTree, color: Color) {
    ensures rb_inorder(rb_recolor_left(tree, color)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor_left(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor_left(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color,
                    rb_recolor(left, color), right)));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left, right)));
                apply(rb_recolor_preserves_inorder(left, color));
                rewrite(rb_inorder(rb_recolor(left, color)) == rb_inorder(left));
                normalize();
            }
        }
    }
}

theorem rb_recolor_right_preserves_inorder(tree: RbTree, color: Color) {
    ensures rb_inorder(rb_recolor_right(tree, color)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor_right(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor_right(RbTree::Node(node, parent, old_color, left, right),
                    color));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left,
                    rb_recolor(right, color))));
                unfold(rb_inorder(RbTree::Node(node, parent, old_color, left, right)));
                apply(rb_recolor_preserves_inorder(right, color));
                rewrite(rb_inorder(rb_recolor(right, color)) == rb_inorder(right));
                normalize();
            }
        }
    }
}

theorem rb_rotate_left_at_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_left_at_left(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left_at_left(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_rotate_left_at_left(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, rb_rotate_left(left), right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                apply(rb_rotate_left_preserves_inorder(left));
                rewrite(rb_inorder(rb_rotate_left(left)) == rb_inorder(left));
                normalize();
            }
        }
    }
}

theorem rb_rotate_right_at_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_rotate_right_at_right(tree)) == rb_inorder(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right_at_right(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_rotate_right_at_right(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left,
                    rb_rotate_right(right))));
                unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
                apply(rb_rotate_right_preserves_inorder(right));
                rewrite(rb_inorder(rb_rotate_right(right)) == rb_inorder(right));
                normalize();
            }
        }
    }
}

theorem black_height_black_node(node: struct rb_node*, parent: struct rb_node*,
                                left: RbTree, right: RbTree) {
    ensures black_height(RbTree::Node(node, parent, Color::Black, left, right))
        == Nat::Succ(black_height(left)) by {
        unfold(black_height(RbTree::Node(node, parent, Color::Black, left, right)));
        normalize();
    }
}

theorem black_height_red_node(node: struct rb_node*, parent: struct rb_node*,
                              left: RbTree, right: RbTree) {
    ensures black_height(RbTree::Node(node, parent, Color::Red, left, right))
        == black_height(left) by {
        unfold(black_height(RbTree::Node(node, parent, Color::Red, left, right)));
        normalize();
    }
}

theorem rb_root_black_black_node(node: struct rb_node*, parent: struct rb_node*,
                                 left: RbTree, right: RbTree) {
    ensures rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by {
        unfold(rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)));
        normalize();
    }
}

theorem rb_root_black_red_node(node: struct rb_node*, parent: struct rb_node*,
                               left: RbTree, right: RbTree) {
    ensures rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) == 0 by {
        unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)));
        normalize();
    }
}

theorem is_rb_black_node(node: struct rb_node*, parent: struct rb_node*,
                         left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);

    ensures is_rb(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by {
        unfold(is_rb(RbTree::Node(node, parent, Color::Black, left, right)));
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
        }
    }
}

theorem is_rb_red_node(node: struct rb_node*, parent: struct rb_node*,
                       left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);
    requires rb_root_black(left) == 1;
    requires rb_root_black(right) == 1;

    ensures is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1 by {
        unfold(is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
        rewrite(rb_root_black(right) == 1);
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
            rb_root_black(left) == 1;
        }
    }
}

theorem is_rb_node_left(node: struct rb_node*, parent: struct rb_node*, color: Color,
                        left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(left) == 1 by {
        if is_rb(left) == 1 {
            assumption();
        } else {
            have is_rb(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize() using { not(is_rb(left) == 1); }
            }
            contradiction(is_rb(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_node_right(node: struct rb_node*, parent: struct rb_node*, color: Color,
                         left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(right) == 1 by {
        if is_rb(right) == 1 {
            assumption();
        } else {
            apply(is_rb_node_left(node, parent, color, left, right));
            have is_rb(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize() using { is_rb(left) == 1; not(is_rb(right) == 1); }
            }
            contradiction(is_rb(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_node_black_heights(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                 left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures black_height(left) == black_height(right) by {
        if black_height(left) == black_height(right) {
            assumption();
        } else {
            apply(is_rb_node_left(node, parent, color, left, right));
            apply(is_rb_node_right(node, parent, color, left, right));
            have is_rb(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, color, left, right)));
                normalize() using {
                    is_rb(left) == 1;
                    is_rb(right) == 1;
                    not(black_height(left) == black_height(right));
                }
            }
            contradiction(is_rb(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_red_node_children_are_black(node: struct rb_node*, parent: struct rb_node*,
                                          left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1;

    ensures rb_root_black(left) == 1 by {
        if rb_root_black(left) == 1 {
            assumption();
        } else {
            apply(is_rb_node_left(node, parent, Color::Red, left, right));
            apply(is_rb_node_right(node, parent, Color::Red, left, right));
            apply(is_rb_node_black_heights(node, parent, Color::Red, left, right));
            have is_rb(RbTree::Node(node, parent, Color::Red, left, right)) != 1 by {
                unfold(is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
                normalize() using {
                    is_rb(left) == 1;
                    is_rb(right) == 1;
                    black_height(left) == black_height(right);
                    not(rb_root_black(left) == 1);
                }
            }
            contradiction(is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1);
        }
    }
}

function is_rb_root(tree: RbTree) -> int32 {
    if is_rb(tree) == 1 {
        rb_root_black(tree)
    } else {
        0
    }
}

function almost_rb_insert(tree: RbTree) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if is_rb(left) == 1 {
                if is_rb(right) == 1 {
                    if black_height(left) == black_height(right) {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function almost_rb_erase(tree: RbTree, required: Nat) -> int32 {
    if is_rb(tree) == 1 {
        if Nat::Succ(black_height(tree)) == required {
            1
        } else {
            0
        }
    } else {
        0
    }
}

theorem almost_rb_insert_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                              left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);

    ensures almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1 by {
        unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
        }
    }
}

theorem almost_rb_insert_node_left(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                   left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(left) == 1 by {
        if is_rb(left) == 1 {
            assumption();
        } else {
            have almost_rb_insert(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
                normalize() using { not(is_rb(left) == 1); }
            }
            contradiction(almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem almost_rb_insert_node_right(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                    left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures is_rb(right) == 1 by {
        if is_rb(right) == 1 {
            assumption();
        } else {
            apply(almost_rb_insert_node_left(node, parent, color, left, right));
            have almost_rb_insert(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
                normalize() using { is_rb(left) == 1; not(is_rb(right) == 1); }
            }
            contradiction(almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem almost_rb_insert_node_black_heights(node: struct rb_node*, parent: struct rb_node*,
                                            color: Color, left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures black_height(left) == black_height(right) by {
        if black_height(left) == black_height(right) {
            assumption();
        } else {
            apply(almost_rb_insert_node_left(node, parent, color, left, right));
            apply(almost_rb_insert_node_right(node, parent, color, left, right));
            have almost_rb_insert(RbTree::Node(node, parent, color, left, right)) != 1 by {
                unfold(almost_rb_insert(RbTree::Node(node, parent, color, left, right)));
                normalize() using {
                    is_rb(left) == 1;
                    is_rb(right) == 1;
                    not(black_height(left) == black_height(right));
                }
            }
            contradiction(almost_rb_insert(RbTree::Node(node, parent, color, left, right)) == 1);
        }
    }
}

theorem is_rb_is_almost_rb_insert(tree: RbTree) {
    requires is_rb(tree) == 1;

    ensures almost_rb_insert(tree) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(almost_rb_insert(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(is_rb_node_left(node, parent, color, left, right));
                apply(is_rb_node_right(node, parent, color, left, right));
                apply(is_rb_node_black_heights(node, parent, color, left, right));
                apply(almost_rb_insert_node(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

theorem almost_rb_insert_black_root_is_rb(node: struct rb_node*, parent: struct rb_node*,
                                          left: RbTree, right: RbTree) {
    requires almost_rb_insert(RbTree::Node(node, parent, Color::Black, left, right)) == 1;

    ensures is_rb(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by {
        apply(almost_rb_insert_node_left(node, parent, Color::Black, left, right));
        apply(almost_rb_insert_node_right(node, parent, Color::Black, left, right));
        apply(almost_rb_insert_node_black_heights(node, parent, Color::Black, left, right));
        apply(is_rb_black_node(node, parent, left, right));
        assumption();
    }
}

theorem rb_blacken_root_restores_rb(tree: RbTree) {
    requires almost_rb_insert(tree) == 1;

    ensures is_rb_root(rb_recolor(tree, Color::Black)) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, Color::Black));
                unfold(is_rb_root(RbTree::Empty));
                unfold(is_rb(RbTree::Empty));
                unfold(rb_root_black(RbTree::Empty));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(almost_rb_insert_node_left(node, parent, color, left, right));
                apply(almost_rb_insert_node_right(node, parent, color, left, right));
                apply(almost_rb_insert_node_black_heights(node, parent, color, left, right));
                apply(is_rb_black_node(node, parent, left, right));
                apply(rb_root_black_black_node(node, parent, left, right));
                unfold(rb_recolor(RbTree::Node(node, parent, color, left, right), Color::Black));
                unfold(is_rb_root(RbTree::Node(node, parent, Color::Black, left, right)));
                rewrite(rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)) == 1);
                normalize() using {
                    is_rb(RbTree::Node(node, parent, Color::Black, left, right)) == 1;
                }
            }
        }
    }
}

theorem almost_rb_erase_node(tree: RbTree, required: Nat) {
    requires is_rb(tree) == 1;
    requires Nat::Succ(black_height(tree)) == required;

    ensures almost_rb_erase(tree, required) == 1 by {
        unfold(almost_rb_erase(tree, required));
        normalize() using {
            is_rb(tree) == 1;
            Nat::Succ(black_height(tree)) == required;
        }
    }
}

theorem almost_rb_erase_is_rb(tree: RbTree, required: Nat) {
    requires almost_rb_erase(tree, required) == 1;

    ensures is_rb(tree) == 1 by {
        if is_rb(tree) == 1 {
            assumption();
        } else {
            have almost_rb_erase(tree, required) != 1 by {
                unfold(almost_rb_erase(tree, required));
                normalize() using { not(is_rb(tree) == 1); }
            }
            contradiction(almost_rb_erase(tree, required) == 1);
        }
    }
}

theorem almost_rb_erase_black_deficit(tree: RbTree, required: Nat) {
    requires almost_rb_erase(tree, required) == 1;

    ensures Nat::Succ(black_height(tree)) == required by {
        if Nat::Succ(black_height(tree)) == required {
            assumption();
        } else {
            apply(almost_rb_erase_is_rb(tree, required));
            have almost_rb_erase(tree, required) != 1 by {
                unfold(almost_rb_erase(tree, required));
                normalize() using {
                    is_rb(tree) == 1;
                    not(Nat::Succ(black_height(tree)) == required);
                }
            }
            contradiction(almost_rb_erase(tree, required) == 1);
        }
    }
}

function rb_insert_fix_recolor(tree: RbTree) -> RbTree {
    rb_recolor(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red)
}

function rb_insert_fix_inner_left(tree: RbTree) -> RbTree {
    rb_rotate_left_at_left(tree)
}

function rb_insert_fix_inner_right(tree: RbTree) -> RbTree {
    rb_rotate_right_at_right(tree)
}

function rb_insert_fix_outer_left(tree: RbTree) -> RbTree {
    rb_recolor(rb_recolor_right(rb_rotate_right(tree), Color::Red), Color::Black)
}

function rb_insert_fix_outer_right(tree: RbTree) -> RbTree {
    rb_recolor(rb_recolor_left(rb_rotate_left(tree), Color::Red), Color::Black)
}


theorem rb_insert_fix_recolor_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_recolor(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_recolor(tree));
        apply(rb_recolor_preserves_inorder(
            rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red));
        rewrite(rb_inorder(rb_recolor(
            rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red))
            == rb_inorder(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black)));
        apply(rb_recolor_left_preserves_inorder(
            rb_recolor_right(tree, Color::Black), Color::Black));
        rewrite(rb_inorder(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black))
            == rb_inorder(rb_recolor_right(tree, Color::Black)));
        apply(rb_recolor_right_preserves_inorder(tree, Color::Black));
        assumption();
    }
}

theorem rb_insert_fix_inner_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_inner_left(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_inner_left(tree));
        apply(rb_rotate_left_at_left_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_inner_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_inner_right(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_inner_right(tree));
        apply(rb_rotate_right_at_right_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_outer_left_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_outer_left(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_outer_left(tree));
        apply(rb_recolor_preserves_inorder(
            rb_recolor_right(rb_rotate_right(tree), Color::Red), Color::Black));
        rewrite(rb_inorder(rb_recolor(
            rb_recolor_right(rb_rotate_right(tree), Color::Red), Color::Black))
            == rb_inorder(rb_recolor_right(rb_rotate_right(tree), Color::Red)));
        apply(rb_recolor_right_preserves_inorder(rb_rotate_right(tree), Color::Red));
        rewrite(rb_inorder(rb_recolor_right(rb_rotate_right(tree), Color::Red))
            == rb_inorder(rb_rotate_right(tree)));
        apply(rb_rotate_right_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_outer_right_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_insert_fix_outer_right(tree)) == rb_inorder(tree) by {
        unfold(rb_insert_fix_outer_right(tree));
        apply(rb_recolor_preserves_inorder(
            rb_recolor_left(rb_rotate_left(tree), Color::Red), Color::Black));
        rewrite(rb_inorder(rb_recolor(
            rb_recolor_left(rb_rotate_left(tree), Color::Red), Color::Black))
            == rb_inorder(rb_recolor_left(rb_rotate_left(tree), Color::Red)));
        apply(rb_recolor_left_preserves_inorder(rb_rotate_left(tree), Color::Red));
        rewrite(rb_inorder(rb_recolor_left(rb_rotate_left(tree), Color::Red))
            == rb_inorder(rb_rotate_left(tree)));
        apply(rb_rotate_left_preserves_inorder(tree));
        assumption();
    }
}

theorem rb_insert_fix_recolor_propagates(grandparent: struct rb_node*,
                                         above: struct rb_node*,
                                         parent: struct rb_node*,
                                         uncle: struct rb_node*,
                                         a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures almost_rb_insert(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d)))) == 1 by {
        unfold(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        unfold(rb_recolor_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d)), Color::Black));
        unfold(rb_recolor(RbTree::Node(uncle, grandparent, Color::Red, c, d), Color::Black));
        unfold(rb_recolor_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d)), Color::Black));
        unfold(rb_recolor(RbTree::Node(parent, grandparent, Color::Red, a, b), Color::Black));
        unfold(rb_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d)), Color::Red));
        apply(is_rb_black_node(parent, grandparent, a, b));
        apply(is_rb_black_node(uncle, grandparent, c, d));
        apply(black_height_black_node(parent, grandparent, a, b));
        apply(black_height_black_node(uncle, grandparent, c, d));
        have black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
            == black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d)) by {
            rewrite(black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
                == Nat::Succ(black_height(a)));
            rewrite(black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d))
                == Nat::Succ(black_height(c)));
            rewrite(black_height(a) == black_height(b));
            rewrite(black_height(b) == black_height(c));
            normalize();
        }
        apply(almost_rb_insert_node(grandparent, above, Color::Red,
            RbTree::Node(parent, grandparent, Color::Black, a, b),
            RbTree::Node(uncle, grandparent, Color::Black, c, d)));
        assumption();
    }
}

theorem rb_insert_fix_outer_left_restores(grandparent: struct rb_node*,
                                          above: struct rb_node*,
                                          parent: struct rb_node*,
                                          cursor: struct rb_node*,
                                          a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b), c),
            d))) == 1 by {
        unfold(rb_insert_fix_outer_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_rotate_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_recolor_right(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Black,
                    rb_reparent(c, grandparent), d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black,
            rb_reparent(c, grandparent), d), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d)), Color::Black));
        apply(rb_reparent_preserves_is_rb(c, grandparent));
        apply(rb_reparent_preserves_black_height(c, grandparent));
        apply(rb_reparent_preserves_rb_root_black(c, grandparent));
        have is_rb(rb_reparent(c, grandparent)) == 1 by auto;
        have rb_root_black(rb_reparent(c, grandparent)) == 1 by auto;
        have black_height(rb_reparent(c, grandparent)) == black_height(d) by auto;
        apply(is_rb_red_node(cursor, parent, a, b));
        apply(is_rb_red_node(grandparent, parent, rb_reparent(c, grandparent), d));
        apply(black_height_red_node(cursor, parent, a, b));
        apply(black_height_red_node(grandparent, parent, rb_reparent(c, grandparent), d));
        have black_height(RbTree::Node(cursor, parent, Color::Red, a, b))
            == black_height(RbTree::Node(grandparent, parent, Color::Red,
                rb_reparent(c, grandparent), d)) by {
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, a, b))
                == black_height(a));
            rewrite(black_height(RbTree::Node(grandparent, parent, Color::Red,
                rb_reparent(c, grandparent), d)) == black_height(rb_reparent(c, grandparent)));
            rewrite(black_height(rb_reparent(c, grandparent)) == black_height(c));
            rewrite(black_height(a) == black_height(b));
            rewrite(black_height(b) == black_height(c));
            normalize();
        }
        apply(is_rb_black_node(parent, above,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)));
        assumption();
    }
}

theorem rb_insert_fix_outer_right_restores(grandparent: struct rb_node*,
                                           above: struct rb_node*,
                                           parent: struct rb_node*,
                                           cursor: struct rb_node*,
                                           a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red, b,
                RbTree::Node(cursor, parent, Color::Red, c, d))))) == 1 by {
        unfold(rb_insert_fix_outer_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_rotate_left(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_recolor_left(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Black, a,
                    rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black, a,
            rb_reparent(b, grandparent)), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Black));
        apply(rb_reparent_preserves_is_rb(b, grandparent));
        apply(rb_reparent_preserves_black_height(b, grandparent));
        apply(rb_reparent_preserves_rb_root_black(b, grandparent));
        have is_rb(rb_reparent(b, grandparent)) == 1 by auto;
        have rb_root_black(rb_reparent(b, grandparent)) == 1 by auto;
        have black_height(a) == black_height(rb_reparent(b, grandparent)) by {
            rewrite(black_height(rb_reparent(b, grandparent)) == black_height(b));
            assumption();
        }
        apply(is_rb_red_node(grandparent, parent, a, rb_reparent(b, grandparent)));
        apply(is_rb_red_node(cursor, parent, c, d));
        apply(black_height_red_node(grandparent, parent, a, rb_reparent(b, grandparent)));
        apply(black_height_red_node(cursor, parent, c, d));
        have black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent)))
            == black_height(RbTree::Node(cursor, parent, Color::Red, c, d)) by {
            rewrite(black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent))) == black_height(a));
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, c, d))
                == black_height(c));
            rewrite(black_height(a) == black_height(b));
            rewrite(black_height(b) == black_height(c));
            normalize();
        }
        apply(is_rb_black_node(parent, above,
            RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)));
        assumption();
    }
}

theorem rb_insert_fix_inner_left_becomes_outer(grandparent: struct rb_node*,
                                               above: struct rb_node*,
                                               parent: struct rb_node*,
                                               cursor: struct rb_node*,
                                               a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_inner_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c)),
            d))
        == RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(cursor, grandparent, Color::Red,
                RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c),
            d) by {
        unfold(rb_insert_fix_inner_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d)));
        unfold(rb_rotate_left_at_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d)));
        unfold(rb_rotate_left(
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c))));
        normalize();
    }
}

theorem rb_insert_fix_inner_right_becomes_outer(grandparent: struct rb_node*,
                                                above: struct rb_node*,
                                                parent: struct rb_node*,
                                                cursor: struct rb_node*,
                                                a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_inner_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d)))
        == RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(cursor, grandparent, Color::Red, b,
                RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) by {
        unfold(rb_insert_fix_inner_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        unfold(rb_rotate_right_at_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        unfold(rb_rotate_right(
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d)));
        normalize();
    }
}

theorem rb_insert_fix_inner_left_restores(grandparent: struct rb_node*,
                                          above: struct rb_node*,
                                          parent: struct rb_node*,
                                          cursor: struct rb_node*,
                                          a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c)),
            d)))) == 1 by {
        apply(rb_insert_fix_inner_left_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        rewrite(rb_insert_fix_inner_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d))
            == RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(cursor, grandparent, Color::Red,
                    RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c),
                d));
        apply(rb_reparent_preserves_is_rb(b, parent));
        apply(rb_reparent_preserves_black_height(b, parent));
        apply(rb_reparent_preserves_rb_root_black(b, parent));
        have is_rb(rb_reparent(b, parent)) == 1 by auto;
        have rb_root_black(rb_reparent(b, parent)) == 1 by auto;
        have black_height(a) == black_height(rb_reparent(b, parent)) by {
            rewrite(black_height(rb_reparent(b, parent)) == black_height(b));
            assumption();
        }
        have black_height(rb_reparent(b, parent)) == black_height(c) by auto;
        apply(rb_insert_fix_outer_left_restores(grandparent, above, cursor, parent,
            a, rb_reparent(b, parent), c, d));
        assumption();
    }
}

theorem rb_insert_fix_inner_right_restores(grandparent: struct rb_node*,
                                           above: struct rb_node*,
                                           parent: struct rb_node*,
                                           cursor: struct rb_node*,
                                           a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    requires is_rb(a) == 1;
    requires is_rb(b) == 1;
    requires is_rb(c) == 1;
    requires is_rb(d) == 1;
    requires rb_root_black(a) == 1;
    requires rb_root_black(b) == 1;
    requires rb_root_black(c) == 1;
    requires rb_root_black(d) == 1;
    requires black_height(a) == black_height(b);
    requires black_height(b) == black_height(c);
    requires black_height(c) == black_height(d);

    ensures is_rb(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d))))) == 1 by {
        apply(rb_insert_fix_inner_right_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        rewrite(rb_insert_fix_inner_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d)))
            == RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(cursor, grandparent, Color::Red, b,
                    RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))));
        apply(rb_reparent_preserves_is_rb(c, parent));
        apply(rb_reparent_preserves_black_height(c, parent));
        apply(rb_reparent_preserves_rb_root_black(c, parent));
        have is_rb(rb_reparent(c, parent)) == 1 by auto;
        have rb_root_black(rb_reparent(c, parent)) == 1 by auto;
        have black_height(b) == black_height(rb_reparent(c, parent)) by {
            rewrite(black_height(rb_reparent(c, parent)) == black_height(c));
            assumption();
        }
        have black_height(rb_reparent(c, parent)) == black_height(d) by auto;
        apply(rb_insert_fix_outer_right_restores(grandparent, above, cursor, parent,
            a, b, rb_reparent(c, parent), d));
        assumption();
    }
}

function list_tail<T>(xs: List<T>) -> List<T> {
    match xs {
        List::Nil => List<T>::Nil,
        List::Cons(head, tail) => tail,
    }
}

theorem list_tail_cons<T>(head: T, tail: List<T>) {
    ensures list_tail(List<T>::Cons(head, tail)) == tail by {
        unfold(list_tail(List<T>::Cons(head, tail)));
        normalize();
    }
}

function rb_min_list(tree: RbTree) -> List<struct rb_node*>
    decreases tree
{
    match tree {
        RbTree::Empty => List<struct rb_node*>::Nil,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => List<struct rb_node*>::Cons(node, List<struct rb_node*>::Nil),
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) =>
                rb_min_list(left),
        },
    }
}

function rb_remove_min(tree: RbTree) -> RbTree
    decreases tree
{
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => rb_reparent(right, parent),
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) =>
                RbTree::Node(node, parent, color, rb_remove_min(left), right),
        },
    }
}

theorem rb_inorder_node_splits(node: struct rb_node*, parent: struct rb_node*, color: Color,
                               left: RbTree, right: RbTree) {
    ensures rb_inorder(RbTree::Node(node, parent, color, left, right))
        == list_append(rb_inorder(left),
            List<struct rb_node*>::Cons(node, rb_inorder(right))) by {
        unfold(rb_inorder(RbTree::Node(node, parent, color, left, right)));
        normalize();
    }
}

theorem rb_erase_no_left_child(erased: struct rb_node*, parent: struct rb_node*, color: Color,
                               right: RbTree) {
    ensures rb_inorder(RbTree::Node(erased, parent, color, RbTree::Empty, right))
        == List<struct rb_node*>::Cons(erased, rb_inorder(right)) by {
        unfold(rb_inorder(RbTree::Node(erased, parent, color, RbTree::Empty, right)));
        unfold(rb_inorder(RbTree::Empty));
        unfold(list_append(List<struct rb_node*>::Nil,
            List<struct rb_node*>::Cons(erased, rb_inorder(right))));
        normalize();
    }
}

theorem rb_erase_no_right_child(erased: struct rb_node*, parent: struct rb_node*, color: Color,
                                left: RbTree) {
    ensures rb_inorder(RbTree::Node(erased, parent, color, left, RbTree::Empty))
        == list_append(rb_inorder(left),
            List<struct rb_node*>::Cons(erased, List<struct rb_node*>::Nil)) by {
        unfold(rb_inorder(RbTree::Node(erased, parent, color, left, RbTree::Empty)));
        unfold(rb_inorder(RbTree::Empty));
        normalize();
    }
}

theorem rb_min_list_splits_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                left: RbTree, right: RbTree) {
    requires rb_inorder(left)
        == list_append(rb_min_list(left), rb_inorder(rb_remove_min(left)));

    ensures rb_inorder(RbTree::Node(node, parent, color, left, right))
        == list_append(rb_min_list(RbTree::Node(node, parent, color, left, right)),
            rb_inorder(rb_remove_min(RbTree::Node(node, parent, color, left, right)))) by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_min_list(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                apply(rb_reparent_preserves_inorder(right, parent));
                rewrite(rb_inorder(rb_reparent(right, parent)) == rb_inorder(right));
                unfold(rb_inorder(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_append(List<struct rb_node*>::Nil,
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                unfold(list_append(List<struct rb_node*>::Cons(node,
                    List<struct rb_node*>::Nil), rb_inorder(right)));
                unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(right)));
                normalize();
            }
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) => {
                unfold(rb_min_list(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                unfold(rb_remove_min(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                unfold(rb_inorder(RbTree::Node(node, parent, color,
                    rb_remove_min(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    right)));
                rewrite(rb_inorder(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right))
                    == list_append(
                        rb_min_list(RbTree::Node(inner_node, inner_parent, inner_color,
                            inner_left, inner_right)),
                        rb_inorder(rb_remove_min(
                            RbTree::Node(inner_node, inner_parent, inner_color,
                                inner_left, inner_right)))));
                apply(list_append_associative(
                    rb_min_list(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    rb_inorder(rb_remove_min(
                        RbTree::Node(inner_node, inner_parent, inner_color,
                            inner_left, inner_right))),
                    List<struct rb_node*>::Cons(node, rb_inorder(right))));
                assumption();
            }
        }
    }
}

theorem rb_min_list_splits_inorder(tree: RbTree) {
    ensures rb_inorder(tree)
        == list_append(rb_min_list(tree), rb_inorder(rb_remove_min(tree))) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_min_list(RbTree::Empty));
                unfold(rb_remove_min(RbTree::Empty));
                unfold(rb_inorder(RbTree::Empty));
                unfold(list_append(List<struct rb_node*>::Nil, List<struct rb_node*>::Nil));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(ih(left));
                apply(rb_min_list_splits_node(node, parent, color, left, right));
                assumption();
            }
        }
    }
}

theorem rb_remove_min_drops_head(tree: RbTree, minimum: struct rb_node*) {
    requires rb_min_list(tree)
        == List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil);

    ensures rb_inorder(tree)
        == List<struct rb_node*>::Cons(minimum, rb_inorder(rb_remove_min(tree))) by {
        apply(rb_min_list_splits_inorder(tree));
        rewrite(rb_inorder(tree)
            == list_append(rb_min_list(tree), rb_inorder(rb_remove_min(tree))));
        rewrite(rb_min_list(tree)
            == List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil));
        unfold(list_append(
            List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil),
            rb_inorder(rb_remove_min(tree))));
        unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(rb_remove_min(tree))));
        normalize();
    }
}

theorem rb_remove_min_is_inorder_tail(tree: RbTree, minimum: struct rb_node*) {
    requires rb_min_list(tree)
        == List<struct rb_node*>::Cons(minimum, List<struct rb_node*>::Nil);

    ensures rb_inorder(rb_remove_min(tree)) == list_tail(rb_inorder(tree)) by {
        apply(rb_remove_min_drops_head(tree, minimum));
        rewrite(rb_inorder(tree)
            == List<struct rb_node*>::Cons(minimum, rb_inorder(rb_remove_min(tree))));
        unfold(list_tail(List<struct rb_node*>::Cons(minimum,
            rb_inorder(rb_remove_min(tree)))));
        normalize();
    }
}

theorem rb_erase_two_child_splice(erased: struct rb_node*, successor: struct rb_node*,
                                  parent: struct rb_node*, color: Color,
                                  left: RbTree, right: RbTree) {
    requires rb_min_list(right)
        == List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil);

    ensures rb_inorder(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor)))
        == list_append(rb_inorder(left), rb_inorder(right)) by {
        unfold(rb_inorder(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor))));
        apply(rb_reparent_preserves_inorder(left, successor));
        rewrite(rb_inorder(rb_reparent(left, successor)) == rb_inorder(left));
        apply(rb_reparent_preserves_inorder(rb_remove_min(right), successor));
        rewrite(rb_inorder(rb_reparent(rb_remove_min(right), successor))
            == rb_inorder(rb_remove_min(right)));
        apply(rb_min_list_splits_inorder(right));
        rewrite(rb_inorder(right)
            == list_append(rb_min_list(right), rb_inorder(rb_remove_min(right))));
        rewrite(rb_min_list(right)
            == List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil));
        unfold(list_append(
            List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil),
            rb_inorder(rb_remove_min(right))));
        unfold(list_append(List<struct rb_node*>::Nil, rb_inorder(rb_remove_min(right))));
        normalize();
    }
}

function rb_node_is(a: struct rb_node*, b: struct rb_node*) -> int32 {
    if a == b { 1 } else { 0 }
}

function rb_parent_is(tree: RbTree, p: struct rb_node*) -> int32 {
    match tree {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if parent == p { 1 } else { 0 },
    }
}

function rb_parent_consistent(t: RbTree, p: struct rb_node*) -> int32
    decreases t
{
    match t {
        RbTree::Empty => 1,
        RbTree::Node(node, parent, color, left, right) =>
            if rb_parent_consistent(left, node) == 1 {
                if rb_parent_consistent(right, node) == 1 {
                    if rb_node_is(parent, p) == 1 { 1 } else { 0 }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

function rb_leaf(node: struct rb_node*, parent: struct rb_node*) -> RbTree {
    RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)
}

theorem rb_node_is_reflexive(a: struct rb_node*) {
    ensures rb_node_is(a, a) == 1 by {
        unfold(rb_node_is(a, a));
        normalize();
    }
}

theorem rb_node_is_equal(a: struct rb_node*, b: struct rb_node*) {
    requires a == b;

    ensures rb_node_is(a, b) == 1 by {
        unfold(rb_node_is(a, b));
        normalize() using { a == b; }
    }
}

theorem rb_node_is_same(a: struct rb_node*, b: struct rb_node*) {
    requires rb_node_is(a, b) == 1;

    ensures a == b by {
        if a == b {
            assumption();
        } else {
            have rb_node_is(a, b) != 1 by {
                unfold(rb_node_is(a, b));
                normalize() using { not(a == b); }
            }
            contradiction(rb_node_is(a, b) == 1);
        }
    }
}

theorem rb_parent_is_node_is(node: struct rb_node*, parent: struct rb_node*, color: Color,
                             left: RbTree, right: RbTree, p: struct rb_node*) {
    ensures rb_parent_is(RbTree::Node(node, parent, color, left, right), p)
        == rb_node_is(parent, p) by {
        unfold(rb_parent_is(RbTree::Node(node, parent, color, left, right), p));
        unfold(rb_node_is(parent, p));
        normalize();
    }
}

theorem rb_reparent_parent_is(tree: RbTree, p: struct rb_node*) {
    ensures rb_parent_is(rb_reparent(tree, p), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, p));
                unfold(rb_parent_is(RbTree::Empty, p));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), p));
                apply(rb_parent_is_node_is(node, p, color, left, right, p));
                apply(rb_node_is_reflexive(p));
                rewrite(rb_parent_is(RbTree::Node(node, p, color, left, right), p)
                    == rb_node_is(p, p));
                assumption();
            }
        }
    }
}

theorem rb_parent_consistent_empty(p: struct rb_node*) {
    ensures rb_parent_consistent(RbTree::Empty, p) == 1 by {
        unfold(rb_parent_consistent(RbTree::Empty, p));
        normalize();
    }
}

theorem rb_parent_consistent_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                  left: RbTree, right: RbTree, p: struct rb_node*) {
    requires rb_node_is(parent, p) == 1;
    requires rb_parent_consistent(left, node) == 1;
    requires rb_parent_consistent(right, node) == 1;

    ensures rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1 by {
        unfold(rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p));
        rewrite(rb_node_is(parent, p) == 1);
        normalize() using {
            rb_parent_consistent(left, node) == 1;
            rb_parent_consistent(right, node) == 1;
        }
    }
}

theorem rb_parent_consistent_node_left(node: struct rb_node*, parent: struct rb_node*,
                                       color: Color, left: RbTree, right: RbTree,
                                       p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(left, node) == 1 by {
        if rb_parent_consistent(left, node) == 1 {
            assumption();
        } else {
            have rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_consistent(
                    RbTree::Node(node, parent, color, left, right), p));
                normalize() using { not(rb_parent_consistent(left, node) == 1); }
            }
            contradiction(rb_parent_consistent(
                RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_parent_consistent_node_right(node: struct rb_node*, parent: struct rb_node*,
                                        color: Color, left: RbTree, right: RbTree,
                                        p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(right, node) == 1 by {
        if rb_parent_consistent(right, node) == 1 {
            assumption();
        } else {
            apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
            have rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_consistent(
                    RbTree::Node(node, parent, color, left, right), p));
                normalize() using {
                    rb_parent_consistent(left, node) == 1;
                    not(rb_parent_consistent(right, node) == 1);
                }
            }
            contradiction(rb_parent_consistent(
                RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_parent_consistent_node_parent(node: struct rb_node*, parent: struct rb_node*,
                                         color: Color, left: RbTree, right: RbTree,
                                         p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_node_is(parent, p) == 1 by {
        if rb_node_is(parent, p) == 1 {
            assumption();
        } else {
            apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
            apply(rb_parent_consistent_node_right(node, parent, color, left, right, p));
            have rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_consistent(
                    RbTree::Node(node, parent, color, left, right), p));
                normalize() using {
                    rb_parent_consistent(left, node) == 1;
                    rb_parent_consistent(right, node) == 1;
                    not(rb_node_is(parent, p) == 1);
                }
            }
            contradiction(rb_parent_consistent(
                RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_reparent_parent_consistent_at(tree: RbTree, p: struct rb_node*,
                                         new_parent: struct rb_node*, q: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;
    requires rb_node_is(new_parent, q) == 1;

    ensures rb_parent_consistent(rb_reparent(tree, new_parent), q) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                apply(rb_parent_consistent_empty(q));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
                apply(rb_parent_consistent_node_right(node, parent, color, left, right, p));
                apply(rb_parent_consistent_node(node, new_parent, color, left, right, q));
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                assumption();
            }
        }
    }
}

theorem rb_reparent_parent_consistent(tree: RbTree, p: struct rb_node*,
                                      new_parent: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_reparent(tree, new_parent), new_parent) == 1 by {
        apply(rb_node_is_reflexive(new_parent));
        apply(rb_reparent_parent_consistent_at(tree, p, new_parent, new_parent));
        assumption();
    }
}

theorem rb_rotate_left_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                              color: Color, left: RbTree, right: RbTree,
                                              p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(
        rb_rotate_left(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(right) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left, RbTree::Empty)));
                assumption();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right), p));
                apply(rb_parent_consistent_node_right(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right), p));
                apply(rb_parent_consistent_node_parent(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right), p));
                apply(rb_parent_consistent_node_left(pivot, pivot_parent, pivot_color,
                    middle, far_right, node));
                apply(rb_parent_consistent_node_right(pivot, pivot_parent, pivot_color,
                    middle, far_right, node));
                apply(rb_reparent_parent_consistent(middle, pivot, node));
                apply(rb_node_is_reflexive(pivot));
                apply(rb_parent_consistent_node(node, pivot, color, left,
                    rb_reparent(middle, node), pivot));
                apply(rb_parent_consistent_node(pivot, parent, pivot_color,
                    RbTree::Node(node, pivot, color, left, rb_reparent(middle, node)),
                    far_right, p));
                unfold(rb_rotate_left(RbTree::Node(node, parent, color, left,
                    RbTree::Node(pivot, pivot_parent, pivot_color, middle, far_right))));
                assumption();
            }
        }
    }
}

theorem rb_rotate_left_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_rotate_left(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_left(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_left_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_rotate_right_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree, right: RbTree,
                                               p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(
        rb_rotate_right(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(left) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                assumption();
            }
            RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle) => {
                apply(rb_parent_consistent_node_left(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right, p));
                apply(rb_parent_consistent_node_right(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right, p));
                apply(rb_parent_consistent_node_left(pivot, pivot_parent, pivot_color,
                    far_left, middle, node));
                apply(rb_parent_consistent_node_right(pivot, pivot_parent, pivot_color,
                    far_left, middle, node));
                apply(rb_reparent_parent_consistent(middle, pivot, node));
                apply(rb_node_is_reflexive(pivot));
                apply(rb_parent_consistent_node(node, pivot, color,
                    rb_reparent(middle, node), right, pivot));
                apply(rb_parent_consistent_node(pivot, parent, pivot_color, far_left,
                    RbTree::Node(node, pivot, color, rb_reparent(middle, node), right), p));
                unfold(rb_rotate_right(RbTree::Node(node, parent, color,
                    RbTree::Node(pivot, pivot_parent, pivot_color, far_left, middle), right)));
                assumption();
            }
        }
    }
}

theorem rb_rotate_right_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_rotate_right(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_rotate_right(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_rotate_right_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_recolor_parent_consistent(tree: RbTree, color: Color, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_recolor(tree, color), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, color));
                assumption();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, old_color, left, right, p));
                apply(rb_parent_consistent_node_right(node, parent, old_color, left, right, p));
                apply(rb_parent_consistent_node_parent(node, parent, old_color, left, right, p));
                apply(rb_parent_consistent_node(node, parent, color, left, right, p));
                unfold(rb_recolor(RbTree::Node(node, parent, old_color, left, right), color));
                assumption();
            }
        }
    }
}

theorem rb_leaf_parent_consistent(node: struct rb_node*, parent: struct rb_node*) {
    ensures rb_parent_consistent(rb_leaf(node, parent), parent) == 1 by {
        apply(rb_parent_consistent_empty(node));
        apply(rb_node_is_reflexive(parent));
        apply(rb_parent_consistent_node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty,
            parent));
        unfold(rb_leaf(node, parent));
        assumption();
    }
}

theorem rb_insert_leaf_left_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                              color: Color, right: RbTree,
                                              fresh: struct rb_node*, p: struct rb_node*) {
    requires rb_parent_consistent(
        RbTree::Node(node, parent, color, RbTree::Empty, right), p) == 1;

    ensures rb_parent_consistent(
        RbTree::Node(node, parent, color, rb_leaf(fresh, node), right), p) == 1 by {
        apply(rb_parent_consistent_node_right(node, parent, color, RbTree::Empty, right, p));
        apply(rb_parent_consistent_node_parent(node, parent, color, RbTree::Empty, right, p));
        apply(rb_leaf_parent_consistent(fresh, node));
        apply(rb_parent_consistent_node(node, parent, color, rb_leaf(fresh, node), right, p));
        assumption();
    }
}

theorem rb_insert_leaf_right_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree,
                                               fresh: struct rb_node*, p: struct rb_node*) {
    requires rb_parent_consistent(
        RbTree::Node(node, parent, color, left, RbTree::Empty), p) == 1;

    ensures rb_parent_consistent(
        RbTree::Node(node, parent, color, left, rb_leaf(fresh, node)), p) == 1 by {
        apply(rb_parent_consistent_node_left(node, parent, color, left, RbTree::Empty, p));
        apply(rb_parent_consistent_node_parent(node, parent, color, left, RbTree::Empty, p));
        apply(rb_leaf_parent_consistent(fresh, node));
        apply(rb_parent_consistent_node(node, parent, color, left, rb_leaf(fresh, node), p));
        assumption();
    }
}

theorem rb_remove_min_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                             color: Color, left: RbTree, right: RbTree,
                                             p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;
    requires rb_parent_consistent(rb_remove_min(left), node) == 1;

    ensures rb_parent_consistent(
        rb_remove_min(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(left) as ih {
            RbTree::Empty => {
                apply(rb_parent_consistent_node_right(node, parent, color, RbTree::Empty,
                    right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color, RbTree::Empty,
                    right, p));
                apply(rb_reparent_parent_consistent_at(right, node, parent, p));
                unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                assumption();
            }
            RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right) => {
                apply(rb_parent_consistent_node_right(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right, p));
                apply(rb_parent_consistent_node(node, parent, color,
                    rb_remove_min(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    right, p));
                unfold(rb_remove_min(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                assumption();
            }
        }
    }
}

theorem rb_remove_min_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_remove_min(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_remove_min(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
                apply(ih(left, node));
                apply(rb_remove_min_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_erase_two_child_splice_parent_consistent(erased: struct rb_node*,
                                                    successor: struct rb_node*,
                                                    parent: struct rb_node*, color: Color,
                                                    left: RbTree, right: RbTree,
                                                    p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(erased, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor)), p) == 1 by {
        apply(rb_parent_consistent_node_left(erased, parent, color, left, right, p));
        apply(rb_parent_consistent_node_right(erased, parent, color, left, right, p));
        apply(rb_parent_consistent_node_parent(erased, parent, color, left, right, p));
        apply(rb_reparent_parent_consistent(left, erased, successor));
        apply(rb_remove_min_parent_consistent(right, erased));
        apply(rb_reparent_parent_consistent(rb_remove_min(right), erased, successor));
        apply(rb_parent_consistent_node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min(right), successor), p));
        assumption();
    }
}

function plug(ctx: Context, sub: RbTree) -> RbTree
    decreases ctx
{
    match ctx {
        Context::Top => sub,
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model)),
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub)),
    }
}

// Join the successor descent spine to the context above the erased node.
function ctx_concat(inner: Context, outer: Context) -> Context
    decreases inner
{
    match inner {
        Context::Top => outer,
        Context::Left(id, parent, color, sibling, up) =>
            Context::Left(id, parent, color, sibling, ctx_concat(up, outer)),
        Context::Right(id, parent, color, sibling, up) =>
            Context::Right(id, parent, color, sibling, ctx_concat(up, outer)),
    }
}

theorem plug_ctx_concat(inner: Context, outer: Context, sub: RbTree) {
    ensures plug(ctx_concat(inner, outer), sub) == plug(outer, plug(inner, sub)) by {
        induct(inner) as ih {
            Context::Top => {
                unfold(ctx_concat(Context::Top, outer));
                unfold(plug(Context::Top, sub));
                normalize();
            }
            Context::Left(id, parent, color, sibling, up) => {
                apply(ih(up, outer, RbTree::Node(id, parent, color, sub, sibling)));
                unfold(ctx_concat(Context::Left(id, parent, color, sibling, up), outer));
                unfold(plug(Context::Left(id, parent, color, sibling, ctx_concat(up, outer)), sub));
                unfold(plug(Context::Left(id, parent, color, sibling, up), sub));
                assumption();
            }
            Context::Right(id, parent, color, sibling, up) => {
                apply(ih(up, outer, RbTree::Node(id, parent, color, sibling, sub)));
                unfold(ctx_concat(Context::Right(id, parent, color, sibling, up), outer));
                unfold(plug(Context::Right(id, parent, color, sibling, ctx_concat(up, outer)), sub));
                unfold(plug(Context::Right(id, parent, color, sibling, up), sub));
                assumption();
            }
        }
    }
}

function ctx_consistent(ctx: Context, sub: RbTree, root_parent: struct rb_node*) -> int32
    decreases ctx
{
    match ctx {
        Context::Top => if rb_parent_consistent(sub, root_parent) == 1 { 1 } else { 0 },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if rb_parent_consistent(sub, identity) == 1 {
                if rb_parent_consistent(sibling_model, identity) == 1 {
                    if ctx_consistent(up_model,
                            RbTree::Node(identity, grandparent, color, sub, sibling_model),
                            root_parent) == 1 {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if rb_parent_consistent(sub, identity) == 1 {
                if rb_parent_consistent(sibling_model, identity) == 1 {
                    if ctx_consistent(up_model,
                            RbTree::Node(identity, grandparent, color, sibling_model, sub),
                            root_parent) == 1 {
                        1
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

theorem plug_inorder_transport(ctx: Context, a: RbTree, b: RbTree) {
    requires rb_inorder(a) == rb_inorder(b);

    ensures rb_inorder(plug(ctx, a)) == rb_inorder(plug(ctx, b)) by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, a));
                unfold(plug(Context::Top, b));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have rb_inorder(RbTree::Node(identity, grandparent, color, a, sibling_model))
                    == rb_inorder(RbTree::Node(identity, grandparent, color, b, sibling_model)) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, a, sibling_model)));
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, b, sibling_model)));
                    rewrite(rb_inorder(a) == rb_inorder(b));
                    normalize();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, a, sibling_model),
                    RbTree::Node(identity, grandparent, color, b, sibling_model)));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    a));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    b));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, a))
                    == rb_inorder(RbTree::Node(identity, grandparent, color, sibling_model, b)) by {
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sibling_model, a)));
                    unfold(rb_inorder(
                        RbTree::Node(identity, grandparent, color, sibling_model, b)));
                    rewrite(rb_inorder(a) == rb_inorder(b));
                    normalize();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, a),
                    RbTree::Node(identity, grandparent, color, sibling_model, b)));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    a));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    b));
                assumption();
            }
        }
    }
}

theorem ctx_consistent_top(sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(Context::Top, sub, root_parent) == 1;

    ensures rb_parent_consistent(sub, root_parent) == 1 by {
        if rb_parent_consistent(sub, root_parent) == 1 {
            assumption();
        } else {
            have ctx_consistent(Context::Top, sub, root_parent) != 1 by {
                unfold(ctx_consistent(Context::Top, sub, root_parent));
                normalize() using { not(rb_parent_consistent(sub, root_parent) == 1); }
            }
            contradiction(ctx_consistent(Context::Top, sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_top_frame(sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(sub, root_parent) == 1;

    ensures ctx_consistent(Context::Top, sub, root_parent) == 1 by {
        unfold(ctx_consistent(Context::Top, sub, root_parent));
        normalize() using { rb_parent_consistent(sub, root_parent) == 1; }
    }
}

theorem ctx_consistent_left_focus(identity: struct rb_node*, grandparent: struct rb_node*,
                                  color: Color, sibling_model: RbTree, up_model: Context,
                                  sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sub, identity) == 1 by {
        if rb_parent_consistent(sub, identity) == 1 {
            assumption();
        } else {
            have ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using { not(rb_parent_consistent(sub, identity) == 1); }
            }
            contradiction(ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_left_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                                    color: Color, sibling_model: RbTree, up_model: Context,
                                    sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sibling_model, identity) == 1 by {
        if rb_parent_consistent(sibling_model, identity) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    not(rb_parent_consistent(sibling_model, identity) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_left_up(identity: struct rb_node*, grandparent: struct rb_node*,
                               color: Color, sibling_model: RbTree, up_model: Context,
                               sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sub, sibling_model), root_parent) == 1 by {
        if ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sub, sibling_model),
                root_parent) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            apply(ctx_consistent_left_sibling(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    rb_parent_consistent(sibling_model, identity) == 1;
                    not(ctx_consistent(up_model,
                        RbTree::Node(identity, grandparent, color, sub, sibling_model),
                        root_parent) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_left_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                                  color: Color, sibling_model: RbTree, up_model: Context,
                                  sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(sub, identity) == 1;
    requires rb_parent_consistent(sibling_model, identity) == 1;
    requires ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sub, sibling_model), root_parent) == 1;

    ensures ctx_consistent(
        Context::Left(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1 by {
        unfold(ctx_consistent(
            Context::Left(identity, grandparent, color, sibling_model, up_model),
            sub, root_parent));
        normalize() using {
            rb_parent_consistent(sub, identity) == 1;
            rb_parent_consistent(sibling_model, identity) == 1;
            ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sub, sibling_model),
                root_parent) == 1;
        }
    }
}

theorem ctx_consistent_right_focus(identity: struct rb_node*, grandparent: struct rb_node*,
                                   color: Color, sibling_model: RbTree, up_model: Context,
                                   sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sub, identity) == 1 by {
        if rb_parent_consistent(sub, identity) == 1 {
            assumption();
        } else {
            have ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using { not(rb_parent_consistent(sub, identity) == 1); }
            }
            contradiction(ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_right_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                                     color: Color, sibling_model: RbTree, up_model: Context,
                                     sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures rb_parent_consistent(sibling_model, identity) == 1 by {
        if rb_parent_consistent(sibling_model, identity) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    not(rb_parent_consistent(sibling_model, identity) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_right_up(identity: struct rb_node*, grandparent: struct rb_node*,
                                color: Color, sibling_model: RbTree, up_model: Context,
                                sub: RbTree, root_parent: struct rb_node*) {
    requires ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1;

    ensures ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sibling_model, sub), root_parent) == 1 by {
        if ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sibling_model, sub),
                root_parent) == 1 {
            assumption();
        } else {
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            apply(ctx_consistent_right_sibling(identity, grandparent, color, sibling_model,
                up_model, sub, root_parent));
            have ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) != 1 by {
                unfold(ctx_consistent(
                    Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub, root_parent));
                normalize() using {
                    rb_parent_consistent(sub, identity) == 1;
                    rb_parent_consistent(sibling_model, identity) == 1;
                    not(ctx_consistent(up_model,
                        RbTree::Node(identity, grandparent, color, sibling_model, sub),
                        root_parent) == 1);
                }
            }
            contradiction(ctx_consistent(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                sub, root_parent) == 1);
        }
    }
}

theorem ctx_consistent_right_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                                   color: Color, sibling_model: RbTree, up_model: Context,
                                   sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(sub, identity) == 1;
    requires rb_parent_consistent(sibling_model, identity) == 1;
    requires ctx_consistent(up_model,
        RbTree::Node(identity, grandparent, color, sibling_model, sub), root_parent) == 1;

    ensures ctx_consistent(
        Context::Right(identity, grandparent, color, sibling_model, up_model),
        sub, root_parent) == 1 by {
        unfold(ctx_consistent(
            Context::Right(identity, grandparent, color, sibling_model, up_model),
            sub, root_parent));
        normalize() using {
            rb_parent_consistent(sub, identity) == 1;
            rb_parent_consistent(sibling_model, identity) == 1;
            ctx_consistent(up_model,
                RbTree::Node(identity, grandparent, color, sibling_model, sub),
                root_parent) == 1;
        }
    }
}

theorem plug_parent_consistent_transport(ctx: Context, sub: RbTree,
                                         root_parent: struct rb_node*) {
    requires ctx_consistent(ctx, sub, root_parent) == 1;

    ensures rb_parent_consistent(plug(ctx, sub), root_parent) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(sub, root_parent));
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_consistent_left_up(identity, grandparent, color, sibling_model,
                    up_model, sub, root_parent));
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sub, sibling_model),
                    root_parent));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_consistent_right_up(identity, grandparent, color, sibling_model,
                    up_model, sub, root_parent));
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, sub),
                    root_parent));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub));
                assumption();
            }
        }
    }
}

theorem ctx_consistent_node_children(ctx: Context, node: struct rb_node*,
                                     parent: struct rb_node*, color: Color,
                                     left: RbTree, right: RbTree,
                                     root_parent: struct rb_node*) {
    requires ctx_consistent(ctx, RbTree::Node(node, parent, color, left, right),
        root_parent) == 1;

    ensures rb_parent_consistent(left, node) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(RbTree::Node(node, parent, color, left, right),
                    root_parent));
                apply(rb_parent_consistent_node_left(node, parent, color, left, right,
                    root_parent));
                assumption();
            }
            Context::Left(identity, grandparent, fcolor, sibling_model, up_model) => {
                apply(ctx_consistent_left_focus(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(rb_parent_consistent_node_left(node, parent, color, left, right,
                    identity));
                assumption();
            }
            Context::Right(identity, grandparent, fcolor, sibling_model, up_model) => {
                apply(ctx_consistent_right_focus(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(rb_parent_consistent_node_left(node, parent, color, left, right,
                    identity));
                assumption();
            }
        }
    }

    ensures rb_parent_consistent(right, node) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(RbTree::Node(node, parent, color, left, right),
                    root_parent));
                apply(rb_parent_consistent_node_right(node, parent, color, left, right,
                    root_parent));
                assumption();
            }
            Context::Left(identity, grandparent, fcolor, sibling_model, up_model) => {
                apply(ctx_consistent_left_focus(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(rb_parent_consistent_node_right(node, parent, color, left, right,
                    identity));
                assumption();
            }
            Context::Right(identity, grandparent, fcolor, sibling_model, up_model) => {
                apply(ctx_consistent_right_focus(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(rb_parent_consistent_node_right(node, parent, color, left, right,
                    identity));
                assumption();
            }
        }
    }
}

theorem plug_parent_consistent_ctx(ctx: Context, sub: RbTree, root_parent: struct rb_node*) {
    requires rb_parent_consistent(plug(ctx, sub), root_parent) == 1;

    ensures ctx_consistent(ctx, sub, root_parent) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, sub));
                have rb_parent_consistent(sub, root_parent) == 1 by {
                    rewrite(sub == plug(Context::Top, sub));
                    assumption();
                }
                apply(ctx_consistent_top_frame(sub, root_parent));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub));
                have rb_parent_consistent(plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model)), root_parent) == 1 by {
                    rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model))
                        == plug(Context::Left(identity, grandparent, color, sibling_model,
                            up_model), sub));
                    assumption();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sub, sibling_model),
                    root_parent));
                apply(ctx_consistent_node_children(up_model, identity, grandparent, color,
                    sub, sibling_model, root_parent));
                apply(ctx_consistent_left_frame(identity, grandparent, color, sibling_model,
                    up_model, sub, root_parent));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    sub));
                have rb_parent_consistent(plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub)), root_parent) == 1 by {
                    rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub))
                        == plug(Context::Right(identity, grandparent, color, sibling_model,
                            up_model), sub));
                    assumption();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, sub),
                    root_parent));
                apply(ctx_consistent_node_children(up_model, identity, grandparent, color,
                    sibling_model, sub, root_parent));
                apply(ctx_consistent_right_frame(identity, grandparent, color, sibling_model,
                    up_model, sub, root_parent));
                assumption();
            }
        }
    }
}

theorem rb_parent_consistent_node_fixes_parent(node: struct rb_node*, parent: struct rb_node*,
                                               color: Color, left: RbTree, right: RbTree,
                                               p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures parent == p by {
        apply(rb_parent_consistent_node_parent(node, parent, color, left, right, p));
        apply(rb_node_is_same(parent, p));
        assumption();
    }
}

theorem rb_parent_consistent_same(t: RbTree, a: struct rb_node*, b: struct rb_node*) {
    requires rb_parent_consistent(t, a) == 1;
    requires a == b;

    ensures rb_parent_consistent(t, b) == 1 by {
        induct(t) as ih {
            RbTree::Empty => {
                apply(rb_parent_consistent_empty(b));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left, right, a));
                apply(rb_parent_consistent_node_right(node, parent, color, left, right, a));
                apply(rb_parent_consistent_node_parent(node, parent, color, left, right, a));
                apply(rb_node_is_same(parent, a));
                have parent == b by auto;
                apply(rb_node_is_equal(parent, b));
                apply(rb_parent_consistent_node(node, parent, color, left, right, b));
                assumption();
            }
        }
    }
}

theorem ctx_consistent_swap(ctx: Context, node: struct rb_node*, parent: struct rb_node*,
                            color: Color, left: RbTree, right: RbTree, other: RbTree,
                            root_parent: struct rb_node*) {
    requires ctx_consistent(ctx, RbTree::Node(node, parent, color, left, right),
        root_parent) == 1;
    requires rb_parent_consistent(other, parent) == 1;

    ensures ctx_consistent(ctx, other, root_parent) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_consistent_top(RbTree::Node(node, parent, color, left, right),
                    root_parent));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right,
                    root_parent));
                have rb_parent_consistent(other, root_parent) == 1 by auto;
                apply(ctx_consistent_top_frame(other, root_parent));
                assumption();
            }
            Context::Left(identity, grandparent, fcolor, sibling_model, up_model) => {
                apply(ctx_consistent_left_focus(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(ctx_consistent_left_sibling(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(ctx_consistent_left_up(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right,
                    identity));
                have rb_parent_consistent(other, identity) == 1 by auto;
                apply(rb_node_is_reflexive(grandparent));
                apply(rb_parent_consistent_node(identity, grandparent, fcolor, other,
                    sibling_model, grandparent));
                apply(ih(up_model, identity, grandparent, fcolor,
                    RbTree::Node(node, parent, color, left, right), sibling_model,
                    RbTree::Node(identity, grandparent, fcolor, other, sibling_model),
                    root_parent));
                apply(ctx_consistent_left_frame(identity, grandparent, fcolor, sibling_model,
                    up_model, other, root_parent));
                assumption();
            }
            Context::Right(identity, grandparent, fcolor, sibling_model, up_model) => {
                apply(ctx_consistent_right_focus(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(ctx_consistent_right_sibling(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(ctx_consistent_right_up(identity, grandparent, fcolor, sibling_model,
                    up_model, RbTree::Node(node, parent, color, left, right), root_parent));
                apply(rb_parent_consistent_node_fixes_parent(node, parent, color, left, right,
                    identity));
                have rb_parent_consistent(other, identity) == 1 by auto;
                apply(rb_node_is_reflexive(grandparent));
                apply(rb_parent_consistent_node(identity, grandparent, fcolor, sibling_model,
                    other, grandparent));
                apply(ih(up_model, identity, grandparent, fcolor, sibling_model,
                    RbTree::Node(node, parent, color, left, right),
                    RbTree::Node(identity, grandparent, fcolor, sibling_model, other),
                    root_parent));
                apply(ctx_consistent_right_frame(identity, grandparent, fcolor, sibling_model,
                    up_model, other, root_parent));
                assumption();
            }
        }
    }
}

function color_black(color: Color) -> int32 {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

function frame_black_height(color: Color, bh: Nat) -> Nat {
    match color {
        Color::Red => bh,
        Color::Black => Nat::Succ(bh),
    }
}

function node_color_ok(color: Color, left_color: Color, right_color: Color) -> int32 {
    match color {
        Color::Red =>
            if color_black(left_color) == 1 {
                if color_black(right_color) == 1 {
                    1
                } else {
                    0
                }
            } else {
                0
            },
        Color::Black => 1,
    }
}

theorem color_black_red() {
    ensures color_black(Color::Red) == 0 by {
        unfold(color_black(Color::Red));
        normalize();
    }
}

theorem color_black_black() {
    ensures color_black(Color::Black) == 1 by {
        unfold(color_black(Color::Black));
        normalize();
    }
}

theorem frame_black_height_red(bh: Nat) {
    ensures frame_black_height(Color::Red, bh) == bh by {
        unfold(frame_black_height(Color::Red, bh));
        normalize();
    }
}

theorem frame_black_height_black(bh: Nat) {
    ensures frame_black_height(Color::Black, bh) == Nat::Succ(bh) by {
        unfold(frame_black_height(Color::Black, bh));
        normalize();
    }
}

theorem rb_root_black_is_color_black(tree: RbTree) {
    ensures rb_root_black(tree) == color_black(rb_color(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_root_black(RbTree::Empty));
                unfold(rb_color(RbTree::Empty));
                unfold(color_black(Color::Black));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_root_black(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
                unfold(color_black(color));
                normalize();
            }
        }
    }
}

theorem color_black_of_rb_color(tree: RbTree) {
    ensures color_black(rb_color(tree)) == rb_root_black(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_root_black(RbTree::Empty));
                unfold(rb_color(RbTree::Empty));
                unfold(color_black(Color::Black));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_root_black(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
                unfold(color_black(color));
                normalize();
            }
        }
    }
}

theorem black_height_node_frame(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                left: RbTree, right: RbTree) {
    ensures black_height(RbTree::Node(node, parent, color, left, right))
        == frame_black_height(color, black_height(left)) by {
        unfold(black_height(RbTree::Node(node, parent, color, left, right)));
        unfold(frame_black_height(color, black_height(left)));
        normalize();
    }
}

theorem rb_color_node(node: struct rb_node*, parent: struct rb_node*, color: Color,
                      left: RbTree, right: RbTree) {
    ensures rb_color(RbTree::Node(node, parent, color, left, right)) == color by {
        unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
        normalize();
    }
}

theorem node_color_ok_black(left_color: Color, right_color: Color) {
    ensures node_color_ok(Color::Black, left_color, right_color) == 1 by {
        unfold(node_color_ok(Color::Black, left_color, right_color));
        normalize();
    }
}

theorem node_color_ok_red(left_color: Color, right_color: Color) {
    requires color_black(left_color) == 1;
    requires color_black(right_color) == 1;

    ensures node_color_ok(Color::Red, left_color, right_color) == 1 by {
        unfold(node_color_ok(Color::Red, left_color, right_color));
        normalize() using {
            color_black(left_color) == 1;
            color_black(right_color) == 1;
        }
    }
}

theorem node_color_ok_red_left(left_color: Color, right_color: Color) {
    requires node_color_ok(Color::Red, left_color, right_color) == 1;

    ensures color_black(left_color) == 1 by {
        if color_black(left_color) == 1 {
            assumption();
        } else {
            have node_color_ok(Color::Red, left_color, right_color) != 1 by {
                unfold(node_color_ok(Color::Red, left_color, right_color));
                normalize() using { not(color_black(left_color) == 1); }
            }
            contradiction(node_color_ok(Color::Red, left_color, right_color) == 1);
        }
    }
}

theorem node_color_ok_red_right(left_color: Color, right_color: Color) {
    requires node_color_ok(Color::Red, left_color, right_color) == 1;

    ensures color_black(right_color) == 1 by {
        if color_black(right_color) == 1 {
            assumption();
        } else {
            apply(node_color_ok_red_left(left_color, right_color));
            have node_color_ok(Color::Red, left_color, right_color) != 1 by {
                unfold(node_color_ok(Color::Red, left_color, right_color));
                normalize() using {
                    color_black(left_color) == 1;
                    not(color_black(right_color) == 1);
                }
            }
            contradiction(node_color_ok(Color::Red, left_color, right_color) == 1);
        }
    }
}

theorem is_rb_red_node_value(node: struct rb_node*, parent: struct rb_node*,
                             left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);
    requires rb_root_black(left) == 1;

    ensures rb_root_black(right)
        == is_rb(RbTree::Node(node, parent, Color::Red, left, right)) by {
        unfold(is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
        normalize() using {
            is_rb(left) == 1;
            is_rb(right) == 1;
            black_height(left) == black_height(right);
            rb_root_black(left) == 1;
        }
    }
}

theorem is_rb_red_node_right_child_is_black(node: struct rb_node*, parent: struct rb_node*,
                                            left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, Color::Red, left, right)) == 1;

    ensures rb_root_black(right) == 1 by {
        apply(is_rb_node_left(node, parent, Color::Red, left, right));
        apply(is_rb_node_right(node, parent, Color::Red, left, right));
        apply(is_rb_node_black_heights(node, parent, Color::Red, left, right));
        apply(is_rb_red_node_children_are_black(node, parent, left, right));
        apply(is_rb_red_node_value(node, parent, left, right));
        rewrite(rb_root_black(right)
            == is_rb(RbTree::Node(node, parent, Color::Red, left, right)));
        assumption();
    }
}

theorem is_rb_node_from_parts(node: struct rb_node*, parent: struct rb_node*, color: Color,
                              left: RbTree, right: RbTree) {
    requires is_rb(left) == 1;
    requires is_rb(right) == 1;
    requires black_height(left) == black_height(right);
    requires node_color_ok(color, rb_color(left), rb_color(right)) == 1;

    ensures is_rb(RbTree::Node(node, parent, color, left, right)) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(is_rb_black_node(node, parent, left, right));
                assumption();
            }
            Color::Red => {
                apply(node_color_ok_red_left(rb_color(left), rb_color(right)));
                apply(node_color_ok_red_right(rb_color(left), rb_color(right)));
                apply(rb_root_black_is_color_black(left));
                apply(rb_root_black_is_color_black(right));
                have rb_root_black(left) == 1 by auto;
                have rb_root_black(right) == 1 by auto;
                apply(is_rb_red_node(node, parent, left, right));
                assumption();
            }
        }
    }
}

theorem is_rb_node_colors(node: struct rb_node*, parent: struct rb_node*, color: Color,
                          left: RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures node_color_ok(color, rb_color(left), rb_color(right)) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(node_color_ok_black(rb_color(left), rb_color(right)));
                assumption();
            }
            Color::Red => {
                apply(is_rb_red_node_children_are_black(node, parent, left, right));
                apply(is_rb_red_node_right_child_is_black(node, parent, left, right));
                apply(color_black_of_rb_color(left));
                apply(color_black_of_rb_color(right));
                have color_black(rb_color(left)) == 1 by auto;
                have color_black(rb_color(right)) == 1 by auto;
                apply(node_color_ok_red(rb_color(left), rb_color(right)));
                assumption();
            }
        }
    }
}

theorem is_rb_root_from_parts(tree: RbTree) {
    requires is_rb(tree) == 1;
    requires rb_root_black(tree) == 1;

    ensures is_rb_root(tree) == 1 by {
        unfold(is_rb_root(tree));
        rewrite(rb_root_black(tree) == 1);
        normalize() using { is_rb(tree) == 1; }
    }
}

function ctx_rb(ctx: Context, bh: Nat, focus_color: Color) -> int32
    decreases ctx
{
    match ctx {
        Context::Top =>
            if color_black(focus_color) == 1 {
                1
            } else {
                0
            },
        Context::Left(identity, grandparent, color, sibling_model, up_model) =>
            if is_rb(sibling_model) == 1 {
                if bh == black_height(sibling_model) {
                    if node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 {
                        ctx_rb(up_model, frame_black_height(color, bh), color)
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
        Context::Right(identity, grandparent, color, sibling_model, up_model) =>
            if is_rb(sibling_model) == 1 {
                if black_height(sibling_model) == bh {
                    if node_color_ok(color, rb_color(sibling_model), focus_color) == 1 {
                        ctx_rb(up_model, frame_black_height(color, bh), color)
                    } else {
                        0
                    }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

theorem ctx_rb_top(bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Top, bh, focus_color) == 1;

    ensures color_black(focus_color) == 1 by {
        if color_black(focus_color) == 1 {
            assumption();
        } else {
            have ctx_rb(Context::Top, bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Top, bh, focus_color));
                normalize() using { not(color_black(focus_color) == 1); }
            }
            contradiction(ctx_rb(Context::Top, bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_top_frame(bh: Nat, focus_color: Color) {
    requires color_black(focus_color) == 1;

    ensures ctx_rb(Context::Top, bh, focus_color) == 1 by {
        unfold(ctx_rb(Context::Top, bh, focus_color));
        normalize() using { color_black(focus_color) == 1; }
    }
}

theorem ctx_rb_left_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                            color: Color, sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures is_rb(sibling_model) == 1 by {
        if is_rb(sibling_model) == 1 {
            assumption();
        } else {
            have ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using { not(is_rb(sibling_model) == 1); }
            }
            contradiction(ctx_rb(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_left_height(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures bh == black_height(sibling_model) by {
        if bh == black_height(sibling_model) {
            assumption();
        } else {
            apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    not(bh == black_height(sibling_model));
                }
            }
            contradiction(ctx_rb(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_left_colors(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 by {
        if node_color_ok(color, focus_color, rb_color(sibling_model)) == 1 {
            assumption();
        } else {
            apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    bh == black_height(sibling_model);
                    not(node_color_ok(color, focus_color, rb_color(sibling_model)) == 1);
                }
            }
            contradiction(ctx_rb(
                Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_left_value(identity: struct rb_node*, grandparent: struct rb_node*,
                          color: Color, sibling_model: RbTree, up_model: Context,
                          bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires bh == black_height(sibling_model);
    requires node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color)
        == ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color) by {
        unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        normalize() using {
            is_rb(sibling_model) == 1;
            bh == black_height(sibling_model);
            node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;
        }
    }
}

theorem ctx_rb_left_up(identity: struct rb_node*, grandparent: struct rb_node*,
                       color: Color, sibling_model: RbTree, up_model: Context,
                       bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color) == 1 by {
        apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_value(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color)
            == ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_left_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                          color: Color, sibling_model: RbTree, up_model: Context,
                          bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires bh == black_height(sibling_model);
    requires node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;
    requires ctx_rb(up_model, frame_black_height(color, bh), color) == 1;

    ensures ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1 by {
        unfold(ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color) == 1);
        normalize() using {
            is_rb(sibling_model) == 1;
            bh == black_height(sibling_model);
            node_color_ok(color, focus_color, rb_color(sibling_model)) == 1;
        }
    }
}

theorem ctx_rb_right_sibling(identity: struct rb_node*, grandparent: struct rb_node*,
                             color: Color, sibling_model: RbTree, up_model: Context,
                             bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures is_rb(sibling_model) == 1 by {
        if is_rb(sibling_model) == 1 {
            assumption();
        } else {
            have ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using { not(is_rb(sibling_model) == 1); }
            }
            contradiction(ctx_rb(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_right_height(identity: struct rb_node*, grandparent: struct rb_node*,
                            color: Color, sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures black_height(sibling_model) == bh by {
        if black_height(sibling_model) == bh {
            assumption();
        } else {
            apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    not(black_height(sibling_model) == bh);
                }
            }
            contradiction(ctx_rb(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_right_colors(identity: struct rb_node*, grandparent: struct rb_node*,
                            color: Color, sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures node_color_ok(color, rb_color(sibling_model), focus_color) == 1 by {
        if node_color_ok(color, rb_color(sibling_model), focus_color) == 1 {
            assumption();
        } else {
            apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
                bh, focus_color));
            have ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) != 1 by {
                unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), bh, focus_color));
                normalize() using {
                    is_rb(sibling_model) == 1;
                    black_height(sibling_model) == bh;
                    not(node_color_ok(color, rb_color(sibling_model), focus_color) == 1);
                }
            }
            contradiction(ctx_rb(
                Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color) == 1);
        }
    }
}

theorem ctx_rb_right_value(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires black_height(sibling_model) == bh;
    requires node_color_ok(color, rb_color(sibling_model), focus_color) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color)
        == ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color) by {
        unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        normalize() using {
            is_rb(sibling_model) == 1;
            black_height(sibling_model) == bh;
            node_color_ok(color, rb_color(sibling_model), focus_color) == 1;
        }
    }
}

theorem ctx_rb_right_up(identity: struct rb_node*, grandparent: struct rb_node*,
                        color: Color, sibling_model: RbTree, up_model: Context,
                        bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, frame_black_height(color, bh), color) == 1 by {
        apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_value(identity, grandparent, color, sibling_model, up_model,
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color)
            == ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_right_frame(identity: struct rb_node*, grandparent: struct rb_node*,
                           color: Color, sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires is_rb(sibling_model) == 1;
    requires black_height(sibling_model) == bh;
    requires node_color_ok(color, rb_color(sibling_model), focus_color) == 1;
    requires ctx_rb(up_model, frame_black_height(color, bh), color) == 1;

    ensures ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, focus_color) == 1 by {
        unfold(ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
            bh, focus_color));
        rewrite(ctx_rb(up_model, frame_black_height(color, bh), color) == 1);
        normalize() using {
            is_rb(sibling_model) == 1;
            black_height(sibling_model) == bh;
            node_color_ok(color, rb_color(sibling_model), focus_color) == 1;
        }
    }
}

// A valid context fragment ending at a subtree boundary, not the tree root.
// The boundary can be red. Only the outer ctx_rb imposes root blackness.
function ctx_rb_between(ctx: Context, bh: Nat, focus_color: Color,
                       boundary_bh: Nat, boundary_color: Color) -> int32
    decreases ctx
{
    match ctx {
        Context::Top =>
            if bh == boundary_bh {
                if focus_color == boundary_color { 1 } else { 0 }
            } else { 0 },
        Context::Left(id, parent, color, sibling, up) =>
            if is_rb(sibling) == 1 {
                if bh == black_height(sibling) {
                    if node_color_ok(color, focus_color, rb_color(sibling)) == 1 {
                        ctx_rb_between(up, frame_black_height(color, bh), color,
                            boundary_bh, boundary_color)
                    } else { 0 }
                } else { 0 }
            } else { 0 },
        Context::Right(id, parent, color, sibling, up) =>
            if is_rb(sibling) == 1 {
                if black_height(sibling) == bh {
                    if node_color_ok(color, rb_color(sibling), focus_color) == 1 {
                        ctx_rb_between(up, frame_black_height(color, bh), color,
                            boundary_bh, boundary_color)
                    } else { 0 }
                } else { 0 }
            } else { 0 },
    }
}

theorem ctx_rb_between_top(bh: Nat, color: Color) {
    ensures ctx_rb_between(Context::Top, bh, color, bh, color) == 1 by {
        unfold(ctx_rb_between(Context::Top, bh, color, bh, color));
        normalize();
    }
}

theorem ctx_rb_between_left_frame(id: struct rb_node*, parent: struct rb_node*,
        color: Color, sibling: RbTree, up: Context, bh: Nat, focus_color: Color,
        boundary_bh: Nat, boundary_color: Color) {
    requires is_rb(sibling) == 1;
    requires bh == black_height(sibling);
    requires node_color_ok(color, focus_color, rb_color(sibling)) == 1;
    requires ctx_rb_between(up, frame_black_height(color, bh), color,
        boundary_bh, boundary_color) == 1;

    ensures ctx_rb_between(Context::Left(id, parent, color, sibling, up),
        bh, focus_color, boundary_bh, boundary_color) == 1 by {
        unfold(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
            bh, focus_color, boundary_bh, boundary_color));
        rewrite(ctx_rb_between(up, frame_black_height(color, bh), color,
            boundary_bh, boundary_color) == 1);
        normalize() using { is_rb(sibling) == 1; bh == black_height(sibling);
            node_color_ok(color, focus_color, rb_color(sibling)) == 1; }
    }
}

theorem ctx_rb_between_right_frame(id: struct rb_node*, parent: struct rb_node*,
        color: Color, sibling: RbTree, up: Context, bh: Nat, focus_color: Color,
        boundary_bh: Nat, boundary_color: Color) {
    requires is_rb(sibling) == 1;
    requires black_height(sibling) == bh;
    requires node_color_ok(color, rb_color(sibling), focus_color) == 1;
    requires ctx_rb_between(up, frame_black_height(color, bh), color,
        boundary_bh, boundary_color) == 1;

    ensures ctx_rb_between(Context::Right(id, parent, color, sibling, up),
        bh, focus_color, boundary_bh, boundary_color) == 1 by {
        unfold(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
            bh, focus_color, boundary_bh, boundary_color));
        rewrite(ctx_rb_between(up, frame_black_height(color, bh), color,
            boundary_bh, boundary_color) == 1);
        normalize() using { is_rb(sibling) == 1; black_height(sibling) == bh;
            node_color_ok(color, rb_color(sibling), focus_color) == 1; }
    }
}

theorem ctx_rb_concat(inner: Context, outer: Context, bh: Nat, focus_color: Color,
                      boundary_bh: Nat, boundary_color: Color) {
    requires ctx_rb_between(inner, bh, focus_color, boundary_bh, boundary_color) == 1;
    requires ctx_rb(outer, boundary_bh, boundary_color) == 1;

    ensures ctx_rb(ctx_concat(inner, outer), bh, focus_color) == 1 by {
        induct(inner) as ih {
            Context::Top => {
                if bh == boundary_bh {
                    if focus_color == boundary_color {
                        unfold(ctx_concat(Context::Top, outer));
                        rewrite(bh == boundary_bh);
                        rewrite(focus_color == boundary_color);
                        assumption();
                    } else {
                        have ctx_rb_between(Context::Top, bh, focus_color,
                            boundary_bh, boundary_color) != 1 by {
                            unfold(ctx_rb_between(Context::Top, bh, focus_color,
                                boundary_bh, boundary_color));
                            normalize() using { bh == boundary_bh;
                                not(focus_color == boundary_color); }
                        }
                        contradiction(ctx_rb_between(Context::Top, bh, focus_color,
                            boundary_bh, boundary_color) == 1);
                    }
                } else {
                    have ctx_rb_between(Context::Top, bh, focus_color,
                        boundary_bh, boundary_color) != 1 by {
                        unfold(ctx_rb_between(Context::Top, bh, focus_color,
                            boundary_bh, boundary_color));
                        normalize() using { not(bh == boundary_bh); }
                    }
                    contradiction(ctx_rb_between(Context::Top, bh, focus_color,
                        boundary_bh, boundary_color) == 1);
                }
            }
            Context::Left(id, parent, color, sibling, up) => {
                if is_rb(sibling) == 1 {
                    if bh == black_height(sibling) {
                        if node_color_ok(color, focus_color, rb_color(sibling)) == 1 {
                            have ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                    bh, focus_color, boundary_bh, boundary_color)
                                == ctx_rb_between(up, frame_black_height(color, bh), color,
                                    boundary_bh, boundary_color) by {
                                unfold(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                    bh, focus_color, boundary_bh, boundary_color));
                                normalize() using {
                                    is_rb(sibling) == 1;
                                    bh == black_height(sibling);
                                    node_color_ok(color, focus_color, rb_color(sibling)) == 1;
                                }
                            }
                            have ctx_rb_between(up, frame_black_height(color, bh), color,
                                boundary_bh, boundary_color) == 1 by {
                                rewrite(ctx_rb_between(up, frame_black_height(color, bh), color,
                                    boundary_bh, boundary_color)
                                    == ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                        bh, focus_color, boundary_bh, boundary_color));
                                assumption();
                            }
                            apply(ih(up, outer, frame_black_height(color, bh), color,
                                boundary_bh, boundary_color));
                            apply(ctx_rb_left_frame(id, parent, color, sibling,
                                ctx_concat(up, outer), bh, focus_color));
                            unfold(ctx_concat(Context::Left(id, parent, color, sibling, up), outer));
                            assumption();
                        } else {
                            have ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                bh, focus_color, boundary_bh, boundary_color) != 1 by {
                                unfold(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                    bh, focus_color, boundary_bh, boundary_color));
                                normalize() using {
                                    is_rb(sibling) == 1;
                                    bh == black_height(sibling);
                                    not(node_color_ok(color, focus_color, rb_color(sibling)) == 1);
                                }
                            }
                            contradiction(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                bh, focus_color, boundary_bh, boundary_color) == 1);
                        }
                    } else {
                        have ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                            bh, focus_color, boundary_bh, boundary_color) != 1 by {
                            unfold(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                                bh, focus_color, boundary_bh, boundary_color));
                            normalize() using { is_rb(sibling) == 1; not(bh == black_height(sibling)); }
                        }
                        contradiction(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                            bh, focus_color, boundary_bh, boundary_color) == 1);
                    }
                } else {
                    have ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                        bh, focus_color, boundary_bh, boundary_color) != 1 by {
                        unfold(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                            bh, focus_color, boundary_bh, boundary_color));
                        normalize() using { not(is_rb(sibling) == 1); }
                    }
                    contradiction(ctx_rb_between(Context::Left(id, parent, color, sibling, up),
                        bh, focus_color, boundary_bh, boundary_color) == 1);
                }
            }
            Context::Right(id, parent, color, sibling, up) => {
                if is_rb(sibling) == 1 {
                    if black_height(sibling) == bh {
                        if node_color_ok(color, rb_color(sibling), focus_color) == 1 {
                            have ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                    bh, focus_color, boundary_bh, boundary_color)
                                == ctx_rb_between(up, frame_black_height(color, bh), color,
                                    boundary_bh, boundary_color) by {
                                unfold(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                    bh, focus_color, boundary_bh, boundary_color));
                                normalize() using {
                                    is_rb(sibling) == 1;
                                    black_height(sibling) == bh;
                                    node_color_ok(color, rb_color(sibling), focus_color) == 1;
                                }
                            }
                            have ctx_rb_between(up, frame_black_height(color, bh), color,
                                boundary_bh, boundary_color) == 1 by {
                                rewrite(ctx_rb_between(up, frame_black_height(color, bh), color,
                                    boundary_bh, boundary_color)
                                    == ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                        bh, focus_color, boundary_bh, boundary_color));
                                assumption();
                            }
                            apply(ih(up, outer, frame_black_height(color, bh), color,
                                boundary_bh, boundary_color));
                            apply(ctx_rb_right_frame(id, parent, color, sibling,
                                ctx_concat(up, outer), bh, focus_color));
                            unfold(ctx_concat(Context::Right(id, parent, color, sibling, up), outer));
                            assumption();
                        } else {
                            have ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                bh, focus_color, boundary_bh, boundary_color) != 1 by {
                                unfold(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                    bh, focus_color, boundary_bh, boundary_color));
                                normalize() using {
                                    is_rb(sibling) == 1;
                                    black_height(sibling) == bh;
                                    not(node_color_ok(color, rb_color(sibling), focus_color) == 1);
                                }
                            }
                            contradiction(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                bh, focus_color, boundary_bh, boundary_color) == 1);
                        }
                    } else {
                        have ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                            bh, focus_color, boundary_bh, boundary_color) != 1 by {
                            unfold(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                                bh, focus_color, boundary_bh, boundary_color));
                            normalize() using { is_rb(sibling) == 1; not(black_height(sibling) == bh); }
                        }
                        contradiction(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                            bh, focus_color, boundary_bh, boundary_color) == 1);
                    }
                } else {
                    have ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                        bh, focus_color, boundary_bh, boundary_color) != 1 by {
                        unfold(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                            bh, focus_color, boundary_bh, boundary_color));
                        normalize() using { not(is_rb(sibling) == 1); }
                    }
                    contradiction(ctx_rb_between(Context::Right(id, parent, color, sibling, up),
                        bh, focus_color, boundary_bh, boundary_color) == 1);
                }
            }
        }
    }
}

theorem ctx_consistent_concat(inner: Context, outer: Context, sub: RbTree,
                              root_parent: struct rb_node*) {
    requires ctx_consistent(outer, plug(inner, sub), root_parent) == 1;

    ensures ctx_consistent(ctx_concat(inner, outer), sub, root_parent) == 1 by {
        apply(plug_parent_consistent_transport(outer, plug(inner, sub), root_parent));
        apply(plug_ctx_concat(inner, outer, sub));
        have rb_parent_consistent(plug(ctx_concat(inner, outer), sub), root_parent) == 1 by {
            rewrite(plug(ctx_concat(inner, outer), sub) == plug(outer, plug(inner, sub)));
            assumption();
        }
        apply(plug_parent_consistent_ctx(ctx_concat(inner, outer), sub, root_parent));
        assumption();
    }
}

theorem plug_rb_from_ctx_rb(ctx: Context, sub: RbTree) {
    requires is_rb(sub) == 1;
    requires ctx_rb(ctx, black_height(sub), rb_color(sub)) == 1;

    ensures is_rb_root(plug(ctx, sub)) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_rb_top(black_height(sub), rb_color(sub)));
                apply(rb_root_black_is_color_black(sub));
                have rb_root_black(sub) == 1 by auto;
                apply(is_rb_root_from_parts(sub));
                unfold(plug(Context::Top, sub));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_left_up(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(is_rb_node_from_parts(identity, grandparent, color, sub, sibling_model));
                apply(black_height_node_frame(identity, grandparent, color, sub, sibling_model));
                apply(rb_color_node(identity, grandparent, color, sub, sibling_model));
                have ctx_rb(up_model,
                        black_height(RbTree::Node(identity, grandparent, color, sub,
                            sibling_model)),
                        rb_color(RbTree::Node(identity, grandparent, color, sub,
                            sibling_model))) == 1 by {
                    rewrite(black_height(RbTree::Node(identity, grandparent, color, sub,
                        sibling_model)) == frame_black_height(color, black_height(sub)));
                    rewrite(rb_color(RbTree::Node(identity, grandparent, color, sub,
                        sibling_model)) == color);
                    assumption();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sub, sibling_model)));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    sub));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(ctx_rb_right_up(identity, grandparent, color, sibling_model, up_model,
                    black_height(sub), rb_color(sub)));
                apply(is_rb_node_from_parts(identity, grandparent, color, sibling_model, sub));
                apply(black_height_node_frame(identity, grandparent, color, sibling_model, sub));
                apply(rb_color_node(identity, grandparent, color, sibling_model, sub));
                have ctx_rb(up_model,
                        black_height(RbTree::Node(identity, grandparent, color, sibling_model,
                            sub)),
                        rb_color(RbTree::Node(identity, grandparent, color, sibling_model,
                            sub))) == 1 by {
                    rewrite(rb_color(RbTree::Node(identity, grandparent, color, sibling_model,
                        sub)) == color);
                    rewrite(black_height(RbTree::Node(identity, grandparent, color,
                        sibling_model, sub))
                        == frame_black_height(color, black_height(sibling_model)));
                    rewrite(black_height(sibling_model) == black_height(sub));
                    assumption();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, sub)));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model,
                    up_model), sub));
                assumption();
            }
        }
    }
}

theorem is_rb_root_is_rb(tree: RbTree) {
    requires is_rb_root(tree) == 1;

    ensures is_rb(tree) == 1 by {
        if is_rb(tree) == 1 {
            assumption();
        } else {
            have is_rb_root(tree) != 1 by {
                unfold(is_rb_root(tree));
                normalize() using { not(is_rb(tree) == 1); }
            }
            contradiction(is_rb_root(tree) == 1);
        }
    }
}

theorem is_rb_root_value(tree: RbTree) {
    requires is_rb(tree) == 1;

    ensures rb_root_black(tree) == is_rb_root(tree) by {
        unfold(is_rb_root(tree));
        normalize() using { is_rb(tree) == 1; }
    }
}

theorem is_rb_root_root_black(tree: RbTree) {
    requires is_rb_root(tree) == 1;

    ensures rb_root_black(tree) == 1 by {
        apply(is_rb_root_is_rb(tree));
        apply(is_rb_root_value(tree));
        rewrite(rb_root_black(tree) == is_rb_root(tree));
        assumption();
    }
}

theorem node_color_ok_weaken_left(color: Color, left_color: Color, right_color: Color) {
    requires node_color_ok(color, left_color, right_color) == 1;

    ensures node_color_ok(color, Color::Black, right_color) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(node_color_ok_black(Color::Black, right_color));
                assumption();
            }
            Color::Red => {
                apply(node_color_ok_red_right(left_color, right_color));
                apply(color_black_black());
                apply(node_color_ok_red(Color::Black, right_color));
                assumption();
            }
        }
    }
}

theorem node_color_ok_weaken_right(color: Color, left_color: Color, right_color: Color) {
    requires node_color_ok(color, left_color, right_color) == 1;

    ensures node_color_ok(color, left_color, Color::Black) == 1 by {
        induct(color) as ih {
            Color::Black => {
                apply(node_color_ok_black(left_color, Color::Black));
                assumption();
            }
            Color::Red => {
                apply(node_color_ok_red_left(left_color, right_color));
                apply(color_black_black());
                apply(node_color_ok_red(left_color, Color::Black));
                assumption();
            }
        }
    }
}

function ctx_almost_rb_insert(ctx: Context, bh: Nat) -> int32 {
    ctx_rb(ctx, bh, Color::Black)
}

theorem ctx_almost_rb_insert_unfolds(ctx: Context, bh: Nat) {
    ensures ctx_almost_rb_insert(ctx, bh) == ctx_rb(ctx, bh, Color::Black) by {
        unfold(ctx_almost_rb_insert(ctx, bh));
        normalize();
    }
}

theorem ctx_almost_rb_insert_folds(ctx: Context, bh: Nat) {
    ensures ctx_rb(ctx, bh, Color::Black) == ctx_almost_rb_insert(ctx, bh) by {
        unfold(ctx_almost_rb_insert(ctx, bh));
        normalize();
    }
}

theorem ctx_almost_rb_insert_holds(ctx: Context, bh: Nat) {
    requires ctx_rb(ctx, bh, Color::Black) == 1;

    ensures ctx_almost_rb_insert(ctx, bh) == 1 by {
        apply(ctx_almost_rb_insert_unfolds(ctx, bh));
        rewrite(ctx_almost_rb_insert(ctx, bh) == ctx_rb(ctx, bh, Color::Black));
        assumption();
    }
}

theorem ctx_almost_rb_insert_black_focus(ctx: Context, bh: Nat) {
    requires ctx_almost_rb_insert(ctx, bh) == 1;

    ensures ctx_rb(ctx, bh, Color::Black) == 1 by {
        apply(ctx_almost_rb_insert_folds(ctx, bh));
        rewrite(ctx_rb(ctx, bh, Color::Black) == ctx_almost_rb_insert(ctx, bh));
        assumption();
    }
}

theorem ctx_rb_weaken_to_almost(ctx: Context, bh: Nat, focus_color: Color) {
    requires ctx_rb(ctx, bh, focus_color) == 1;

    ensures ctx_almost_rb_insert(ctx, bh) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(color_black_black());
                apply(ctx_rb_top_frame(bh, Color::Black));
                apply(ctx_almost_rb_insert_holds(Context::Top, bh));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_left_height(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_left_up(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(node_color_ok_weaken_left(color, focus_color, rb_color(sibling_model)));
                apply(ctx_rb_left_frame(identity, grandparent, color, sibling_model, up_model,
                    bh, Color::Black));
                apply(ctx_almost_rb_insert_holds(
                    Context::Left(identity, grandparent, color, sibling_model, up_model), bh));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_right_height(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(ctx_rb_right_up(identity, grandparent, color, sibling_model, up_model,
                    bh, focus_color));
                apply(node_color_ok_weaken_right(color, rb_color(sibling_model), focus_color));
                apply(ctx_rb_right_frame(identity, grandparent, color, sibling_model, up_model,
                    bh, Color::Black));
                apply(ctx_almost_rb_insert_holds(
                    Context::Right(identity, grandparent, color, sibling_model, up_model), bh));
                assumption();
            }
        }
    }
}

theorem ctx_rb_left_red_up(identity: struct rb_node*, grandparent: struct rb_node*,
                           sibling_model: RbTree, up_model: Context,
                           bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, bh, Color::Red) == 1 by {
        apply(ctx_rb_left_sibling(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_height(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_colors(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Red, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                bh == black_height(sibling_model);
                node_color_ok(Color::Red, focus_color, rb_color(sibling_model)) == 1;
            }
        }
        rewrite(ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Left(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_left_black_up(identity: struct rb_node*, grandparent: struct rb_node*,
                             sibling_model: RbTree, up_model: Context,
                             bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, Nat::Succ(bh), Color::Black) == 1 by {
        apply(ctx_rb_left_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_left_colors(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Black, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                bh == black_height(sibling_model);
                node_color_ok(Color::Black, focus_color, rb_color(sibling_model)) == 1;
            }
        }
        rewrite(ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_right_red_up(identity: struct rb_node*, grandparent: struct rb_node*,
                            sibling_model: RbTree, up_model: Context,
                            bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, bh, Color::Red) == 1 by {
        apply(ctx_rb_right_sibling(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_height(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_colors(identity, grandparent, Color::Red, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Red, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                black_height(sibling_model) == bh;
                node_color_ok(Color::Red, rb_color(sibling_model), focus_color) == 1;
            }
        }
        rewrite(ctx_rb(up_model, bh, Color::Red)
            == ctx_rb(Context::Right(identity, grandparent, Color::Red, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_rb_right_black_up(identity: struct rb_node*, grandparent: struct rb_node*,
                              sibling_model: RbTree, up_model: Context,
                              bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1;

    ensures ctx_rb(up_model, Nat::Succ(bh), Color::Black) == 1 by {
        apply(ctx_rb_right_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        apply(ctx_rb_right_colors(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        have ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(
                Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color) by {
            unfold(ctx_rb(
                Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
            unfold(frame_black_height(Color::Black, bh));
            normalize() using {
                is_rb(sibling_model) == 1;
                black_height(sibling_model) == bh;
                node_color_ok(Color::Black, rb_color(sibling_model), focus_color) == 1;
            }
        }
        rewrite(ctx_rb(up_model, Nat::Succ(bh), Color::Black)
            == ctx_rb(
                Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
                bh, focus_color));
        assumption();
    }
}

theorem ctx_black_frame_left_restores(identity: struct rb_node*, grandparent: struct rb_node*,
                                      sibling_model: RbTree, up_model: Context,
                                      bh: Nat, focus_color: Color) {
    requires ctx_almost_rb_insert(
        Context::Left(identity, grandparent, Color::Black, sibling_model, up_model), bh) == 1;

    ensures ctx_rb(Context::Left(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1 by {
        apply(ctx_almost_rb_insert_black_focus(
            Context::Left(identity, grandparent, Color::Black, sibling_model, up_model), bh));
        apply(ctx_rb_left_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_left_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_left_up(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(node_color_ok_black(focus_color, rb_color(sibling_model)));
        apply(ctx_rb_left_frame(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        assumption();
    }
}

theorem ctx_black_frame_right_restores(identity: struct rb_node*, grandparent: struct rb_node*,
                                       sibling_model: RbTree, up_model: Context,
                                       bh: Nat, focus_color: Color) {
    requires ctx_almost_rb_insert(
        Context::Right(identity, grandparent, Color::Black, sibling_model, up_model), bh) == 1;

    ensures ctx_rb(Context::Right(identity, grandparent, Color::Black, sibling_model, up_model),
        bh, focus_color) == 1 by {
        apply(ctx_almost_rb_insert_black_focus(
            Context::Right(identity, grandparent, Color::Black, sibling_model, up_model), bh));
        apply(ctx_rb_right_sibling(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_right_height(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(ctx_rb_right_up(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, Color::Black));
        apply(node_color_ok_black(rb_color(sibling_model), focus_color));
        apply(ctx_rb_right_frame(identity, grandparent, Color::Black, sibling_model, up_model,
            bh, focus_color));
        assumption();
    }
}

theorem ctx_insert_black_parent_exit(ctx: Context, sub: RbTree) {
    requires is_rb(sub) == 1;
    requires ctx_rb(ctx, black_height(sub), rb_color(sub)) == 1;

    ensures is_rb_root(plug(ctx, sub)) == 1 by {
        apply(plug_rb_from_ctx_rb(ctx, sub));
        assumption();
    }
}

theorem ctx_insert_root_exit(sub: RbTree) {
    requires is_rb(sub) == 1;

    ensures is_rb_root(plug(Context::Top, rb_recolor(sub, Color::Black))) == 1 by {
        apply(is_rb_is_almost_rb_insert(sub));
        apply(rb_blacken_root_restores_rb(sub));
        unfold(plug(Context::Top, rb_recolor(sub, Color::Black)));
        assumption();
    }
}

theorem node_color_ok_red_focus_is_black(color: Color, right_color: Color) {
    requires node_color_ok(color, Color::Red, right_color) == 1;

    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Black => {
                normalize();
            }
            Color::Red => {
                apply(node_color_ok_red_left(Color::Red, right_color));
                apply(color_black_red());
                have color_black(Color::Red) != 1 by auto;
                contradiction(color_black(Color::Red) == 1);
            }
        }
    }
}

theorem nat_eq_symmetric(x: Nat, y: Nat) {
    requires x == y;

    ensures y == x by {
        rewrite(x == y);
        normalize();
    }
}

theorem nat_eq_transitive(x: Nat, y: Nat, z: Nat) {
    requires x == y;
    requires y == z;

    ensures x == z by {
        rewrite(x == y);
        assumption();
    }
}

theorem ctx_insert_cursor_left_parent(parent: struct rb_node*, grandparent: struct rb_node*,
                                      sub: RbTree, sibling_model: RbTree, up_g: Context) {
    requires is_rb(sub) == 1;
    requires ctx_rb(Context::Left(parent, grandparent, Color::Red, sibling_model, up_g),
        black_height(sub), Color::Black) == 1;

    ensures almost_rb_insert(
        RbTree::Node(parent, grandparent, Color::Red, sub, sibling_model)) == 1 by {
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(almost_rb_insert_node(parent, grandparent, Color::Red, sub, sibling_model));
        assumption();
    }

    ensures rb_root_black(sibling_model) == 1 by {
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(sibling_model)));
        apply(rb_root_black_is_color_black(sibling_model));
        rewrite(rb_root_black(sibling_model) == color_black(rb_color(sibling_model)));
        assumption();
    }

    ensures black_height(RbTree::Node(parent, grandparent, Color::Red, sub, sibling_model))
        == black_height(sub) by {
        apply(black_height_red_node(parent, grandparent, sub, sibling_model));
        assumption();
    }

    ensures ctx_rb(up_g, black_height(sub), Color::Red) == 1 by {
        apply(ctx_rb_left_red_up(parent, grandparent, sibling_model, up_g,
            black_height(sub), Color::Black));
        assumption();
    }
}

theorem ctx_insert_cursor_right_parent(parent: struct rb_node*, grandparent: struct rb_node*,
                                       sub: RbTree, sibling_model: RbTree, up_g: Context) {
    requires is_rb(sub) == 1;
    requires ctx_rb(Context::Right(parent, grandparent, Color::Red, sibling_model, up_g),
        black_height(sub), Color::Black) == 1;

    ensures almost_rb_insert(
        RbTree::Node(parent, grandparent, Color::Red, sibling_model, sub)) == 1 by {
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(almost_rb_insert_node(parent, grandparent, Color::Red, sibling_model, sub));
        assumption();
    }

    ensures rb_root_black(sibling_model) == 1 by {
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        apply(node_color_ok_red_left(rb_color(sibling_model), Color::Black));
        apply(rb_root_black_is_color_black(sibling_model));
        rewrite(rb_root_black(sibling_model) == color_black(rb_color(sibling_model)));
        assumption();
    }

    ensures black_height(sibling_model) == black_height(sub) by {
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        assumption();
    }

    ensures black_height(RbTree::Node(parent, grandparent, Color::Red, sibling_model, sub))
        == black_height(sub) by {
        apply(black_height_red_node(parent, grandparent, sibling_model, sub));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, sibling_model, up_g,
            black_height(sub), Color::Black));
        rewrite(black_height(RbTree::Node(parent, grandparent, Color::Red, sibling_model, sub))
            == black_height(sibling_model));
        assumption();
    }

    ensures ctx_rb(up_g, black_height(sub), Color::Red) == 1 by {
        apply(ctx_rb_right_red_up(parent, grandparent, sibling_model, up_g,
            black_height(sub), Color::Black));
        assumption();
    }
}

theorem rb_insert_fix_recolor_shape(grandparent: struct rb_node*, above: struct rb_node*,
                                    left_node: struct rb_node*, right_node: struct rb_node*,
                                    ll: RbTree, lr: RbTree, rl: RbTree, rr: RbTree) {
    ensures rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))
        == RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)) by {
        unfold(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr))));
        unfold(rb_recolor_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr)), Color::Black));
        unfold(rb_recolor(RbTree::Node(right_node, grandparent, Color::Red, rl, rr),
            Color::Black));
        unfold(rb_recolor_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)), Color::Black));
        unfold(rb_recolor(RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            Color::Black));
        unfold(rb_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)), Color::Red));
        normalize();
    }
}

theorem rb_insert_fix_recolor_black_height(grandparent: struct rb_node*,
                                           above: struct rb_node*,
                                           left_node: struct rb_node*,
                                           right_node: struct rb_node*,
                                           ll: RbTree, lr: RbTree, rl: RbTree, rr: RbTree) {
    ensures black_height(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Red, rl, rr))))
        == Nat::Succ(black_height(ll)) by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, left_node, right_node,
            ll, lr, rl, rr));
        apply(black_height_red_node(grandparent, above,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        apply(black_height_black_node(left_node, grandparent, ll, lr));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        rewrite(black_height(RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)))
            == black_height(RbTree::Node(left_node, grandparent, Color::Black, ll, lr)));
        rewrite(black_height(RbTree::Node(left_node, grandparent, Color::Black, ll, lr))
            == Nat::Succ(black_height(ll)));
        normalize();
    }
}

theorem rb_insert_fix_recolor_root_is_red(grandparent: struct rb_node*,
                                          above: struct rb_node*,
                                          left_node: struct rb_node*,
                                          right_node: struct rb_node*,
                                          ll: RbTree, lr: RbTree, rl: RbTree, rr: RbTree) {
    ensures rb_color(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))) == Color::Red by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, left_node, right_node,
            ll, lr, rl, rr));
        apply(rb_color_node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(left_node, grandparent, Color::Red, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Red, rl, rr)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
                RbTree::Node(right_node, grandparent, Color::Black, rl, rr)));
        rewrite(rb_color(RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(left_node, grandparent, Color::Black, ll, lr),
            RbTree::Node(right_node, grandparent, Color::Black, rl, rr))) == Color::Red);
        normalize();
    }
}

theorem ctx_insert_case1_left(above: struct rb_node*, grandparent: struct rb_node*,
                              parent: struct rb_node*, uncle: struct rb_node*,
                              a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires almost_rb_insert(RbTree::Node(parent, grandparent, Color::Red, a, b)) == 1;
    requires ctx_rb(Context::Left(grandparent, above, Color::Black,
        RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
        black_height(a), Color::Red) == 1;

    ensures is_rb(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d)))) == 1 by {
        apply(almost_rb_insert_node_left(parent, grandparent, Color::Red, a, b));
        apply(almost_rb_insert_node_right(parent, grandparent, Color::Red, a, b));
        apply(almost_rb_insert_node_black_heights(parent, grandparent, Color::Red, a, b));
        apply(ctx_rb_left_sibling(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            black_height(a), Color::Red));
        apply(is_rb_node_left(uncle, grandparent, Color::Red, c, d));
        apply(is_rb_node_right(uncle, grandparent, Color::Red, c, d));
        apply(is_rb_node_black_heights(uncle, grandparent, Color::Red, c, d));
        apply(ctx_rb_left_height(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            black_height(a), Color::Red));
        apply(black_height_red_node(uncle, grandparent, c, d));
        have black_height(a) == black_height(c) by {
            rewrite(black_height(a)
                == black_height(RbTree::Node(uncle, grandparent, Color::Red, c, d)));
            assumption();
        }
        apply(is_rb_black_node(parent, grandparent, a, b));
        apply(is_rb_black_node(uncle, grandparent, c, d));
        apply(rb_root_black_black_node(parent, grandparent, a, b));
        apply(rb_root_black_black_node(uncle, grandparent, c, d));
        apply(black_height_black_node(parent, grandparent, a, b));
        apply(black_height_black_node(uncle, grandparent, c, d));
        have black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
            == black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d)) by {
            rewrite(black_height(RbTree::Node(parent, grandparent, Color::Black, a, b))
                == Nat::Succ(black_height(a)));
            rewrite(black_height(RbTree::Node(uncle, grandparent, Color::Black, c, d))
                == Nat::Succ(black_height(c)));
            rewrite(black_height(a) == black_height(c));
            normalize();
        }
        apply(is_rb_red_node(grandparent, above,
            RbTree::Node(parent, grandparent, Color::Black, a, b),
            RbTree::Node(uncle, grandparent, Color::Black, c, d)));
        apply(rb_insert_fix_recolor_shape(grandparent, above, parent, uncle, a, b, c, d));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d)));
        assumption();
    }

    ensures black_height(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d))))
        == Nat::Succ(black_height(a)) by {
        apply(rb_insert_fix_recolor_black_height(grandparent, above, parent, uncle,
            a, b, c, d));
        assumption();
    }

    ensures ctx_almost_rb_insert(up2, Nat::Succ(black_height(a))) == 1 by {
        apply(ctx_rb_left_black_up(grandparent, above,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            black_height(a), Color::Red));
        apply(ctx_almost_rb_insert_holds(up2, Nat::Succ(black_height(a))));
        assumption();
    }
}

theorem ctx_insert_case1_right(above: struct rb_node*, grandparent: struct rb_node*,
                               parent: struct rb_node*, uncle: struct rb_node*,
                               a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires almost_rb_insert(RbTree::Node(parent, grandparent, Color::Red, c, d)) == 1;
    requires ctx_rb(Context::Right(grandparent, above, Color::Black,
        RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
        black_height(c), Color::Red) == 1;

    ensures is_rb(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b),
            RbTree::Node(parent, grandparent, Color::Red, c, d)))) == 1 by {
        apply(almost_rb_insert_node_left(parent, grandparent, Color::Red, c, d));
        apply(almost_rb_insert_node_right(parent, grandparent, Color::Red, c, d));
        apply(almost_rb_insert_node_black_heights(parent, grandparent, Color::Red, c, d));
        apply(ctx_rb_right_sibling(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(is_rb_node_left(uncle, grandparent, Color::Red, a, b));
        apply(is_rb_node_right(uncle, grandparent, Color::Red, a, b));
        apply(is_rb_node_black_heights(uncle, grandparent, Color::Red, a, b));
        apply(ctx_rb_right_height(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(black_height_red_node(uncle, grandparent, a, b));
        have black_height(a) == black_height(c) by {
            rewrite(black_height(a)
                == black_height(RbTree::Node(uncle, grandparent, Color::Red, a, b)));
            assumption();
        }
        apply(is_rb_black_node(uncle, grandparent, a, b));
        apply(is_rb_black_node(parent, grandparent, c, d));
        apply(rb_root_black_black_node(uncle, grandparent, a, b));
        apply(rb_root_black_black_node(parent, grandparent, c, d));
        apply(black_height_black_node(uncle, grandparent, a, b));
        apply(black_height_black_node(parent, grandparent, c, d));
        have black_height(RbTree::Node(uncle, grandparent, Color::Black, a, b))
            == black_height(RbTree::Node(parent, grandparent, Color::Black, c, d)) by {
            rewrite(black_height(RbTree::Node(uncle, grandparent, Color::Black, a, b))
                == Nat::Succ(black_height(a)));
            rewrite(black_height(RbTree::Node(parent, grandparent, Color::Black, c, d))
                == Nat::Succ(black_height(c)));
            rewrite(black_height(a) == black_height(c));
            normalize();
        }
        apply(is_rb_red_node(grandparent, above,
            RbTree::Node(uncle, grandparent, Color::Black, a, b),
            RbTree::Node(parent, grandparent, Color::Black, c, d)));
        apply(rb_insert_fix_recolor_shape(grandparent, above, uncle, parent, a, b, c, d));
        rewrite(rb_insert_fix_recolor(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d)))
            == RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d)));
        assumption();
    }

    ensures black_height(rb_insert_fix_recolor(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b),
            RbTree::Node(parent, grandparent, Color::Red, c, d))))
        == Nat::Succ(black_height(a)) by {
        apply(rb_insert_fix_recolor_black_height(grandparent, above, uncle, parent,
            a, b, c, d));
        assumption();
    }

    ensures ctx_almost_rb_insert(up2, Nat::Succ(black_height(c))) == 1 by {
        apply(ctx_rb_right_black_up(grandparent, above,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(ctx_almost_rb_insert_holds(up2, Nat::Succ(black_height(c))));
        assumption();
    }
}

theorem rb_insert_fix_outer_left_shape(grandparent: struct rb_node*, above: struct rb_node*,
                                       parent: struct rb_node*, cursor: struct rb_node*,
                                       a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_outer_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b), c),
            d))
        == RbTree::Node(parent, above, Color::Black,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red,
                rb_reparent(c, grandparent), d)) by {
        unfold(rb_insert_fix_outer_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_rotate_right(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d)));
        unfold(rb_recolor_right(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Black,
                    rb_reparent(c, grandparent), d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black,
            rb_reparent(c, grandparent), d), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d)), Color::Black));
        normalize();
    }
}

theorem rb_insert_fix_outer_right_shape(grandparent: struct rb_node*, above: struct rb_node*,
                                        parent: struct rb_node*, cursor: struct rb_node*,
                                        a: RbTree, b: RbTree, c: RbTree, d: RbTree) {
    ensures rb_insert_fix_outer_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red, b,
                RbTree::Node(cursor, parent, Color::Red, c, d))))
        == RbTree::Node(parent, above, Color::Black,
            RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)) by {
        unfold(rb_insert_fix_outer_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_rotate_left(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d)))));
        unfold(rb_recolor_left(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Black, a,
                    rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Red));
        unfold(rb_recolor(RbTree::Node(grandparent, parent, Color::Black, a,
            rb_reparent(b, grandparent)), Color::Red));
        unfold(rb_recolor(
            RbTree::Node(parent, above, Color::Red,
                RbTree::Node(grandparent, parent, Color::Red, a,
                    rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Black));
        normalize();
    }
}

theorem ctx_insert_case3_left(above: struct rb_node*, grandparent: struct rb_node*,
                              parent: struct rb_node*, cursor: struct rb_node*,
                              a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, a, b)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(
        Context::Left(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2)),
        black_height(a), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, a, b), c),
            d)))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, a, b));
        apply(is_rb_node_right(cursor, parent, Color::Red, a, b));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, a, b));
        apply(is_rb_red_node_children_are_black(cursor, parent, a, b));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, a, b));
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(c)));
        apply(rb_root_black_is_color_black(c));
        have rb_root_black(c) == 1 by auto;
        apply(ctx_rb_left_red_up(parent, grandparent, c,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(a), Color::Black));
        apply(ctx_rb_left_sibling(grandparent, above, Color::Black, d, up2,
            black_height(a), Color::Red));
        apply(ctx_rb_left_height(grandparent, above, Color::Black, d, up2,
            black_height(a), Color::Red));
        apply(ctx_rb_left_black_up(grandparent, above, d, up2,
            black_height(a), Color::Red));
        apply(nat_eq_symmetric(black_height(a), black_height(b)));
        apply(nat_eq_transitive(black_height(b), black_height(a), black_height(c)));
        apply(nat_eq_symmetric(black_height(a), black_height(c)));
        apply(nat_eq_transitive(black_height(c), black_height(a), black_height(d)));
        apply(rb_insert_fix_outer_left_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_left_shape(grandparent, above, parent, cursor, a, b, c, d));
        apply(black_height_black_node(parent, above,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)));
        apply(black_height_red_node(cursor, parent, a, b));
        apply(rb_color_node(parent, above, Color::Black,
            RbTree::Node(cursor, parent, Color::Red, a, b),
            RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)));
        have black_height(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Nat::Succ(black_height(a)) by {
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(cursor, parent, Color::Red, a, b),
                    RbTree::Node(grandparent, parent, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(black_height(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d)))
                == Nat::Succ(black_height(RbTree::Node(cursor, parent, Color::Red, a, b))));
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, a, b))
                == black_height(a));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Color::Black by {
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(cursor, parent, Color::Red, a, b),
                    RbTree::Node(grandparent, parent, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(rb_color(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(cursor, parent, Color::Red, a, b),
                RbTree::Node(grandparent, parent, Color::Red,
                    rb_reparent(c, grandparent), d))) == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, a, b), c),
                        d))),
                rb_color(rb_insert_fix_outer_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, a, b), c),
                        d)))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Nat::Succ(black_height(a)));
            rewrite(rb_color(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, a, b), c),
                    d))) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, a, b), c),
                d))));
        assumption();
    }
}

theorem ctx_insert_case3_right(above: struct rb_node*, grandparent: struct rb_node*,
                               parent: struct rb_node*, cursor: struct rb_node*,
                               a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, c, d)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(
        Context::Right(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2)),
        black_height(c), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red, b,
                RbTree::Node(cursor, parent, Color::Red, c, d)))))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, c, d));
        apply(is_rb_node_right(cursor, parent, Color::Red, c, d));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, c, d));
        apply(is_rb_red_node_children_are_black(cursor, parent, c, d));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, c, d));
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(node_color_ok_red_left(rb_color(b), Color::Black));
        apply(rb_root_black_is_color_black(b));
        have rb_root_black(b) == 1 by auto;
        apply(ctx_rb_right_red_up(parent, grandparent, b,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(c), Color::Black));
        apply(ctx_rb_right_sibling(grandparent, above, Color::Black, a, up2,
            black_height(c), Color::Red));
        apply(ctx_rb_right_height(grandparent, above, Color::Black, a, up2,
            black_height(c), Color::Red));
        apply(ctx_rb_right_black_up(grandparent, above, a, up2,
            black_height(c), Color::Red));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        apply(nat_eq_transitive(black_height(a), black_height(c), black_height(b)));
        apply(rb_insert_fix_outer_right_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_right_shape(grandparent, above, parent, cursor, a, b, c, d));
        apply(black_height_black_node(parent, above,
            RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)));
        apply(black_height_red_node(grandparent, parent, a, rb_reparent(b, grandparent)));
        apply(rb_color_node(parent, above, Color::Black,
            RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(cursor, parent, Color::Red, c, d)));
        have black_height(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
            == Nat::Succ(black_height(c)) by {
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d))))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(grandparent, parent, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(cursor, parent, Color::Red, c, d)));
            rewrite(black_height(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d)))
                == Nat::Succ(black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                    rb_reparent(b, grandparent)))));
            rewrite(black_height(RbTree::Node(grandparent, parent, Color::Red, a,
                rb_reparent(b, grandparent))) == black_height(a));
            rewrite(black_height(a) == black_height(c));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
            == Color::Black by {
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d))))
                == RbTree::Node(parent, above, Color::Black,
                    RbTree::Node(grandparent, parent, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(cursor, parent, Color::Red, c, d)));
            rewrite(rb_color(RbTree::Node(parent, above, Color::Black,
                RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(cursor, parent, Color::Red, c, d))) == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red, b,
                            RbTree::Node(cursor, parent, Color::Red, c, d))))),
                rb_color(rb_insert_fix_outer_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red, b,
                            RbTree::Node(cursor, parent, Color::Red, c, d)))))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
                == Nat::Succ(black_height(c)));
            rewrite(rb_color(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red, b,
                        RbTree::Node(cursor, parent, Color::Red, c, d)))))
                == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red, b,
                    RbTree::Node(cursor, parent, Color::Red, c, d))))));
        assumption();
    }
}

theorem ctx_insert_case2_left(above: struct rb_node*, grandparent: struct rb_node*,
                              parent: struct rb_node*, cursor: struct rb_node*,
                              a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(
        Context::Right(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2)),
        black_height(b), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_left(rb_insert_fix_inner_left(
        RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a,
                RbTree::Node(cursor, parent, Color::Red, b, c)),
            d))))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(node_color_ok_red_left(rb_color(a), Color::Black));
        apply(rb_root_black_is_color_black(a));
        have rb_root_black(a) == 1 by auto;
        apply(ctx_rb_right_red_up(parent, grandparent, a,
            Context::Left(grandparent, above, Color::Black, d, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_left_sibling(grandparent, above, Color::Black, d, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_left_height(grandparent, above, Color::Black, d, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_left_black_up(grandparent, above, d, up2,
            black_height(b), Color::Red));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        apply(nat_eq_transitive(black_height(c), black_height(b), black_height(d)));
        apply(rb_insert_fix_inner_left_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_inner_left_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_left_shape(grandparent, above, cursor, parent,
            a, rb_reparent(b, parent), c, d));
        apply(black_height_black_node(cursor, above,
            RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
            RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d)));
        apply(black_height_red_node(parent, cursor, a, rb_reparent(b, parent)));
        apply(rb_color_node(cursor, above, Color::Black,
            RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
            RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d)));
        have black_height(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Nat::Succ(black_height(b)) by {
            rewrite(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d))
                == RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d));
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                    RbTree::Node(grandparent, cursor, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(black_height(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                RbTree::Node(grandparent, cursor, Color::Red,
                    rb_reparent(c, grandparent), d)))
                == Nat::Succ(black_height(RbTree::Node(parent, cursor, Color::Red, a,
                    rb_reparent(b, parent)))));
            rewrite(black_height(RbTree::Node(parent, cursor, Color::Red, a,
                rb_reparent(b, parent))) == black_height(a));
            rewrite(black_height(a) == black_height(b));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Color::Black by {
            rewrite(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d))
                == RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d));
            rewrite(rb_insert_fix_outer_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(cursor, grandparent, Color::Red,
                        RbTree::Node(parent, cursor, Color::Red, a,
                            rb_reparent(b, parent)), c),
                    d))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                    RbTree::Node(grandparent, cursor, Color::Red,
                        rb_reparent(c, grandparent), d)));
            rewrite(rb_color(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)),
                RbTree::Node(grandparent, cursor, Color::Red,
                    rb_reparent(c, grandparent), d))) == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red, a,
                            RbTree::Node(cursor, parent, Color::Red, b, c)),
                        d)))),
                rb_color(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                    RbTree::Node(grandparent, above, Color::Black,
                        RbTree::Node(parent, grandparent, Color::Red, a,
                            RbTree::Node(cursor, parent, Color::Red, b, c)),
                        d))))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Nat::Succ(black_height(b)));
            rewrite(rb_color(rb_insert_fix_outer_left(rb_insert_fix_inner_left(
                RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a,
                        RbTree::Node(cursor, parent, Color::Red, b, c)),
                    d)))) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_left(rb_insert_fix_inner_left(
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a,
                    RbTree::Node(cursor, parent, Color::Red, b, c)),
                d)))));
        assumption();
    }
}

theorem ctx_insert_case2_right(above: struct rb_node*, grandparent: struct rb_node*,
                               parent: struct rb_node*, cursor: struct rb_node*,
                               a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(
        Context::Left(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2)),
        black_height(b), Color::Black) == 1;

    ensures is_rb_root(plug(up2, rb_insert_fix_outer_right(rb_insert_fix_inner_right(
        RbTree::Node(grandparent, above, Color::Black, a,
            RbTree::Node(parent, grandparent, Color::Red,
                RbTree::Node(cursor, parent, Color::Red, b, c), d)))))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(d)));
        apply(rb_root_black_is_color_black(d));
        have rb_root_black(d) == 1 by auto;
        apply(ctx_rb_left_red_up(parent, grandparent, d,
            Context::Right(grandparent, above, Color::Black, a, up2),
            black_height(b), Color::Black));
        apply(ctx_rb_right_sibling(grandparent, above, Color::Black, a, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_right_height(grandparent, above, Color::Black, a, up2,
            black_height(b), Color::Red));
        apply(ctx_rb_right_black_up(grandparent, above, a, up2,
            black_height(b), Color::Red));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        apply(nat_eq_transitive(black_height(c), black_height(b), black_height(d)));
        apply(rb_insert_fix_inner_right_restores(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_inner_right_becomes_outer(grandparent, above, parent, cursor,
            a, b, c, d));
        apply(rb_insert_fix_outer_right_shape(grandparent, above, cursor, parent,
            a, b, rb_reparent(c, parent), d));
        apply(black_height_black_node(cursor, above,
            RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        apply(black_height_red_node(grandparent, cursor, a, rb_reparent(b, grandparent)));
        apply(rb_color_node(cursor, above, Color::Black,
            RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
            RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        have black_height(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
            == Nat::Succ(black_height(b)) by {
            rewrite(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))
                == RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))));
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(grandparent, cursor, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
            rewrite(black_height(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))
                == Nat::Succ(black_height(RbTree::Node(grandparent, cursor, Color::Red, a,
                    rb_reparent(b, grandparent)))));
            rewrite(black_height(RbTree::Node(grandparent, cursor, Color::Red, a,
                rb_reparent(b, grandparent))) == black_height(a));
            rewrite(black_height(a) == black_height(b));
            normalize();
        }
        have rb_color(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
            == Color::Black by {
            rewrite(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))
                == RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))));
            rewrite(rb_insert_fix_outer_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(cursor, grandparent, Color::Red, b,
                        RbTree::Node(parent, cursor, Color::Red,
                            rb_reparent(c, parent), d))))
                == RbTree::Node(cursor, above, Color::Black,
                    RbTree::Node(grandparent, cursor, Color::Red, a,
                        rb_reparent(b, grandparent)),
                    RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
            rewrite(rb_color(RbTree::Node(cursor, above, Color::Black,
                RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)),
                RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))
                == Color::Black);
            normalize();
        }
        have ctx_rb(up2,
                black_height(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, b, c), d))))),
                rb_color(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                    RbTree::Node(grandparent, above, Color::Black, a,
                        RbTree::Node(parent, grandparent, Color::Red,
                            RbTree::Node(cursor, parent, Color::Red, b, c), d)))))) == 1 by {
            rewrite(black_height(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
                == Nat::Succ(black_height(b)));
            rewrite(rb_color(rb_insert_fix_outer_right(rb_insert_fix_inner_right(
                RbTree::Node(grandparent, above, Color::Black, a,
                    RbTree::Node(parent, grandparent, Color::Red,
                        RbTree::Node(cursor, parent, Color::Red, b, c), d)))))
                == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up2, rb_insert_fix_outer_right(rb_insert_fix_inner_right(
            RbTree::Node(grandparent, above, Color::Black, a,
                RbTree::Node(parent, grandparent, Color::Red,
                    RbTree::Node(cursor, parent, Color::Red, b, c), d))))));
        assumption();
    }
}

theorem plug_left_frame(identity: struct rb_node*, grandparent: struct rb_node*, color: Color,
                        sibling_model: RbTree, up_model: Context, sub: RbTree) {
    ensures plug(Context::Left(identity, grandparent, color, sibling_model, up_model), sub)
        == plug(up_model, RbTree::Node(identity, grandparent, color, sub, sibling_model)) by {
        unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), sub));
        normalize();
    }
}

theorem plug_right_frame(identity: struct rb_node*, grandparent: struct rb_node*, color: Color,
                         sibling_model: RbTree, up_model: Context, sub: RbTree) {
    ensures plug(Context::Right(identity, grandparent, color, sibling_model, up_model), sub)
        == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, sub)) by {
        unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), sub));
        normalize();
    }
}

theorem plug_left_in_left(above: struct rb_node*, grandparent: struct rb_node*,
                          parent: struct rb_node*, gcolor: Color, pcolor: Color,
                          sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Left(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model), uncle)) by {
        apply(plug_left_frame(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_left_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        rewrite(plug(Context::Left(parent, grandparent, pcolor, sibling_model,
                Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Left(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        assumption();
    }
}

theorem plug_right_in_left(above: struct rb_node*, grandparent: struct rb_node*,
                           parent: struct rb_node*, gcolor: Color, pcolor: Color,
                           sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Right(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub), uncle)) by {
        apply(plug_right_frame(parent, grandparent, pcolor, sibling_model,
            Context::Left(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_left_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        rewrite(plug(Context::Right(parent, grandparent, pcolor, sibling_model,
                Context::Left(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Left(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        assumption();
    }
}

theorem plug_left_in_right(above: struct rb_node*, grandparent: struct rb_node*,
                           parent: struct rb_node*, gcolor: Color, pcolor: Color,
                           sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Left(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor, uncle,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model))) by {
        apply(plug_left_frame(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_right_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        rewrite(plug(Context::Left(parent, grandparent, pcolor, sibling_model,
                Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Right(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sub, sibling_model)));
        assumption();
    }
}

theorem plug_right_in_right(above: struct rb_node*, grandparent: struct rb_node*,
                            parent: struct rb_node*, gcolor: Color, pcolor: Color,
                            sibling_model: RbTree, uncle: RbTree, up2: Context, sub: RbTree) {
    ensures plug(Context::Right(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
        == plug(up2, RbTree::Node(grandparent, above, gcolor, uncle,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub))) by {
        apply(plug_right_frame(parent, grandparent, pcolor, sibling_model,
            Context::Right(grandparent, above, gcolor, uncle, up2), sub));
        apply(plug_right_frame(grandparent, above, gcolor, uncle, up2,
            RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        rewrite(plug(Context::Right(parent, grandparent, pcolor, sibling_model,
                Context::Right(grandparent, above, gcolor, uncle, up2)), sub)
            == plug(Context::Right(grandparent, above, gcolor, uncle, up2),
                RbTree::Node(parent, grandparent, pcolor, sibling_model, sub)));
        assumption();
    }
}

theorem ctx_insert_case2_left_step(above: struct rb_node*, grandparent: struct rb_node*,
                                   parent: struct rb_node*, cursor: struct rb_node*,
                                   a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, b, c)), 0) == 1;

    ensures rb_inorder(plug(Context::Left(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))))
        == rb_inorder(plug(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, b, c))) by {
        apply(plug_left_in_left(above, grandparent, cursor, Color::Black, Color::Red, c, d, up2, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        apply(plug_right_in_left(above, grandparent, parent, Color::Black, Color::Red, a, d, up2, RbTree::Node(cursor, parent, Color::Red, b, c)));
        apply(rb_insert_fix_inner_left_becomes_outer(grandparent, above, parent, cursor, a, b, c, d));
        apply(rb_insert_fix_inner_left_preserves_inorder(RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, a, RbTree::Node(cursor, parent, Color::Red, b, c)), d)));
        apply(plug_inorder_transport(up2, rb_insert_fix_inner_left(RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, a, RbTree::Node(cursor, parent, Color::Red, b, c)), d)), RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, a, RbTree::Node(cursor, parent, Color::Red, b, c)), d)));
        rewrite(plug(Context::Left(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))) == plug(up2, RbTree::Node(grandparent, above, Color::Black, RbTree::Node(cursor, grandparent, Color::Red, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c), d)));
        rewrite(plug(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, b, c)) == plug(up2, RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, a, RbTree::Node(cursor, parent, Color::Red, b, c)), d)));
        rewrite(RbTree::Node(grandparent, above, Color::Black, RbTree::Node(cursor, grandparent, Color::Red, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c), d) == rb_insert_fix_inner_left(RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, a, RbTree::Node(cursor, parent, Color::Red, b, c)), d)));
        assumption();
    }

    ensures is_rb(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(black_height_red_node(cursor, parent, b, c));
        apply(ctx_rb_right_sibling(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(node_color_ok_red_left(rb_color(a), Color::Black));
        apply(rb_root_black_is_color_black(a));
        have rb_root_black(a) == 1 by auto;
        apply(rb_reparent_preserves_is_rb(b, parent));
        apply(rb_reparent_preserves_black_height(b, parent));
        apply(rb_reparent_preserves_rb_root_black(b, parent));
        have is_rb(rb_reparent(b, parent)) == 1 by auto;
        have rb_root_black(rb_reparent(b, parent)) == 1 by auto;
        have black_height(a) == black_height(rb_reparent(b, parent)) by {
            rewrite(black_height(rb_reparent(b, parent)) == black_height(b));
            rewrite(black_height(a) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)));
            assumption();
        }
        apply(is_rb_red_node(parent, cursor, a, rb_reparent(b, parent)));
        assumption();
    }

    ensures ctx_rb(Context::Left(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))), Color::Black) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(black_height_red_node(cursor, parent, b, c));
        apply(black_height_red_node(parent, cursor, a, rb_reparent(b, parent)));
        apply(ctx_rb_right_height(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(rb_root_black_is_color_black(c));
        have color_black(rb_color(c)) == 1 by auto;
        apply(color_black_black());
        apply(node_color_ok_red(Color::Black, rb_color(c)));
        have black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)) by auto;
        have black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))) == black_height(c) by auto;
        apply(ctx_rb_right_red_up(parent, grandparent, a, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(frame_black_height_red(black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)))));
        have ctx_rb(Context::Left(grandparent, above, Color::Black, d, up2), frame_black_height(Color::Red, black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)))), Color::Red) == 1 by {
            rewrite(frame_black_height(Color::Red, black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)))) == black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
            rewrite(black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)));
            assumption();
        }
        apply(ctx_rb_left_frame(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))), Color::Black));
        assumption();
    }

    ensures rb_parent_consistent(plug(Context::Left(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(ctx_consistent_right_focus(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(ctx_consistent_right_sibling(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(ctx_consistent_right_up(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(rb_parent_consistent_node_left(cursor, parent, Color::Red, b, c, parent));
        apply(rb_parent_consistent_node_right(cursor, parent, Color::Red, b, c, parent));
        apply(rb_reparent_parent_consistent(b, cursor, parent));
        apply(rb_node_is_reflexive(cursor));
        apply(rb_node_is_reflexive(grandparent));
        apply(rb_parent_consistent_node(parent, cursor, Color::Red, a, rb_reparent(b, parent), cursor));
        apply(rb_parent_consistent_node(cursor, grandparent, Color::Red, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c, grandparent));
        apply(ctx_consistent_swap(Context::Left(grandparent, above, Color::Black, d, up2), parent, grandparent, Color::Red, a, RbTree::Node(cursor, parent, Color::Red, b, c), RbTree::Node(cursor, grandparent, Color::Red, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), c), 0));
        apply(ctx_consistent_left_frame(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), 0));
        apply(plug_parent_consistent_transport(Context::Left(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), 0));
        assumption();
    }

    ensures rb_root_black(b) == 1 by {
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        assumption();
    }
}

theorem ctx_insert_case2_right_step(above: struct rb_node*, grandparent: struct rb_node*,
                                    parent: struct rb_node*, cursor: struct rb_node*,
                                    a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, b, c)), 0) == 1;

    ensures rb_inorder(plug(Context::Right(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))
        == rb_inorder(plug(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, b, c))) by {
        apply(plug_right_in_right(above, grandparent, cursor, Color::Black, Color::Red, b, a, up2, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        apply(plug_left_in_right(above, grandparent, parent, Color::Black, Color::Red, d, a, up2, RbTree::Node(cursor, parent, Color::Red, b, c)));
        apply(rb_insert_fix_inner_right_becomes_outer(grandparent, above, parent, cursor, a, b, c, d));
        apply(rb_insert_fix_inner_right_preserves_inorder(RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        apply(plug_inorder_transport(up2, rb_insert_fix_inner_right(RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, b, c), d))), RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        rewrite(plug(Context::Right(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) == plug(up2, RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(cursor, grandparent, Color::Red, b, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))));
        rewrite(plug(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, b, c)) == plug(up2, RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        rewrite(RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(cursor, grandparent, Color::Red, b, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) == rb_insert_fix_inner_right(RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, b, c), d))));
        assumption();
    }

    ensures is_rb(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(black_height_red_node(cursor, parent, b, c));
        apply(ctx_rb_left_sibling(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(d)));
        apply(rb_root_black_is_color_black(d));
        have rb_root_black(d) == 1 by auto;
        apply(rb_reparent_preserves_is_rb(c, parent));
        apply(rb_reparent_preserves_black_height(c, parent));
        apply(rb_reparent_preserves_rb_root_black(c, parent));
        have is_rb(rb_reparent(c, parent)) == 1 by auto;
        have rb_root_black(rb_reparent(c, parent)) == 1 by auto;
        have black_height(rb_reparent(c, parent)) == black_height(d) by {
            rewrite(black_height(rb_reparent(c, parent)) == black_height(c));
            rewrite(black_height(c) == black_height(b));
            rewrite(black_height(b) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)));
            assumption();
        }
        apply(is_rb_red_node(parent, cursor, rb_reparent(c, parent), d));
        assumption();
    }

    ensures ctx_rb(Context::Right(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)), Color::Black) == 1 by {
        apply(is_rb_node_left(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_right(cursor, parent, Color::Red, b, c));
        apply(is_rb_node_black_heights(cursor, parent, Color::Red, b, c));
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        apply(black_height_red_node(cursor, parent, b, c));
        apply(black_height_red_node(parent, cursor, rb_reparent(c, parent), d));
        apply(ctx_rb_left_height(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(rb_root_black_is_color_black(b));
        have color_black(rb_color(b)) == 1 by auto;
        apply(color_black_black());
        apply(node_color_ok_red(rb_color(b), Color::Black));
        apply(rb_reparent_preserves_black_height(c, parent));
        apply(nat_eq_symmetric(black_height(b), black_height(c)));
        have black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)) by {
            rewrite(black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) == black_height(rb_reparent(c, parent)));
            rewrite(black_height(rb_reparent(c, parent)) == black_height(c));
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, b, c)) == black_height(b));
            assumption();
        }
        have black_height(b) == black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) by {
            rewrite(black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)));
            rewrite(black_height(RbTree::Node(cursor, parent, Color::Red, b, c)) == black_height(b));
            normalize();
        }
        apply(ctx_rb_left_red_up(parent, grandparent, d, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black));
        apply(frame_black_height_red(black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))));
        have ctx_rb(Context::Right(grandparent, above, Color::Black, a, up2), frame_black_height(Color::Red, black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))), Color::Red) == 1 by {
            rewrite(frame_black_height(Color::Red, black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) == black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
            rewrite(black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)) == black_height(RbTree::Node(cursor, parent, Color::Red, b, c)));
            assumption();
        }
        apply(ctx_rb_right_frame(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)), Color::Black));
        assumption();
    }

    ensures rb_parent_consistent(plug(Context::Right(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(ctx_consistent_left_focus(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(ctx_consistent_left_sibling(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(ctx_consistent_left_up(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(cursor, parent, Color::Red, b, c), 0));
        apply(rb_parent_consistent_node_left(cursor, parent, Color::Red, b, c, parent));
        apply(rb_parent_consistent_node_right(cursor, parent, Color::Red, b, c, parent));
        apply(rb_reparent_parent_consistent(c, cursor, parent));
        apply(rb_node_is_reflexive(cursor));
        apply(rb_node_is_reflexive(grandparent));
        apply(rb_parent_consistent_node(parent, cursor, Color::Red, rb_reparent(c, parent), d, cursor));
        apply(rb_parent_consistent_node(cursor, grandparent, Color::Red, b, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d), grandparent));
        apply(ctx_consistent_swap(Context::Right(grandparent, above, Color::Black, a, up2), parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, b, c), d, RbTree::Node(cursor, grandparent, Color::Red, b, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)), 0));
        apply(ctx_consistent_right_frame(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d), 0));
        apply(plug_parent_consistent_transport(Context::Right(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d), 0));
        assumption();
    }

    ensures rb_root_black(c) == 1 by {
        apply(is_rb_red_node_children_are_black(cursor, parent, b, c));
        apply(is_rb_red_node_right_child_is_black(cursor, parent, b, c));
        assumption();
    }
}

theorem plug_recolor_inorder(ctx: Context, tree: RbTree, color: Color) {
    ensures rb_inorder(plug(ctx, rb_recolor(tree, color))) == rb_inorder(plug(ctx, tree)) by {
        apply(rb_recolor_preserves_inorder(tree, color));
        apply(plug_inorder_transport(ctx, rb_recolor(tree, color), tree));
        assumption();
    }
}

theorem plug_insert_fix_recolor_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_recolor(tree)))
        == rb_inorder(plug(ctx, tree)) by {
        apply(rb_insert_fix_recolor_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_recolor(tree), tree));
        assumption();
    }
}

theorem plug_insert_fix_outer_left_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_left(tree)))
        == rb_inorder(plug(ctx, tree)) by {
        apply(rb_insert_fix_outer_left_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_outer_left(tree), tree));
        assumption();
    }
}

theorem plug_insert_fix_outer_right_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_right(tree)))
        == rb_inorder(plug(ctx, tree)) by {
        apply(rb_insert_fix_outer_right_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_outer_right(tree), tree));
        assumption();
    }
}

theorem plug_insert_fix_inner_left_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_left(rb_insert_fix_inner_left(tree))))
        == rb_inorder(plug(ctx, tree)) by {
        apply(plug_insert_fix_outer_left_inorder(ctx, rb_insert_fix_inner_left(tree)));
        apply(rb_insert_fix_inner_left_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_inner_left(tree), tree));
        rewrite(rb_inorder(plug(ctx, rb_insert_fix_outer_left(rb_insert_fix_inner_left(tree))))
            == rb_inorder(plug(ctx, rb_insert_fix_inner_left(tree))));
        assumption();
    }
}

theorem plug_insert_fix_inner_right_inorder(ctx: Context, tree: RbTree) {
    ensures rb_inorder(plug(ctx, rb_insert_fix_outer_right(rb_insert_fix_inner_right(tree))))
        == rb_inorder(plug(ctx, tree)) by {
        apply(plug_insert_fix_outer_right_inorder(ctx, rb_insert_fix_inner_right(tree)));
        apply(rb_insert_fix_inner_right_preserves_inorder(tree));
        apply(plug_inorder_transport(ctx, rb_insert_fix_inner_right(tree), tree));
        rewrite(rb_inorder(plug(ctx, rb_insert_fix_outer_right(rb_insert_fix_inner_right(tree))))
            == rb_inorder(plug(ctx, rb_insert_fix_inner_right(tree))));
        assumption();
    }
}

spec enum Links {
    Leaf,
    Link(struct rb_node*, struct rb_node*, Links, Links),
}

function rb_links(tree: RbTree) -> Links
    decreases tree
{
    match tree {
        RbTree::Empty => Links::Leaf,
        RbTree::Node(node, parent, color, left, right) =>
            Links::Link(node, parent, rb_links(left), rb_links(right)),
    }
}

function links_consistent(links: Links, p: struct rb_node*) -> int32
    decreases links
{
    match links {
        Links::Leaf => 1,
        Links::Link(node, parent, left, right) =>
            if links_consistent(left, node) == 1 {
                if links_consistent(right, node) == 1 {
                    if rb_node_is(parent, p) == 1 { 1 } else { 0 }
                } else {
                    0
                }
            } else {
                0
            },
    }
}

theorem rb_parent_consistent_is_links_consistent(tree: RbTree, p: struct rb_node*) {
    ensures rb_parent_consistent(tree, p) == links_consistent(rb_links(tree), p) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_parent_consistent(RbTree::Empty, p));
                unfold(rb_links(RbTree::Empty));
                unfold(links_consistent(Links::Leaf, p));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(ih(left, node));
                apply(ih(right, node));
                unfold(rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p));
                unfold(rb_links(RbTree::Node(node, parent, color, left, right)));
                unfold(links_consistent(
                    Links::Link(node, parent, rb_links(left), rb_links(right)), p));
                rewrite(rb_parent_consistent(left, node)
                    == links_consistent(rb_links(left), node));
                rewrite(rb_parent_consistent(right, node)
                    == links_consistent(rb_links(right), node));
                normalize();
            }
        }
    }
}

theorem rb_links_recolor(tree: RbTree, color: Color) {
    ensures rb_links(rb_recolor(tree, color)) == rb_links(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                unfold(rb_recolor(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_links(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_links(RbTree::Node(node, parent, old_color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_links_recolor_left(tree: RbTree, color: Color) {
    ensures rb_links(rb_recolor_left(tree, color)) == rb_links(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor_left(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                apply(rb_links_recolor(left, color));
                unfold(rb_recolor_left(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_links(RbTree::Node(node, parent, old_color,
                    rb_recolor(left, color), right)));
                unfold(rb_links(RbTree::Node(node, parent, old_color, left, right)));
                rewrite(rb_links(rb_recolor(left, color)) == rb_links(left));
                normalize();
            }
        }
    }
}

theorem rb_links_recolor_right(tree: RbTree, color: Color) {
    ensures rb_links(rb_recolor_right(tree, color)) == rb_links(tree) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_recolor_right(RbTree::Empty, color));
                normalize();
            }
            RbTree::Node(node, parent, old_color, left, right) => {
                apply(rb_links_recolor(right, color));
                unfold(rb_recolor_right(RbTree::Node(node, parent, old_color, left, right), color));
                unfold(rb_links(RbTree::Node(node, parent, old_color, left,
                    rb_recolor(right, color))));
                unfold(rb_links(RbTree::Node(node, parent, old_color, left, right)));
                rewrite(rb_links(rb_recolor(right, color)) == rb_links(right));
                normalize();
            }
        }
    }
}

theorem rb_links_insert_fix_recolor(tree: RbTree) {
    ensures rb_links(rb_insert_fix_recolor(tree)) == rb_links(tree) by {
        apply(rb_links_recolor(
            rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red));
        apply(rb_links_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black));
        apply(rb_links_recolor_right(tree, Color::Black));
        unfold(rb_insert_fix_recolor(tree));
        rewrite(rb_links(rb_recolor(
            rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black), Color::Red))
            == rb_links(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black)));
        rewrite(rb_links(rb_recolor_left(rb_recolor_right(tree, Color::Black), Color::Black))
            == rb_links(rb_recolor_right(tree, Color::Black)));
        rewrite(rb_links(rb_recolor_right(tree, Color::Black)) == rb_links(tree));
        normalize();
    }
}

theorem plug_links_transport(ctx: Context, a: RbTree, b: RbTree) {
    requires rb_links(a) == rb_links(b);

    ensures rb_links(plug(ctx, a)) == rb_links(plug(ctx, b)) by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(plug(Context::Top, a));
                unfold(plug(Context::Top, b));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                have rb_links(RbTree::Node(identity, grandparent, color, a, sibling_model))
                    == rb_links(RbTree::Node(identity, grandparent, color, b, sibling_model)) by {
                    unfold(rb_links(RbTree::Node(identity, grandparent, color, a, sibling_model)));
                    unfold(rb_links(RbTree::Node(identity, grandparent, color, b, sibling_model)));
                    rewrite(rb_links(a) == rb_links(b));
                    normalize();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, a, sibling_model),
                    RbTree::Node(identity, grandparent, color, b, sibling_model)));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    a));
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model),
                    b));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                have rb_links(RbTree::Node(identity, grandparent, color, sibling_model, a))
                    == rb_links(RbTree::Node(identity, grandparent, color, sibling_model, b)) by {
                    unfold(rb_links(RbTree::Node(identity, grandparent, color, sibling_model, a)));
                    unfold(rb_links(RbTree::Node(identity, grandparent, color, sibling_model, b)));
                    rewrite(rb_links(a) == rb_links(b));
                    normalize();
                }
                apply(ih(up_model,
                    RbTree::Node(identity, grandparent, color, sibling_model, a),
                    RbTree::Node(identity, grandparent, color, sibling_model, b)));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    a));
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model),
                    b));
                assumption();
            }
        }
    }
}

theorem plug_parent_consistent_links(ctx: Context, a: RbTree, b: RbTree, p: struct rb_node*) {
    requires rb_links(a) == rb_links(b);

    ensures rb_parent_consistent(plug(ctx, a), p) == rb_parent_consistent(plug(ctx, b), p) by {
        apply(plug_links_transport(ctx, a, b));
        apply(rb_parent_consistent_is_links_consistent(plug(ctx, a), p));
        apply(rb_parent_consistent_is_links_consistent(plug(ctx, b), p));
        rewrite(rb_parent_consistent(plug(ctx, a), p)
            == links_consistent(rb_links(plug(ctx, a)), p));
        rewrite(rb_parent_consistent(plug(ctx, b), p)
            == links_consistent(rb_links(plug(ctx, b)), p));
        rewrite(rb_links(plug(ctx, a)) == rb_links(plug(ctx, b)));
        normalize();
    }
}

theorem plug_insert_fix_recolor_parent_consistent(ctx: Context, tree: RbTree,
                                                  p: struct rb_node*) {
    ensures rb_parent_consistent(plug(ctx, rb_insert_fix_recolor(tree)), p)
        == rb_parent_consistent(plug(ctx, tree), p) by {
        apply(rb_links_insert_fix_recolor(tree));
        apply(plug_parent_consistent_links(ctx, rb_insert_fix_recolor(tree), tree, p));
        assumption();
    }
}

theorem rb_parent_is_node_parent(node: struct rb_node*, parent: struct rb_node*, color: Color,
                                 left: RbTree, right: RbTree, p: struct rb_node*) {
    requires rb_parent_is(RbTree::Node(node, parent, color, left, right), p) == 1;

    ensures parent == p by {
        if parent == p {
            assumption();
        } else {
            have rb_parent_is(RbTree::Node(node, parent, color, left, right), p) != 1 by {
                unfold(rb_parent_is(RbTree::Node(node, parent, color, left, right), p));
                normalize() using { not(parent == p); }
            }
            contradiction(rb_parent_is(RbTree::Node(node, parent, color, left, right), p) == 1);
        }
    }
}

theorem rb_parent_is_node_of(node: struct rb_node*, parent: struct rb_node*, color: Color,
                             left: RbTree, right: RbTree) {
    ensures rb_parent_is(RbTree::Node(node, parent, color, left, right), parent) == 1 by {
        unfold(rb_parent_is(RbTree::Node(node, parent, color, left, right), parent));
        normalize();
    }
}

theorem node_color_ok_red_right_focus_is_black(color: Color, left_color: Color) {
    requires node_color_ok(color, left_color, Color::Red) == 1;

    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Black => {
                normalize();
            }
            Color::Red => {
                apply(node_color_ok_red_right(left_color, Color::Red));
                apply(color_black_red());
                have color_black(Color::Red) != 1 by auto;
                contradiction(color_black(Color::Red) == 1);
            }
        }
    }
}

theorem ctx_rb_left_red_focus_black(identity: struct rb_node*, grandparent: struct rb_node*,
                                    color: Color, sibling_model: RbTree, up_model: Context,
                                    bh: Nat) {
    requires ctx_rb(Context::Left(identity, grandparent, color, sibling_model, up_model),
        bh, Color::Red) == 1;

    ensures color == Color::Black by {
        apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model, up_model,
            bh, Color::Red));
        apply(node_color_ok_red_focus_is_black(color, rb_color(sibling_model)));
        assumption();
    }
}

theorem ctx_rb_right_red_focus_black(identity: struct rb_node*, grandparent: struct rb_node*,
                                     color: Color, sibling_model: RbTree, up_model: Context,
                                     bh: Nat) {
    requires ctx_rb(Context::Right(identity, grandparent, color, sibling_model, up_model),
        bh, Color::Red) == 1;

    ensures color == Color::Black by {
        apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model, up_model,
            bh, Color::Red));
        apply(node_color_ok_red_right_focus_is_black(color, rb_color(sibling_model)));
        assumption();
    }
}

theorem ctx_insert_case1_left_step(above: struct rb_node*, grandparent: struct rb_node*,
                                   parent: struct rb_node*, uncle: struct rb_node*,
                                   a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires almost_rb_insert(RbTree::Node(parent, grandparent, Color::Red, a, b)) == 1;
    requires ctx_rb(Context::Left(grandparent, above, Color::Black,
        RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
        black_height(a), Color::Red) == 1;

    ensures is_rb(RbTree::Node(grandparent, above, Color::Red,
        RbTree::Node(parent, grandparent, Color::Black, a, b),
        RbTree::Node(uncle, grandparent, Color::Black, c, d))) == 1 by {
        apply(ctx_insert_case1_left(above, grandparent, parent, uncle, a, b, c, d, up2));
        apply(rb_insert_fix_recolor_shape(grandparent, above, parent, uncle, a, b, c, d));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a, b),
                    RbTree::Node(uncle, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(parent, grandparent, Color::Black, a, b),
                    RbTree::Node(uncle, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        assumption();
    }

    ensures ctx_almost_rb_insert(up2, black_height(RbTree::Node(grandparent, above, Color::Red,
        RbTree::Node(parent, grandparent, Color::Black, a, b),
        RbTree::Node(uncle, grandparent, Color::Black, c, d)))) == 1 by {
        apply(ctx_insert_case1_left(above, grandparent, parent, uncle, a, b, c, d, up2));
        apply(rb_insert_fix_recolor_shape(grandparent, above, parent, uncle, a, b, c, d));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a, b),
                    RbTree::Node(uncle, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(parent, grandparent, Color::Black, a, b),
                    RbTree::Node(uncle, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        rewrite(black_height(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))))
            == Nat::Succ(black_height(a)));
        assumption();
    }

    ensures rb_inorder(plug(up2, RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(parent, grandparent, Color::Black, a, b),
            RbTree::Node(uncle, grandparent, Color::Black, c, d))))
        == rb_inorder(plug(Context::Left(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
            RbTree::Node(parent, grandparent, Color::Red, a, b))) by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, parent, uncle, a, b, c, d));
        apply(plug_insert_fix_recolor_inorder(up2, RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(parent, grandparent, Color::Red, a, b),
            RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        apply(plug_left_frame(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            RbTree::Node(parent, grandparent, Color::Red, a, b)));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a, b),
                    RbTree::Node(uncle, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(parent, grandparent, Color::Black, a, b),
                    RbTree::Node(uncle, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        rewrite(plug(Context::Left(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
                RbTree::Node(parent, grandparent, Color::Red, a, b))
            == plug(up2, RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up2, RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(parent, grandparent, Color::Black, a, b),
            RbTree::Node(uncle, grandparent, Color::Black, c, d))), 0)
        == rb_parent_consistent(plug(Context::Left(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
            RbTree::Node(parent, grandparent, Color::Red, a, b)), 0) by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, parent, uncle, a, b, c, d));
        apply(plug_insert_fix_recolor_parent_consistent(up2,
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d)), 0));
        apply(plug_left_frame(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, c, d), up2,
            RbTree::Node(parent, grandparent, Color::Red, a, b)));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(parent, grandparent, Color::Red, a, b),
                    RbTree::Node(uncle, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(parent, grandparent, Color::Black, a, b),
                    RbTree::Node(uncle, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(parent, grandparent, Color::Black, a, b),
                RbTree::Node(uncle, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        rewrite(plug(Context::Left(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, c, d), up2),
                RbTree::Node(parent, grandparent, Color::Red, a, b))
            == plug(up2, RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(parent, grandparent, Color::Red, a, b),
                RbTree::Node(uncle, grandparent, Color::Red, c, d))));
        assumption();
    }
}

theorem ctx_insert_case1_right_step(above: struct rb_node*, grandparent: struct rb_node*,
                                    parent: struct rb_node*, uncle: struct rb_node*,
                                    a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires almost_rb_insert(RbTree::Node(parent, grandparent, Color::Red, c, d)) == 1;
    requires ctx_rb(Context::Right(grandparent, above, Color::Black,
        RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
        black_height(c), Color::Red) == 1;

    ensures is_rb(RbTree::Node(grandparent, above, Color::Red,
        RbTree::Node(uncle, grandparent, Color::Black, a, b),
        RbTree::Node(parent, grandparent, Color::Black, c, d))) == 1 by {
        apply(ctx_insert_case1_right(above, grandparent, parent, uncle, a, b, c, d, up2));
        apply(rb_insert_fix_recolor_shape(grandparent, above, uncle, parent, a, b, c, d));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(uncle, grandparent, Color::Red, a, b),
                    RbTree::Node(parent, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(uncle, grandparent, Color::Black, a, b),
                    RbTree::Node(parent, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))));
        assumption();
    }

    ensures ctx_almost_rb_insert(up2, black_height(RbTree::Node(grandparent, above, Color::Red,
        RbTree::Node(uncle, grandparent, Color::Black, a, b),
        RbTree::Node(parent, grandparent, Color::Black, c, d)))) == 1 by {
        apply(ctx_insert_case1_right(above, grandparent, parent, uncle, a, b, c, d, up2));
        apply(rb_insert_fix_recolor_shape(grandparent, above, uncle, parent, a, b, c, d));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(uncle, grandparent, Color::Red, a, b),
                    RbTree::Node(parent, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(uncle, grandparent, Color::Black, a, b),
                    RbTree::Node(parent, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))));
        rewrite(black_height(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))))
            == Nat::Succ(black_height(a)));
        apply(ctx_rb_right_height(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            black_height(c), Color::Red));
        apply(black_height_red_node(uncle, grandparent, a, b));
        have black_height(a) == black_height(c) by {
            rewrite(black_height(a)
                == black_height(RbTree::Node(uncle, grandparent, Color::Red, a, b)));
            assumption();
        }
        rewrite(black_height(a) == black_height(c));
        assumption();
    }

    ensures rb_inorder(plug(up2, RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(uncle, grandparent, Color::Black, a, b),
            RbTree::Node(parent, grandparent, Color::Black, c, d))))
        == rb_inorder(plug(Context::Right(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
            RbTree::Node(parent, grandparent, Color::Red, c, d))) by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, uncle, parent, a, b, c, d));
        apply(plug_insert_fix_recolor_inorder(up2, RbTree::Node(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b),
            RbTree::Node(parent, grandparent, Color::Red, c, d))));
        apply(plug_right_frame(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            RbTree::Node(parent, grandparent, Color::Red, c, d)));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(uncle, grandparent, Color::Red, a, b),
                    RbTree::Node(parent, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(uncle, grandparent, Color::Black, a, b),
                    RbTree::Node(parent, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))));
        rewrite(plug(Context::Right(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
                RbTree::Node(parent, grandparent, Color::Red, c, d))
            == plug(up2, RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up2, RbTree::Node(grandparent, above, Color::Red,
            RbTree::Node(uncle, grandparent, Color::Black, a, b),
            RbTree::Node(parent, grandparent, Color::Black, c, d))), 0)
        == rb_parent_consistent(plug(Context::Right(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
            RbTree::Node(parent, grandparent, Color::Red, c, d)), 0) by {
        apply(rb_insert_fix_recolor_shape(grandparent, above, uncle, parent, a, b, c, d));
        apply(plug_insert_fix_recolor_parent_consistent(up2,
            RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d)), 0));
        apply(plug_right_frame(grandparent, above, Color::Black,
            RbTree::Node(uncle, grandparent, Color::Red, a, b), up2,
            RbTree::Node(parent, grandparent, Color::Red, c, d)));
        have RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))) by {
            rewrite(rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                    RbTree::Node(uncle, grandparent, Color::Red, a, b),
                    RbTree::Node(parent, grandparent, Color::Red, c, d)))
                == RbTree::Node(grandparent, above, Color::Red,
                    RbTree::Node(uncle, grandparent, Color::Black, a, b),
                    RbTree::Node(parent, grandparent, Color::Black, c, d)));
            normalize();
        }
        rewrite(RbTree::Node(grandparent, above, Color::Red,
                RbTree::Node(uncle, grandparent, Color::Black, a, b),
                RbTree::Node(parent, grandparent, Color::Black, c, d))
            == rb_insert_fix_recolor(RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))));
        rewrite(plug(Context::Right(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b), up2),
                RbTree::Node(parent, grandparent, Color::Red, c, d))
            == plug(up2, RbTree::Node(grandparent, above, Color::Black,
                RbTree::Node(uncle, grandparent, Color::Red, a, b),
                RbTree::Node(parent, grandparent, Color::Red, c, d))));
        assumption();
    }
}

theorem ctx_insert_case3_left_step(above: struct rb_node*, grandparent: struct rb_node*,
                                   parent: struct rb_node*, cursor: struct rb_node*,
                                   a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, a, b)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(Context::Left(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), black_height(RbTree::Node(cursor, parent, Color::Red, a, b)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Left(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, a, b)), 0) == 1;

    ensures rb_inorder(plug(Context::Left(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(cursor, parent, Color::Red, a, b)))
        == rb_inorder(plug(Context::Left(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, a, b))) by {
        apply(plug_left_frame(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2, RbTree::Node(cursor, parent, Color::Red, a, b)));
        apply(rb_insert_fix_outer_left_shape(grandparent, above, parent, cursor, a, b, c, d));
        apply(plug_insert_fix_outer_left_inorder(up2, RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), d)));
        apply(plug_left_in_left(above, grandparent, parent, Color::Black, Color::Red, c, d, up2, RbTree::Node(cursor, parent, Color::Red, a, b)));
        rewrite(plug(Context::Left(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(cursor, parent, Color::Red, a, b)) == plug(up2, RbTree::Node(parent, above, Color::Black, RbTree::Node(cursor, parent, Color::Red, a, b), RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d))));
        rewrite(plug(Context::Left(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, a, b)) == plug(up2, RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), d)));
        rewrite(RbTree::Node(parent, above, Color::Black, RbTree::Node(cursor, parent, Color::Red, a, b), RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)) == rb_insert_fix_outer_left(RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), d)));
        assumption();
    }

    ensures is_rb_root(plug(Context::Left(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(cursor, parent, Color::Red, a, b))) == 1 by {
        apply(black_height_red_node(cursor, parent, a, b));
        have ctx_rb(Context::Left(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), black_height(a), Color::Black) == 1 by {
            rewrite(black_height(a) == black_height(RbTree::Node(cursor, parent, Color::Red, a, b)));
            assumption();
        }
        apply(ctx_insert_case3_left(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(plug_left_frame(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2, RbTree::Node(cursor, parent, Color::Red, a, b)));
        apply(rb_insert_fix_outer_left_shape(grandparent, above, parent, cursor, a, b, c, d));
        rewrite(plug(Context::Left(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(cursor, parent, Color::Red, a, b)) == plug(up2, RbTree::Node(parent, above, Color::Black, RbTree::Node(cursor, parent, Color::Red, a, b), RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d))));
        rewrite(RbTree::Node(parent, above, Color::Black, RbTree::Node(cursor, parent, Color::Red, a, b), RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)) == rb_insert_fix_outer_left(RbTree::Node(grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), d)));
        assumption();
    }

    ensures rb_parent_consistent(plug(Context::Left(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(cursor, parent, Color::Red, a, b)), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, a, b), 0));
        apply(ctx_consistent_left_focus(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(cursor, parent, Color::Red, a, b), 0));
        apply(ctx_consistent_left_sibling(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(cursor, parent, Color::Red, a, b), 0));
        apply(ctx_consistent_left_up(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2), RbTree::Node(cursor, parent, Color::Red, a, b), 0));
        apply(ctx_consistent_left_sibling(grandparent, above, Color::Black, d, up2, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), 0));
        apply(ctx_consistent_left_up(grandparent, above, Color::Black, d, up2, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), 0));
        apply(rb_reparent_parent_consistent(c, parent, grandparent));
        apply(rb_node_is_reflexive(parent));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d, parent));
        apply(rb_parent_consistent_node(parent, above, Color::Black, RbTree::Node(cursor, parent, Color::Red, a, b), RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), above));
        apply(ctx_consistent_swap(up2, grandparent, above, Color::Black, RbTree::Node(parent, grandparent, Color::Red, RbTree::Node(cursor, parent, Color::Red, a, b), c), d, RbTree::Node(parent, above, Color::Black, RbTree::Node(cursor, parent, Color::Red, a, b), RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d)), 0));
        apply(ctx_consistent_left_frame(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2, RbTree::Node(cursor, parent, Color::Red, a, b), 0));
        apply(plug_parent_consistent_transport(Context::Left(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(cursor, parent, Color::Red, a, b), 0));
        assumption();
    }

    ensures rb_root_black(c) == 1 by {
        apply(ctx_rb_left_colors(parent, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2), black_height(RbTree::Node(cursor, parent, Color::Red, a, b)), Color::Black));
        apply(node_color_ok_red_right(Color::Black, rb_color(c)));
        apply(rb_root_black_is_color_black(c));
        rewrite(rb_root_black(c) == color_black(rb_color(c)));
        assumption();
    }
}

theorem ctx_insert_case3_right_step(above: struct rb_node*, grandparent: struct rb_node*,
                                   parent: struct rb_node*, cursor: struct rb_node*,
                                   a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, c, d)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(Context::Right(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), black_height(RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Right(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, c, d)), 0) == 1;

    ensures rb_inorder(plug(Context::Right(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(cursor, parent, Color::Red, c, d)))
        == rb_inorder(plug(Context::Right(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, c, d))) by {
        apply(plug_right_frame(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2, RbTree::Node(cursor, parent, Color::Red, c, d)));
        apply(rb_insert_fix_outer_right_shape(grandparent, above, parent, cursor, a, b, c, d));
        apply(plug_insert_fix_outer_right_inorder(up2, RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)))));
        apply(plug_right_in_right(above, grandparent, parent, Color::Black, Color::Red, b, a, up2, RbTree::Node(cursor, parent, Color::Red, c, d)));
        rewrite(plug(Context::Right(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(cursor, parent, Color::Red, c, d)) == plug(up2, RbTree::Node(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(cursor, parent, Color::Red, c, d))));
        rewrite(plug(Context::Right(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, c, d)) == plug(up2, RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)))));
        rewrite(RbTree::Node(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(cursor, parent, Color::Red, c, d)) == rb_insert_fix_outer_right(RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)))));
        assumption();
    }

    ensures is_rb_root(plug(Context::Right(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(cursor, parent, Color::Red, c, d))) == 1 by {
        apply(black_height_red_node(cursor, parent, c, d));
        have ctx_rb(Context::Right(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), black_height(c), Color::Black) == 1 by {
            rewrite(black_height(c) == black_height(RbTree::Node(cursor, parent, Color::Red, c, d)));
            assumption();
        }
        apply(ctx_insert_case3_right(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(plug_right_frame(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2, RbTree::Node(cursor, parent, Color::Red, c, d)));
        apply(rb_insert_fix_outer_right_shape(grandparent, above, parent, cursor, a, b, c, d));
        rewrite(plug(Context::Right(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(cursor, parent, Color::Red, c, d)) == plug(up2, RbTree::Node(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(cursor, parent, Color::Red, c, d))));
        rewrite(RbTree::Node(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(cursor, parent, Color::Red, c, d)) == rb_insert_fix_outer_right(RbTree::Node(grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)))));
        assumption();
    }

    ensures rb_parent_consistent(plug(Context::Right(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(cursor, parent, Color::Red, c, d)), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, c, d), 0));
        apply(ctx_consistent_right_focus(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(cursor, parent, Color::Red, c, d), 0));
        apply(ctx_consistent_right_sibling(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(cursor, parent, Color::Red, c, d), 0));
        apply(ctx_consistent_right_up(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2), RbTree::Node(cursor, parent, Color::Red, c, d), 0));
        apply(ctx_consistent_right_sibling(grandparent, above, Color::Black, a, up2, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)), 0));
        apply(ctx_consistent_right_up(grandparent, above, Color::Black, a, up2, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)), 0));
        apply(rb_reparent_parent_consistent(b, parent, grandparent));
        apply(rb_node_is_reflexive(parent));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent), parent));
        apply(rb_parent_consistent_node(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(cursor, parent, Color::Red, c, d), above));
        apply(ctx_consistent_swap(up2, grandparent, above, Color::Black, a, RbTree::Node(parent, grandparent, Color::Red, b, RbTree::Node(cursor, parent, Color::Red, c, d)), RbTree::Node(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(cursor, parent, Color::Red, c, d)), 0));
        apply(ctx_consistent_right_frame(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2, RbTree::Node(cursor, parent, Color::Red, c, d), 0));
        apply(plug_parent_consistent_transport(Context::Right(parent, above, Color::Black, RbTree::Node(grandparent, parent, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(cursor, parent, Color::Red, c, d), 0));
        assumption();
    }

    ensures rb_root_black(b) == 1 by {
        apply(ctx_rb_right_colors(parent, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2), black_height(RbTree::Node(cursor, parent, Color::Red, c, d)), Color::Black));
        apply(node_color_ok_red_left(rb_color(b), Color::Black));
        apply(rb_root_black_is_color_black(b));
        rewrite(rb_root_black(b) == color_black(rb_color(b)));
        assumption();
    }
}

theorem ctx_insert_case2_left_exit_step(above: struct rb_node*, grandparent: struct rb_node*,
                                        parent: struct rb_node*, cursor: struct rb_node*,
                                        a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(d) == 1;
    requires ctx_rb(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, b, c)), 0) == 1;

    ensures rb_inorder(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d))))
        == rb_inorder(plug(Context::Right(parent, grandparent, Color::Red, a, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(cursor, parent, Color::Red, b, c))) by {
        apply(ctx_insert_case2_left_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_left_step(above, grandparent, cursor, parent, a, rb_reparent(b, parent), c, d, up2));
        apply(plug_left_frame(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        rewrite(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d))) == plug(Context::Left(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        rewrite(rb_inorder(plug(Context::Left(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)))) == rb_inorder(plug(Context::Left(cursor, grandparent, Color::Red, c, Context::Left(grandparent, above, Color::Black, d, up2)), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)))));
        assumption();
    }

    ensures is_rb_root(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d)))) == 1 by {
        apply(ctx_insert_case2_left_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_left_step(above, grandparent, cursor, parent, a, rb_reparent(b, parent), c, d, up2));
        apply(plug_left_frame(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        rewrite(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d))) == plug(Context::Left(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d))), 0) == 1 by {
        apply(ctx_insert_case2_left_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_left_step(above, grandparent, cursor, parent, a, rb_reparent(b, parent), c, d, up2));
        apply(plug_left_frame(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        rewrite(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent)), RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d))) == plug(Context::Left(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, rb_reparent(c, grandparent), d), up2), RbTree::Node(parent, cursor, Color::Red, a, rb_reparent(b, parent))));
        assumption();
    }

    ensures rb_root_black(b) == 1 by {
        apply(ctx_insert_case2_left_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        assumption();
    }

    ensures rb_root_black(c) == 1 by {
        apply(ctx_insert_case2_left_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_left_step(above, grandparent, cursor, parent, a, rb_reparent(b, parent), c, d, up2));
        assumption();
    }
}

theorem ctx_insert_case2_right_exit_step(above: struct rb_node*, grandparent: struct rb_node*,
                                         parent: struct rb_node*, cursor: struct rb_node*,
                                         a: RbTree, b: RbTree, c: RbTree, d: RbTree, up2: Context) {
    requires is_rb(RbTree::Node(cursor, parent, Color::Red, b, c)) == 1;
    requires rb_root_black(a) == 1;
    requires ctx_rb(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), black_height(RbTree::Node(cursor, parent, Color::Red, b, c)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, b, c)), 0) == 1;

    ensures rb_inorder(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))))
        == rb_inorder(plug(Context::Left(parent, grandparent, Color::Red, d, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(cursor, parent, Color::Red, b, c))) by {
        apply(ctx_insert_case2_right_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_right_step(above, grandparent, cursor, parent, a, b, rb_reparent(c, parent), d, up2));
        apply(plug_right_frame(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        rewrite(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) == plug(Context::Right(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        rewrite(rb_inorder(plug(Context::Right(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) == rb_inorder(plug(Context::Right(cursor, grandparent, Color::Red, b, Context::Right(grandparent, above, Color::Black, a, up2)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))));
        assumption();
    }

    ensures is_rb_root(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)))) == 1 by {
        apply(ctx_insert_case2_right_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_right_step(above, grandparent, cursor, parent, a, b, rb_reparent(c, parent), d, up2));
        apply(plug_right_frame(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        rewrite(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) == plug(Context::Right(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        assumption();
    }

    ensures rb_parent_consistent(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))), 0) == 1 by {
        apply(ctx_insert_case2_right_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_right_step(above, grandparent, cursor, parent, a, b, rb_reparent(c, parent), d, up2));
        apply(plug_right_frame(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2, RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        rewrite(plug(up2, RbTree::Node(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d))) == plug(Context::Right(cursor, above, Color::Black, RbTree::Node(grandparent, cursor, Color::Red, a, rb_reparent(b, grandparent)), up2), RbTree::Node(parent, cursor, Color::Red, rb_reparent(c, parent), d)));
        assumption();
    }

    ensures rb_root_black(c) == 1 by {
        apply(ctx_insert_case2_right_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        assumption();
    }

    ensures rb_root_black(b) == 1 by {
        apply(ctx_insert_case2_right_step(above, grandparent, parent, cursor, a, b, c, d, up2));
        apply(ctx_insert_case3_right_step(above, grandparent, cursor, parent, a, b, rb_reparent(c, parent), d, up2));
        assumption();
    }
}

theorem rb_inorder_node_congruence(node: struct rb_node*, parent: struct rb_node*,
                                   left_color: Color, right_color: Color,
                                   left1: RbTree, left2: RbTree,
                                   right1: RbTree, right2: RbTree) {
    requires rb_inorder(left1) == rb_inorder(left2);
    requires rb_inorder(right1) == rb_inorder(right2);

    ensures rb_inorder(RbTree::Node(node, parent, left_color, left1, right1))
        == rb_inorder(RbTree::Node(node, parent, right_color, left2, right2)) by {
        apply(rb_inorder_node_splits(node, parent, left_color, left1, right1));
        apply(rb_inorder_node_splits(node, parent, right_color, left2, right2));
        rewrite(rb_inorder(RbTree::Node(node, parent, left_color, left1, right1))
            == list_append(rb_inorder(left1),
                List<struct rb_node*>::Cons(node, rb_inorder(right1))));
        rewrite(rb_inorder(RbTree::Node(node, parent, right_color, left2, right2))
            == list_append(rb_inorder(left2),
                List<struct rb_node*>::Cons(node, rb_inorder(right2))));
        rewrite(rb_inorder(left1) == rb_inorder(left2));
        rewrite(rb_inorder(right1) == rb_inorder(right2));
        normalize();
    }
}

theorem ctx_rb_black_focus(ctx: Context, bh: Nat, focus_color: Color) {
    requires ctx_rb(ctx, bh, focus_color) == 1;

    ensures ctx_rb(ctx, bh, Color::Black) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                apply(color_black_black());
                apply(ctx_rb_top_frame(bh, Color::Black));
                assumption();
            }
            Context::Left(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_left_sibling(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(ctx_rb_left_height(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(ctx_rb_left_colors(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(ctx_rb_left_up(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(node_color_ok_weaken_left(color, focus_color, rb_color(sibling_model)));
                apply(ctx_rb_left_frame(identity, grandparent, color, sibling_model,
                    up_model, bh, Color::Black));
                assumption();
            }
            Context::Right(identity, grandparent, color, sibling_model, up_model) => {
                apply(ctx_rb_right_sibling(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(ctx_rb_right_height(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(ctx_rb_right_colors(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(ctx_rb_right_up(identity, grandparent, color, sibling_model,
                    up_model, bh, focus_color));
                apply(node_color_ok_weaken_right(color, rb_color(sibling_model), focus_color));
                apply(ctx_rb_right_frame(identity, grandparent, color, sibling_model,
                    up_model, bh, Color::Black));
                assumption();
            }
        }
    }
}

// The black sibling of an erase cursor whose children are both black, made
// red: what `rb_set_parent_color(sibling, parent, RB_RED)` leaves in case 2.
theorem ctx_erase_case2_left_sibling(parent: struct rb_node*, sibling: struct rb_node*,
                                     cursor_bh: Nat, sl: RbTree, sr: RbTree) {
    requires is_rb(RbTree::Node(sibling, parent, Color::Black, sl, sr)) == 1;
    requires Nat::Succ(cursor_bh)
        == black_height(RbTree::Node(sibling, parent, Color::Black, sl, sr));
    requires rb_root_black(sl) == 1;
    requires rb_root_black(sr) == 1;

    ensures is_rb(RbTree::Node(sibling, parent, Color::Red, sl, sr)) == 1 by {
        apply(is_rb_node_left(sibling, parent, Color::Black, sl, sr));
        apply(is_rb_node_right(sibling, parent, Color::Black, sl, sr));
        apply(is_rb_node_black_heights(sibling, parent, Color::Black, sl, sr));
        apply(is_rb_red_node(sibling, parent, sl, sr));
        assumption();
    }

    ensures cursor_bh == black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr)) by {
        apply(black_height_black_node(sibling, parent, sl, sr));
        apply(black_height_red_node(sibling, parent, sl, sr));
        rewrite(black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr))
            == black_height(sl));
        have Nat::Succ(cursor_bh) == Nat::Succ(black_height(sl)) by auto;
        extract(cursor_bh == black_height(sl));
    }
}

theorem ctx_erase_case2_left_red_exit(above: struct rb_node*, parent: struct rb_node*,
                                     sibling: struct rb_node*, t: RbTree, sl: RbTree,
                                     sr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Left(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), Nat::Succ(black_height(t)), Color::Black) == 1;
    requires rb_root_black(sl) == 1;
    requires rb_root_black(sr) == 1;
    requires rb_parent_consistent(plug(Context::Left(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))))
        == rb_inorder(plug(Context::Left(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t)) by {
        apply(plug_left_frame(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t));
        apply(rb_inorder_node_congruence(sibling, parent, Color::Red, Color::Black,
            sl, sl, sr, sr));
        apply(rb_inorder_node_congruence(parent, above, Color::Black, Color::Red, t, t, RbTree::Node(sibling, parent, Color::Red, sl, sr), RbTree::Node(sibling, parent, Color::Black, sl, sr)));
        apply(plug_inorder_transport(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)), RbTree::Node(parent, above, Color::Red, t, RbTree::Node(sibling, parent, Color::Black, sl, sr))));
        rewrite(plug(Context::Left(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t) == plug(up, RbTree::Node(parent, above, Color::Red, t, RbTree::Node(sibling, parent, Color::Black, sl, sr))));
        assumption();
    }

    ensures is_rb_root(plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)))) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_height(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_erase_case2_left_sibling(parent, sibling, black_height(t), sl, sr));
        apply(is_rb_black_node(parent, above, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        apply(black_height_black_node(parent, above, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        apply(rb_color_node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        apply(ctx_rb_left_red_up(parent, above, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_black_focus(up, Nat::Succ(black_height(t)), Color::Red));
        have ctx_rb(up, black_height(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))), rb_color(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)))) == 1 by {
            rewrite(black_height(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == Nat::Succ(black_height(t)));
            rewrite(rb_color(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t, 0));
        apply(ctx_consistent_left_focus(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_left_sibling(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_left_up(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_parent(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr), above));
        apply(ctx_consistent_swap(up, parent, above, Color::Red, t, RbTree::Node(sibling, parent, Color::Black, sl, sr), RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)), 0));
        assumption();
    }
}

theorem ctx_erase_case2_right_red_exit(above: struct rb_node*, parent: struct rb_node*,
                                     sibling: struct rb_node*, t: RbTree, sl: RbTree,
                                     sr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Right(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), Nat::Succ(black_height(t)), Color::Black) == 1;
    requires rb_root_black(sl) == 1;
    requires rb_root_black(sr) == 1;
    requires rb_parent_consistent(plug(Context::Right(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)))
        == rb_inorder(plug(Context::Right(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t)) by {
        apply(plug_right_frame(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t));
        apply(rb_inorder_node_congruence(sibling, parent, Color::Red, Color::Black,
            sl, sl, sr, sr));
        apply(rb_inorder_node_congruence(parent, above, Color::Black, Color::Red, RbTree::Node(sibling, parent, Color::Red, sl, sr), RbTree::Node(sibling, parent, Color::Black, sl, sr), t, t));
        apply(plug_inorder_transport(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t), RbTree::Node(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), t)));
        rewrite(plug(Context::Right(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t) == plug(up, RbTree::Node(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), t)));
        assumption();
    }

    ensures is_rb_root(plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t))) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_right_height(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(nat_eq_symmetric(black_height(RbTree::Node(sibling, parent, Color::Black, sl, sr)), Nat::Succ(black_height(t))));
        apply(ctx_erase_case2_left_sibling(parent, sibling, black_height(t), sl, sr));
        apply(nat_eq_symmetric(black_height(t), black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr))));
        apply(is_rb_black_node(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        apply(black_height_black_node(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        have black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Nat::Succ(black_height(t)) by {
            rewrite(black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Nat::Succ(black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr))));
            rewrite(black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr)) == black_height(t));
            normalize();
        }
        apply(rb_color_node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        apply(ctx_rb_right_red_up(parent, above, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_black_focus(up, Nat::Succ(black_height(t)), Color::Red));
        have ctx_rb(up, black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)), rb_color(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t))) == 1 by {
            rewrite(black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Nat::Succ(black_height(t)));
            rewrite(rb_color(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t, 0));
        apply(ctx_consistent_right_focus(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_right_sibling(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_right_up(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_parent(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t, above));
        apply(ctx_consistent_swap(up, parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Black, sl, sr), t, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t), 0));
        assumption();
    }
}

theorem ctx_erase_case2_left_black_step(above: struct rb_node*, parent: struct rb_node*,
                                       sibling: struct rb_node*, t: RbTree, sl: RbTree,
                                       sr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), Nat::Succ(black_height(t)), Color::Black) == 1;
    requires rb_root_black(sl) == 1;
    requires rb_root_black(sr) == 1;
    requires rb_parent_consistent(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))))
        == rb_inorder(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t)) by {
        apply(plug_left_frame(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t));
        apply(rb_inorder_node_congruence(sibling, parent, Color::Red, Color::Black,
            sl, sl, sr, sr));
        apply(rb_inorder_node_congruence(parent, above, Color::Black, Color::Black, t, t, RbTree::Node(sibling, parent, Color::Red, sl, sr), RbTree::Node(sibling, parent, Color::Black, sl, sr)));
        apply(plug_inorder_transport(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)), RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Black, sl, sr))));
        rewrite(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t) == plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Black, sl, sr))));
        assumption();
    }

    ensures is_rb(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_height(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_erase_case2_left_sibling(parent, sibling, black_height(t), sl, sr));
        apply(is_rb_black_node(parent, above, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        assumption();
    }

    ensures rb_root_black(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == 1 by {
        apply(rb_root_black_black_node(parent, above, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        assumption();
    }

    ensures ctx_rb(up, Nat::Succ(black_height(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)))), Color::Black) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_height(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_erase_case2_left_sibling(parent, sibling, black_height(t), sl, sr));
        apply(black_height_black_node(parent, above, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        apply(ctx_rb_left_black_up(parent, above, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        rewrite(black_height(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == Nat::Succ(black_height(t)));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t, 0));
        apply(ctx_consistent_left_focus(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_left_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_left_up(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_parent(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr), above));
        apply(ctx_consistent_swap(up, parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Black, sl, sr), RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)), 0));
        assumption();
    }
}

theorem ctx_erase_case2_right_black_step(above: struct rb_node*, parent: struct rb_node*,
                                       sibling: struct rb_node*, t: RbTree, sl: RbTree,
                                       sr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), Nat::Succ(black_height(t)), Color::Black) == 1;
    requires rb_root_black(sl) == 1;
    requires rb_root_black(sr) == 1;
    requires rb_parent_consistent(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)))
        == rb_inorder(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t)) by {
        apply(plug_right_frame(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t));
        apply(rb_inorder_node_congruence(sibling, parent, Color::Red, Color::Black,
            sl, sl, sr, sr));
        apply(rb_inorder_node_congruence(parent, above, Color::Black, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), RbTree::Node(sibling, parent, Color::Black, sl, sr), t, t));
        apply(plug_inorder_transport(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t), RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), t)));
        rewrite(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t) == plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), t)));
        assumption();
    }

    ensures is_rb(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_right_height(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(nat_eq_symmetric(black_height(RbTree::Node(sibling, parent, Color::Black, sl, sr)), Nat::Succ(black_height(t))));
        apply(ctx_erase_case2_left_sibling(parent, sibling, black_height(t), sl, sr));
        apply(nat_eq_symmetric(black_height(t), black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr))));
        apply(is_rb_black_node(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        assumption();
    }

    ensures rb_root_black(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == 1 by {
        apply(rb_root_black_black_node(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        assumption();
    }

    ensures ctx_rb(up, Nat::Succ(black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t))), Color::Black) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_right_height(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(nat_eq_symmetric(black_height(RbTree::Node(sibling, parent, Color::Black, sl, sr)), Nat::Succ(black_height(t))));
        apply(ctx_erase_case2_left_sibling(parent, sibling, black_height(t), sl, sr));
        apply(black_height_black_node(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        have black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Nat::Succ(black_height(t)) by {
            rewrite(black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Nat::Succ(black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr))));
            rewrite(black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr)) == black_height(t));
            normalize();
        }
        apply(ctx_rb_right_black_up(parent, above, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        rewrite(black_height(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == Nat::Succ(black_height(t)));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up), t, 0));
        apply(ctx_consistent_right_focus(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_right_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(ctx_consistent_right_up(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node_parent(sibling, parent, Color::Black, sl, sr, parent));
        apply(rb_parent_consistent_node(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t, above));
        apply(ctx_consistent_swap(up, parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Black, sl, sr), t, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t), 0));
        assumption();
    }
}

theorem ctx_erase_root_exit(t: RbTree) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;

    ensures is_rb_root(plug(Context::Top, t)) == 1 by {
        apply(is_rb_root_from_parts(t));
        unfold(plug(Context::Top, t));
        assumption();
    }
}

theorem ctx_erase_case1_left_parent_black(above: struct rb_node*, parent: struct rb_node*,
                                         pcolor: Color, sibling: struct rb_node*, sl: RbTree,
                                         sr: RbTree, up: Context, bh: Nat) {
    requires ctx_rb(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), bh, Color::Black) == 1;

    ensures pcolor == Color::Black by {
        induct(pcolor) as ih {
            Color::Red => {
                apply(ctx_rb_left_colors(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, bh, Color::Black));
                apply(rb_color_node(sibling, parent, Color::Red, sl, sr));
                have node_color_ok(Color::Red, Color::Black, Color::Red) != 1 by {
                    unfold(node_color_ok(Color::Red, Color::Black, Color::Red));
                    unfold(color_black(Color::Black));
                    unfold(color_black(Color::Red));
                    normalize();
                }
                have node_color_ok(Color::Red, Color::Black, rb_color(RbTree::Node(sibling, parent, Color::Red, sl, sr))) != 1 by {
                    rewrite(rb_color(RbTree::Node(sibling, parent, Color::Red, sl, sr)) == Color::Red);
                    assumption();
                }
                contradiction(node_color_ok(Color::Red, Color::Black, rb_color(RbTree::Node(sibling, parent, Color::Red, sl, sr))) == 1);
            }
            Color::Black => {
                normalize();
            }
        }
    }
}

theorem ctx_erase_case1_left_step(above: struct rb_node*, parent: struct rb_node*,
                                 sibling: struct rb_node*, t: RbTree, sl: RbTree,
                                 sr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), Nat::Succ(black_height(t)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t), 0) == 1;

    ensures ctx_rb(Context::Left(parent, sibling, Color::Red, rb_reparent(sl, parent), Context::Left(sibling, above, Color::Black, sr, up)), Nat::Succ(black_height(t)), Color::Black) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_height(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_black_up(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_node_left(sibling, parent, Color::Red, sl, sr));
        apply(is_rb_node_right(sibling, parent, Color::Red, sl, sr));
        apply(is_rb_node_black_heights(sibling, parent, Color::Red, sl, sr));
        apply(black_height_red_node(sibling, parent, sl, sr));
        apply(is_rb_red_node_children_are_black(sibling, parent, sl, sr));
        apply(is_rb_red_node_right_child_is_black(sibling, parent, sl, sr));
        have Nat::Succ(black_height(t)) == black_height(sl) by {
            rewrite(black_height(sl) == black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr)));
            assumption();
        }
        have Nat::Succ(black_height(t)) == black_height(sr) by auto;
        apply(rb_reparent_preserves_is_rb(sl, parent));
        apply(rb_reparent_preserves_black_height(sl, parent));
        apply(rb_reparent_preserves_rb_root_black(sl, parent));
        apply(node_color_ok_black(Color::Red, rb_color(sr)));
        apply(frame_black_height_black(Nat::Succ(black_height(t))));
        have ctx_rb(up, frame_black_height(Color::Black, Nat::Succ(black_height(t))), Color::Black) == 1 by {
            rewrite(frame_black_height(Color::Black, Nat::Succ(black_height(t))) == Nat::Succ(Nat::Succ(black_height(t))));
            assumption();
        }
        apply(ctx_rb_left_frame(sibling, above, Color::Black, sr, up, Nat::Succ(black_height(t)), Color::Red));
        apply(color_black_of_rb_color(rb_reparent(sl, parent)));
        have color_black(rb_color(rb_reparent(sl, parent))) == 1 by auto;
        apply(color_black_black());
        apply(node_color_ok_red(Color::Black, rb_color(rb_reparent(sl, parent))));
        have is_rb(rb_reparent(sl, parent)) == 1 by {
            rewrite(is_rb(rb_reparent(sl, parent)) == is_rb(sl));
            assumption();
        }
        have Nat::Succ(black_height(t)) == black_height(rb_reparent(sl, parent)) by {
            rewrite(black_height(rb_reparent(sl, parent)) == black_height(sl));
            assumption();
        }
        apply(frame_black_height_red(Nat::Succ(black_height(t))));
        have ctx_rb(Context::Left(sibling, above, Color::Black, sr, up),
            frame_black_height(Color::Red, Nat::Succ(black_height(t))), Color::Red) == 1 by {
            rewrite(frame_black_height(Color::Red, Nat::Succ(black_height(t))) == Nat::Succ(black_height(t)));
            assumption();
        }
        apply(ctx_rb_left_frame(parent, sibling, Color::Red, rb_reparent(sl, parent),
            Context::Left(sibling, above, Color::Black, sr, up), Nat::Succ(black_height(t)), Color::Black));
        assumption();
    }

    ensures rb_root_black(rb_reparent(sl, parent)) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_red_node_children_are_black(sibling, parent, sl, sr));
        apply(rb_reparent_preserves_rb_root_black(sl, parent));
        rewrite(rb_root_black(rb_reparent(sl, parent)) == rb_root_black(sl));
        assumption();
    }

    ensures rb_inorder(plug(Context::Left(parent, sibling, Color::Red, rb_reparent(sl, parent), Context::Left(sibling, above, Color::Black, sr, up)), t)) == rb_inorder(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t)) by {
        apply(plug_left_in_left(above, sibling, parent, Color::Black, Color::Red, rb_reparent(sl, parent), sr, up, t));
        apply(plug_left_frame(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t));
        have rb_rotate_left(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == RbTree::Node(sibling, above, Color::Red, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(sl, parent)), sr) by auto;
        apply(rb_rotate_left_node_preserves_inorder(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)));
        apply(rb_inorder_node_congruence(parent, sibling, Color::Red, Color::Black, t, t, rb_reparent(sl, parent), rb_reparent(sl, parent)));
        apply(rb_inorder_node_congruence(sibling, above, Color::Black, Color::Red, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(sl, parent)), sr, sr));
        have rb_inorder(RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr)) == rb_inorder(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) by {
            rewrite(rb_inorder(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == rb_inorder(rb_rotate_left(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr)))));
            rewrite(rb_rotate_left(RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))) == RbTree::Node(sibling, above, Color::Red, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(sl, parent)), sr));
            assumption();
        }
        apply(plug_inorder_transport(up, RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr), RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))));
        rewrite(plug(Context::Left(parent, sibling, Color::Red, rb_reparent(sl, parent), Context::Left(sibling, above, Color::Black, sr, up)), t) == plug(up, RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr)));
        rewrite(plug(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t) == plug(up, RbTree::Node(parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr))));
        assumption();
    }

    ensures rb_parent_consistent(plug(Context::Left(parent, sibling, Color::Red, rb_reparent(sl, parent), Context::Left(sibling, above, Color::Black, sr, up)), t), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t, 0));
        apply(ctx_consistent_left_focus(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t, 0));
        apply(ctx_consistent_left_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t, 0));
        apply(ctx_consistent_left_up(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_reparent_parent_consistent(sl, sibling, parent));
        apply(rb_node_is_reflexive(sibling));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, sibling, Color::Red, t, rb_reparent(sl, parent), sibling));
        apply(rb_parent_consistent_node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr, above));
        apply(ctx_consistent_swap(up, parent, above, Color::Black, t, RbTree::Node(sibling, parent, Color::Red, sl, sr), RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr), 0));
        apply(plug_left_in_left(above, sibling, parent, Color::Black, Color::Red, rb_reparent(sl, parent), sr, up, t));
        rewrite(plug(Context::Left(parent, sibling, Color::Red, rb_reparent(sl, parent), Context::Left(sibling, above, Color::Black, sr, up)), t) == plug(up, RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, Color::Red, t, rb_reparent(sl, parent)), sr)));
        assumption();
    }
}

theorem ctx_erase_case1_right_parent_black(above: struct rb_node*, parent: struct rb_node*,
                                         pcolor: Color, sibling: struct rb_node*, sl: RbTree,
                                         sr: RbTree, up: Context, bh: Nat) {
    requires ctx_rb(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), bh, Color::Black) == 1;

    ensures pcolor == Color::Black by {
        induct(pcolor) as ih {
            Color::Red => {
                apply(ctx_rb_right_colors(parent, above, Color::Red, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, bh, Color::Black));
                apply(rb_color_node(sibling, parent, Color::Red, sl, sr));
                have node_color_ok(Color::Red, Color::Red, Color::Black) != 1 by {
                    unfold(node_color_ok(Color::Red, Color::Red, Color::Black));
                    unfold(color_black(Color::Black));
                    unfold(color_black(Color::Red));
                    normalize();
                }
                have node_color_ok(Color::Red, rb_color(RbTree::Node(sibling, parent, Color::Red, sl, sr)), Color::Black) != 1 by {
                    rewrite(rb_color(RbTree::Node(sibling, parent, Color::Red, sl, sr)) == Color::Red);
                    assumption();
                }
                contradiction(node_color_ok(Color::Red, rb_color(RbTree::Node(sibling, parent, Color::Red, sl, sr)), Color::Black) == 1);
            }
            Color::Black => {
                normalize();
            }
        }
    }
}

theorem ctx_erase_case1_right_step(above: struct rb_node*, parent: struct rb_node*,
                                 sibling: struct rb_node*, t: RbTree, sl: RbTree,
                                 sr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), Nat::Succ(black_height(t)), Color::Black) == 1;
    requires rb_parent_consistent(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t), 0) == 1;

    ensures ctx_rb(Context::Right(parent, sibling, Color::Red, rb_reparent(sr, parent), Context::Right(sibling, above, Color::Black, sl, up)), Nat::Succ(black_height(t)), Color::Black) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_right_height(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(nat_eq_symmetric(black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr)), Nat::Succ(black_height(t))));
        apply(ctx_rb_right_black_up(parent, above, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_node_left(sibling, parent, Color::Red, sl, sr));
        apply(is_rb_node_right(sibling, parent, Color::Red, sl, sr));
        apply(is_rb_node_black_heights(sibling, parent, Color::Red, sl, sr));
        apply(black_height_red_node(sibling, parent, sl, sr));
        apply(is_rb_red_node_right_child_is_black(sibling, parent, sl, sr));
        apply(is_rb_red_node_children_are_black(sibling, parent, sl, sr));
        have Nat::Succ(black_height(t)) == black_height(sl) by {
            rewrite(black_height(sl) == black_height(RbTree::Node(sibling, parent, Color::Red, sl, sr)));
            assumption();
        }
        have Nat::Succ(black_height(t)) == black_height(sr) by auto;
        apply(rb_reparent_preserves_is_rb(sr, parent));
        apply(rb_reparent_preserves_black_height(sr, parent));
        apply(rb_reparent_preserves_rb_root_black(sr, parent));
        apply(node_color_ok_black(rb_color(sl), Color::Red));
        apply(frame_black_height_black(Nat::Succ(black_height(t))));
        have ctx_rb(up, frame_black_height(Color::Black, Nat::Succ(black_height(t))), Color::Black) == 1 by {
            rewrite(frame_black_height(Color::Black, Nat::Succ(black_height(t))) == Nat::Succ(Nat::Succ(black_height(t))));
            assumption();
        }
        apply(nat_eq_symmetric(Nat::Succ(black_height(t)), black_height(sl)));
        apply(ctx_rb_right_frame(sibling, above, Color::Black, sl, up, Nat::Succ(black_height(t)), Color::Red));
        apply(color_black_of_rb_color(rb_reparent(sr, parent)));
        have color_black(rb_color(rb_reparent(sr, parent))) == 1 by auto;
        apply(color_black_black());
        apply(node_color_ok_red(rb_color(rb_reparent(sr, parent)), Color::Black));
        have is_rb(rb_reparent(sr, parent)) == 1 by auto;
        have black_height(rb_reparent(sr, parent)) == Nat::Succ(black_height(t)) by auto;
        apply(frame_black_height_red(Nat::Succ(black_height(t))));
        have ctx_rb(Context::Right(sibling, above, Color::Black, sl, up),
            frame_black_height(Color::Red, Nat::Succ(black_height(t))), Color::Red) == 1 by {
            rewrite(frame_black_height(Color::Red, Nat::Succ(black_height(t))) == Nat::Succ(black_height(t)));
            assumption();
        }
        apply(ctx_rb_right_frame(parent, sibling, Color::Red, rb_reparent(sr, parent),
            Context::Right(sibling, above, Color::Black, sl, up), Nat::Succ(black_height(t)), Color::Black));
        assumption();
    }

    ensures rb_root_black(rb_reparent(sr, parent)) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_red_node_right_child_is_black(sibling, parent, sl, sr));
        apply(rb_reparent_preserves_rb_root_black(sr, parent));
        rewrite(rb_root_black(rb_reparent(sr, parent)) == rb_root_black(sr));
        assumption();
    }

    ensures rb_inorder(plug(Context::Right(parent, sibling, Color::Red, rb_reparent(sr, parent), Context::Right(sibling, above, Color::Black, sl, up)), t)) == rb_inorder(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t)) by {
        apply(plug_right_in_right(above, sibling, parent, Color::Black, Color::Red, rb_reparent(sr, parent), sl, up, t));
        apply(plug_right_frame(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t));
        have rb_rotate_right(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == RbTree::Node(sibling, above, Color::Red, sl, RbTree::Node(parent, sibling, Color::Black, rb_reparent(sr, parent), t)) by auto;
        apply(rb_rotate_right_node_preserves_inorder(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t));
        apply(rb_inorder_node_congruence(parent, sibling, Color::Red, Color::Black, rb_reparent(sr, parent), rb_reparent(sr, parent), t, t));
        apply(rb_inorder_node_congruence(sibling, above, Color::Black, Color::Red, sl, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t), RbTree::Node(parent, sibling, Color::Black, rb_reparent(sr, parent), t)));
        have rb_inorder(RbTree::Node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t))) == rb_inorder(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) by {
            rewrite(rb_inorder(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == rb_inorder(rb_rotate_right(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t))));
            rewrite(rb_rotate_right(RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)) == RbTree::Node(sibling, above, Color::Red, sl, RbTree::Node(parent, sibling, Color::Black, rb_reparent(sr, parent), t)));
            assumption();
        }
        apply(plug_inorder_transport(up, RbTree::Node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t)), RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)));
        rewrite(plug(Context::Right(parent, sibling, Color::Red, rb_reparent(sr, parent), Context::Right(sibling, above, Color::Black, sl, up)), t) == plug(up, RbTree::Node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t))));
        rewrite(plug(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t) == plug(up, RbTree::Node(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t)));
        assumption();
    }

    ensures rb_parent_consistent(plug(Context::Right(parent, sibling, Color::Red, rb_reparent(sr, parent), Context::Right(sibling, above, Color::Black, sl, up)), t), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up), t, 0));
        apply(ctx_consistent_right_focus(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t, 0));
        apply(ctx_consistent_right_sibling(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t, 0));
        apply(ctx_consistent_right_up(parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Red, sl, sr, parent));
        apply(rb_reparent_parent_consistent(sr, sibling, parent));
        apply(rb_node_is_reflexive(sibling));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, sibling, Color::Red, rb_reparent(sr, parent), t, sibling));
        apply(rb_parent_consistent_node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t), above));
        apply(ctx_consistent_swap(up, parent, above, Color::Black, RbTree::Node(sibling, parent, Color::Red, sl, sr), t, RbTree::Node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t)), 0));
        apply(plug_right_in_right(above, sibling, parent, Color::Black, Color::Red, rb_reparent(sr, parent), sl, up, t));
        rewrite(plug(Context::Right(parent, sibling, Color::Red, rb_reparent(sr, parent), Context::Right(sibling, above, Color::Black, sl, up)), t) == plug(up, RbTree::Node(sibling, above, Color::Black, sl, RbTree::Node(parent, sibling, Color::Red, rb_reparent(sr, parent), t))));
        assumption();
    }
}

theorem node_color_ok_black_children(color: Color) {
    ensures node_color_ok(color, Color::Black, Color::Black) == 1 by {
        induct(color) as ih {
            Color::Red => {
                apply(color_black_black());
                apply(node_color_ok_red(Color::Black, Color::Black));
                assumption();
            }
            Color::Black => {
                apply(node_color_ok_black(Color::Black, Color::Black));
                assumption();
            }
        }
    }
}

theorem ctx_erase_case4_left_exit(above: struct rb_node*, parent: struct rb_node*, pcolor: Color,
                                 sibling: struct rb_node*, red: struct rb_node*, t: RbTree,
                                 near: RbTree, rl: RbTree, rr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), Nat::Succ(black_height(t)), Color::Black) == 1;

    requires rb_parent_consistent(plug(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)))) == rb_inorder(plug(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t)) by {
        apply(plug_left_frame(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t));
        have rb_rotate_left(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)))) == RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, pcolor, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Red, rl, rr)) by auto;
        apply(rb_rotate_left_node_preserves_inorder(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr))));
        apply(rb_inorder_node_congruence(parent, sibling, Color::Black, pcolor, t, t, rb_reparent(near, parent), rb_reparent(near, parent)));
        apply(rb_inorder_node_congruence(red, sibling, Color::Black, Color::Red, rl, rl, rr, rr));
        apply(rb_inorder_node_congruence(sibling, above, pcolor, Color::Black,
            RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(parent, sibling, pcolor, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(red, sibling, Color::Red, rl, rr)));
        have rb_inorder(RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr))) == rb_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)))) by {
            rewrite(rb_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)))) == rb_inorder(rb_rotate_left(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr))))));
            rewrite(rb_rotate_left(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)))) == RbTree::Node(sibling, above, Color::Black, RbTree::Node(parent, sibling, pcolor, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Red, rl, rr)));
            assumption();
        }
        apply(plug_inorder_transport(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)), RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)))));
        rewrite(plug(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t) == plug(up, RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)))));
        assumption();
    }

    ensures is_rb_root(plug(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)))) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_height(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_node_left(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(is_rb_node_right(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(is_rb_node_black_heights(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(black_height_black_node(sibling, parent, near, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(is_rb_node_left(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_right(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_black_heights(red, sibling, Color::Red, rl, rr));
        apply(black_height_red_node(red, sibling, rl, rr));
        have black_height(t) == black_height(near) by {
            have Nat::Succ(black_height(t)) == Nat::Succ(black_height(near)) by {
                rewrite(Nat::Succ(black_height(near)) == black_height(RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr))));
                assumption();
            }
            extract(black_height(t) == black_height(near));
        }
        apply(rb_reparent_preserves_is_rb(near, parent));
        apply(rb_reparent_preserves_black_height(near, parent));
        have is_rb(rb_reparent(near, parent)) == 1 by auto;
        have black_height(t) == black_height(rb_reparent(near, parent)) by {
            rewrite(black_height(rb_reparent(near, parent)) == black_height(near));
            assumption();
        }
        apply(is_rb_black_node(parent, sibling, t, rb_reparent(near, parent)));
        apply(is_rb_black_node(red, sibling, rl, rr));
        apply(black_height_black_node(parent, sibling, t, rb_reparent(near, parent)));
        apply(black_height_black_node(red, sibling, rl, rr));
        have black_height(RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent))) == black_height(RbTree::Node(red, sibling, Color::Black, rl, rr)) by {
            rewrite(black_height(RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent))) == Nat::Succ(black_height(t)));
            rewrite(black_height(RbTree::Node(red, sibling, Color::Black, rl, rr)) == Nat::Succ(black_height(rl)));
            rewrite(black_height(t) == black_height(near));
            rewrite(black_height(rl) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            rewrite(black_height(near) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            normalize();
        }
        apply(rb_color_node(parent, sibling, Color::Black, t, rb_reparent(near, parent)));
        apply(rb_color_node(red, sibling, Color::Black, rl, rr));
        apply(node_color_ok_black_children(pcolor));
        have node_color_ok(pcolor, rb_color(RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent))), rb_color(RbTree::Node(red, sibling, Color::Black, rl, rr))) == 1 by {
            rewrite(rb_color(RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent))) == Color::Black);
            rewrite(rb_color(RbTree::Node(red, sibling, Color::Black, rl, rr)) == Color::Black);
            assumption();
        }
        apply(is_rb_node_from_parts(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)));
        apply(black_height_node_frame(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)));
        apply(rb_color_node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)));
        have ctx_rb(up, black_height(RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr))), rb_color(RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)))) == 1 by {
            rewrite(black_height(RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr))) == frame_black_height(pcolor, black_height(RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)))));
            rewrite(black_height(RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent))) == Nat::Succ(black_height(t)));
            rewrite(rb_color(RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr))) == pcolor);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t, 0));
        apply(ctx_consistent_left_focus(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t, 0));
        apply(ctx_consistent_left_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t, 0));
        apply(ctx_consistent_left_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr), parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr), parent));
        apply(rb_parent_consistent_node_left(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_parent_consistent_node_right(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_reparent_parent_consistent(near, sibling, parent));
        apply(rb_node_is_reflexive(sibling));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, sibling, Color::Black, t, rb_reparent(near, parent), sibling));
        apply(rb_parent_consistent_node(red, sibling, Color::Black, rl, rr, sibling));
        apply(rb_parent_consistent_node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr), above));
        apply(ctx_consistent_swap(up, parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, near, RbTree::Node(red, sibling, Color::Red, rl, rr)), RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(parent, sibling, Color::Black, t, rb_reparent(near, parent)), RbTree::Node(red, sibling, Color::Black, rl, rr)), 0));
        assumption();
    }
}

theorem ctx_erase_case4_right_exit(above: struct rb_node*, parent: struct rb_node*, pcolor: Color,
                                 sibling: struct rb_node*, red: struct rb_node*, t: RbTree,
                                 near: RbTree, rl: RbTree, rr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up), Nat::Succ(black_height(t)), Color::Black) == 1;

    requires rb_parent_consistent(plug(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)))) == rb_inorder(plug(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up), t)) by {
        apply(plug_right_frame(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, t));
        have rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)) == RbTree::Node(sibling, above, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), RbTree::Node(parent, sibling, pcolor, rb_reparent(near, parent), t)) by {
            unfold(rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)));
            normalize();
        }
        apply(rb_rotate_right_node_preserves_inorder(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t));
        apply(rb_inorder_node_congruence(parent, sibling, Color::Black, pcolor, rb_reparent(near, parent), rb_reparent(near, parent), t, t));
        apply(rb_inorder_node_congruence(red, sibling, Color::Black, Color::Red, rl, rl, rr, rr));
        apply(rb_inorder_node_congruence(sibling, above, pcolor, Color::Black,
            RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(red, sibling, Color::Red, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t), RbTree::Node(parent, sibling, pcolor, rb_reparent(near, parent), t)));
        have rb_inorder(RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))) == rb_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)) by {
            rewrite(rb_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)) == rb_inorder(rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t))));
            rewrite(rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)) == RbTree::Node(sibling, above, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), RbTree::Node(parent, sibling, pcolor, rb_reparent(near, parent), t)));
            assumption();
        }
        apply(plug_inorder_transport(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)), RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)));
        rewrite(plug(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up), t) == plug(up, RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t)));
        assumption();
    }

    ensures is_rb_root(plug(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)))) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_right_height(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, Nat::Succ(black_height(t)), Color::Black));
        apply(nat_eq_symmetric(black_height(RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near)), Nat::Succ(black_height(t))));
        apply(ctx_rb_right_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_node_left(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near));
        apply(is_rb_node_right(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near));
        apply(is_rb_node_black_heights(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near));
        apply(black_height_black_node(sibling, parent, RbTree::Node(red, sibling, Color::Red, rl, rr), near));
        apply(is_rb_node_left(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_right(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_black_heights(red, sibling, Color::Red, rl, rr));
        apply(black_height_red_node(red, sibling, rl, rr));
        have black_height(t) == black_height(near) by {
            have Nat::Succ(black_height(t)) == Nat::Succ(black_height(RbTree::Node(red, sibling, Color::Red, rl, rr))) by {
                rewrite(Nat::Succ(black_height(RbTree::Node(red, sibling, Color::Red, rl, rr))) == black_height(RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near)));
                assumption();
            }
            extract(black_height(t) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            rewrite(black_height(near) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            assumption();
        }
        apply(rb_reparent_preserves_is_rb(near, parent));
        apply(rb_reparent_preserves_black_height(near, parent));
        have is_rb(rb_reparent(near, parent)) == 1 by auto;
        have black_height(t) == black_height(rb_reparent(near, parent)) by {
            rewrite(black_height(rb_reparent(near, parent)) == black_height(near));
            assumption();
        }
        apply(nat_eq_symmetric(black_height(t), black_height(rb_reparent(near, parent))));
        apply(is_rb_black_node(parent, sibling, rb_reparent(near, parent), t));
        apply(is_rb_black_node(red, sibling, rl, rr));
        apply(black_height_black_node(parent, sibling, rb_reparent(near, parent), t));
        apply(black_height_black_node(red, sibling, rl, rr));
        have black_height(RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)) == black_height(RbTree::Node(red, sibling, Color::Black, rl, rr)) by {
            rewrite(black_height(RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)) == Nat::Succ(black_height(rb_reparent(near, parent))));
            rewrite(black_height(RbTree::Node(red, sibling, Color::Black, rl, rr)) == Nat::Succ(black_height(rl)));
            rewrite(black_height(rb_reparent(near, parent)) == black_height(near));
            rewrite(black_height(rl) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            rewrite(black_height(near) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            normalize();
        }
        apply(rb_color_node(parent, sibling, Color::Black, rb_reparent(near, parent), t));
        apply(rb_color_node(red, sibling, Color::Black, rl, rr));
        apply(node_color_ok_black_children(pcolor));
        have node_color_ok(pcolor, rb_color(RbTree::Node(red, sibling, Color::Black, rl, rr)), rb_color(RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))) == 1 by {
            rewrite(rb_color(RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)) == Color::Black);
            rewrite(rb_color(RbTree::Node(red, sibling, Color::Black, rl, rr)) == Color::Black);
            assumption();
        }
        apply(nat_eq_symmetric(black_height(RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)), black_height(RbTree::Node(red, sibling, Color::Black, rl, rr))));
        apply(is_rb_node_from_parts(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)));
        apply(black_height_node_frame(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)));
        apply(rb_color_node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)));
        have black_height(RbTree::Node(red, sibling, Color::Black, rl, rr)) == Nat::Succ(black_height(t)) by auto;
        have ctx_rb(up, black_height(RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))), rb_color(RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)))) == 1 by {
            rewrite(black_height(RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))) == frame_black_height(pcolor, black_height(RbTree::Node(red, sibling, Color::Black, rl, rr))));
            rewrite(black_height(RbTree::Node(red, sibling, Color::Black, rl, rr)) == Nat::Succ(black_height(t)));
            rewrite(rb_color(RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))) == pcolor);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up), t, 0));
        apply(ctx_consistent_right_focus(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, t, 0));
        apply(ctx_consistent_right_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, t, 0));
        apply(ctx_consistent_right_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), up, t, 0));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near, parent));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near, parent));
        apply(rb_parent_consistent_node_left(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_parent_consistent_node_right(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_reparent_parent_consistent(near, sibling, parent));
        apply(rb_node_is_reflexive(sibling));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, sibling, Color::Black, rb_reparent(near, parent), t, sibling));
        apply(rb_parent_consistent_node(red, sibling, Color::Black, rl, rr, sibling));
        apply(rb_parent_consistent_node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t), above));
        apply(ctx_consistent_swap(up, parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), near), t, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(sibling, above, pcolor, RbTree::Node(red, sibling, Color::Black, rl, rr), RbTree::Node(parent, sibling, Color::Black, rb_reparent(near, parent), t)), 0));
        assumption();
    }
}

theorem ctx_erase_case3_left_exit(above: struct rb_node*, parent: struct rb_node*, pcolor: Color,
                                  sibling: struct rb_node*, red: struct rb_node*, t: RbTree,
                                  far: RbTree, rl: RbTree, rr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up), Nat::Succ(black_height(t)), Color::Black) == 1;

    requires rb_parent_consistent(plug(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))) == rb_inorder(plug(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up), t)) by {
        apply(plug_left_frame(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, t));
        have rb_rotate_right_at_right(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))) == RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))) by {
            unfold(rb_rotate_right_at_right(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))));
            unfold(rb_rotate_right(RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far)));
            normalize();
        }
        have rb_rotate_left(RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))) == RbTree::Node(red, above, Color::Red, RbTree::Node(parent, red, pcolor, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)) by auto;
        apply(rb_rotate_right_at_right_preserves_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))));
        apply(rb_rotate_left_preserves_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))));
        apply(rb_inorder_node_congruence(parent, red, Color::Black, pcolor, t, t, rb_reparent(rl, parent), rb_reparent(rl, parent)));
        apply(rb_inorder_node_congruence(red, above, pcolor, Color::Red,
            RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(parent, red, pcolor, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)));
        have rb_inorder(RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))) == rb_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))) by {
            rewrite(rb_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))) == rb_inorder(rb_rotate_right_at_right(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far)))));
            rewrite(rb_rotate_right_at_right(RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))) == RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))));
            rewrite(rb_inorder(RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))) == rb_inorder(rb_rotate_left(RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))))));
            rewrite(rb_rotate_left(RbTree::Node(parent, above, pcolor, t, RbTree::Node(red, parent, Color::Red, rl, RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))) == RbTree::Node(red, above, Color::Red, RbTree::Node(parent, red, pcolor, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)));
            assumption();
        }
        apply(plug_inorder_transport(up, RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)), RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))));
        rewrite(plug(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up), t) == plug(up, RbTree::Node(parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far))));
        assumption();
    }

    ensures is_rb_root(plug(up, RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))) == 1 by {
        apply(ctx_rb_left_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_height(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_left_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_node_left(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far));
        apply(is_rb_node_right(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far));
        apply(is_rb_node_black_heights(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far));
        apply(black_height_black_node(sibling, parent, RbTree::Node(red, sibling, Color::Red, rl, rr), far));
        apply(is_rb_node_left(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_right(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_black_heights(red, sibling, Color::Red, rl, rr));
        apply(is_rb_red_node_children_are_black(red, sibling, rl, rr));
        apply(is_rb_red_node_right_child_is_black(red, sibling, rl, rr));
        apply(black_height_red_node(red, sibling, rl, rr));
        have black_height(t) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)) by {
            have Nat::Succ(black_height(t)) == Nat::Succ(black_height(RbTree::Node(red, sibling, Color::Red, rl, rr))) by {
                rewrite(Nat::Succ(black_height(RbTree::Node(red, sibling, Color::Red, rl, rr))) == black_height(RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far)));
                assumption();
            }
            extract(black_height(t) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
        }
        have black_height(t) == black_height(rl) by auto;
        have black_height(t) == black_height(rr) by auto;
        apply(rb_reparent_preserves_is_rb(rl, parent));
        apply(rb_reparent_preserves_black_height(rl, parent));
        apply(rb_reparent_preserves_is_rb(rr, sibling));
        apply(rb_reparent_preserves_black_height(rr, sibling));
        have is_rb(rb_reparent(rl, parent)) == 1 by auto;
        have is_rb(rb_reparent(rr, sibling)) == 1 by auto;
        have black_height(t) == black_height(rb_reparent(rl, parent)) by {
            rewrite(black_height(rb_reparent(rl, parent)) == black_height(rl));
            assumption();
        }
        have black_height(t) == black_height(rb_reparent(rr, sibling)) by {
            rewrite(black_height(rb_reparent(rr, sibling)) == black_height(rr));
            assumption();
        }
        have black_height(rb_reparent(rr, sibling)) == black_height(far) by auto;
        apply(is_rb_black_node(parent, red, t, rb_reparent(rl, parent)));
        apply(is_rb_black_node(sibling, red, rb_reparent(rr, sibling), far));
        apply(black_height_black_node(parent, red, t, rb_reparent(rl, parent)));
        apply(black_height_black_node(sibling, red, rb_reparent(rr, sibling), far));
        have black_height(RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent))) == black_height(RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)) by auto;
        apply(rb_color_node(parent, red, Color::Black, t, rb_reparent(rl, parent)));
        apply(rb_color_node(sibling, red, Color::Black, rb_reparent(rr, sibling), far));
        apply(node_color_ok_black_children(pcolor));
        have node_color_ok(pcolor, rb_color(RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent))), rb_color(RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))) == 1 by {
            rewrite(rb_color(RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent))) == Color::Black);
            rewrite(rb_color(RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)) == Color::Black);
            assumption();
        }
        apply(is_rb_node_from_parts(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)));
        apply(black_height_node_frame(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)));
        apply(rb_color_node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)));
        have ctx_rb(up, black_height(RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))), rb_color(RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)))) == 1 by {
            rewrite(black_height(RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))) == frame_black_height(pcolor, black_height(RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)))));
            rewrite(black_height(RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent))) == Nat::Succ(black_height(t)));
            rewrite(rb_color(RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))) == pcolor);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up, RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Left(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up), t, 0));
        apply(ctx_consistent_left_focus(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, t, 0));
        apply(ctx_consistent_left_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, t, 0));
        apply(ctx_consistent_left_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far, parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far, parent));
        apply(rb_parent_consistent_node_left(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_parent_consistent_node_right(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_reparent_parent_consistent(rl, red, parent));
        apply(rb_reparent_parent_consistent(rr, red, sibling));
        apply(rb_node_is_reflexive(red));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, red, Color::Black, t, rb_reparent(rl, parent), red));
        apply(rb_parent_consistent_node(sibling, red, Color::Black, rb_reparent(rr, sibling), far, red));
        apply(rb_parent_consistent_node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far), above));
        apply(ctx_consistent_swap(up, parent, above, pcolor, t, RbTree::Node(sibling, parent, Color::Black, RbTree::Node(red, sibling, Color::Red, rl, rr), far), RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(red, above, pcolor, RbTree::Node(parent, red, Color::Black, t, rb_reparent(rl, parent)), RbTree::Node(sibling, red, Color::Black, rb_reparent(rr, sibling), far)), 0));
        assumption();
    }
}

theorem ctx_erase_case3_right_exit(above: struct rb_node*, parent: struct rb_node*, pcolor: Color,
                                  sibling: struct rb_node*, red: struct rb_node*, t: RbTree,
                                  far: RbTree, rl: RbTree, rr: RbTree, up: Context) {
    requires is_rb(t) == 1;
    requires rb_root_black(t) == 1;
    requires ctx_rb(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), Nat::Succ(black_height(t)), Color::Black) == 1;

    requires rb_parent_consistent(plug(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t), 0) == 1;

    ensures rb_inorder(plug(up, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)))) == rb_inorder(plug(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t)) by {
        apply(plug_right_frame(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t));
        have rb_rotate_left_at_left(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)) == RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t) by {
            unfold(rb_rotate_left_at_left(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)));
            unfold(rb_rotate_left(RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr))));
            normalize();
        }
        have rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t)) == RbTree::Node(red, above, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, pcolor, rb_reparent(rr, parent), t)) by auto;
        apply(rb_rotate_left_at_left_preserves_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)));
        apply(rb_rotate_right_preserves_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t)));
        apply(rb_inorder_node_congruence(parent, red, Color::Black, pcolor, rb_reparent(rr, parent), rb_reparent(rr, parent), t, t));
        apply(rb_inorder_node_congruence(red, above, pcolor, Color::Red,
            RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t), RbTree::Node(parent, red, pcolor, rb_reparent(rr, parent), t)));
        have rb_inorder(RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))) == rb_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)) by {
            rewrite(rb_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)) == rb_inorder(rb_rotate_left_at_left(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t))));
            rewrite(rb_rotate_left_at_left(RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)) == RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t));
            rewrite(rb_inorder(RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t)) == rb_inorder(rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t))));
            rewrite(rb_rotate_right(RbTree::Node(parent, above, pcolor, RbTree::Node(red, parent, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), rr), t)) == RbTree::Node(red, above, Color::Red, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, pcolor, rb_reparent(rr, parent), t)));
            assumption();
        }
        apply(plug_inorder_transport(up, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)), RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)));
        rewrite(plug(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t) == plug(up, RbTree::Node(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t)));
        assumption();
    }

    ensures is_rb_root(plug(up, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)))) == 1 by {
        apply(ctx_rb_right_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, Nat::Succ(black_height(t)), Color::Black));
        apply(ctx_rb_right_height(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, Nat::Succ(black_height(t)), Color::Black));
        apply(nat_eq_symmetric(black_height(RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr))), Nat::Succ(black_height(t))));
        apply(ctx_rb_right_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, Nat::Succ(black_height(t)), Color::Black));
        apply(is_rb_node_left(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(is_rb_node_right(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(is_rb_node_black_heights(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(black_height_black_node(sibling, parent, far, RbTree::Node(red, sibling, Color::Red, rl, rr)));
        apply(is_rb_node_left(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_right(red, sibling, Color::Red, rl, rr));
        apply(is_rb_node_black_heights(red, sibling, Color::Red, rl, rr));
        apply(is_rb_red_node_children_are_black(red, sibling, rl, rr));
        apply(is_rb_red_node_right_child_is_black(red, sibling, rl, rr));
        apply(black_height_red_node(red, sibling, rl, rr));
        have black_height(t) == black_height(far) by {
            have Nat::Succ(black_height(t)) == Nat::Succ(black_height(far)) by {
                rewrite(Nat::Succ(black_height(far)) == black_height(RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr))));
                assumption();
            }
            extract(black_height(t) == black_height(far));
        }
        have black_height(t) == black_height(rl) by {
            rewrite(black_height(rl) == black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)));
            rewrite(black_height(RbTree::Node(red, sibling, Color::Red, rl, rr)) == black_height(far));
            assumption();
        }
        have black_height(t) == black_height(rr) by auto;
        apply(rb_reparent_preserves_is_rb(rl, sibling));
        apply(rb_reparent_preserves_black_height(rl, sibling));
        apply(rb_reparent_preserves_is_rb(rr, parent));
        apply(rb_reparent_preserves_black_height(rr, parent));
        have is_rb(rb_reparent(rr, parent)) == 1 by auto;
        have is_rb(rb_reparent(rl, sibling)) == 1 by auto;
        have black_height(t) == black_height(rb_reparent(rl, sibling)) by {
            rewrite(black_height(rb_reparent(rl, sibling)) == black_height(rl));
            assumption();
        }
        have black_height(far) == black_height(rb_reparent(rl, sibling)) by auto;
        have black_height(rb_reparent(rr, parent)) == black_height(t) by auto;
        apply(is_rb_black_node(parent, red, rb_reparent(rr, parent), t));
        apply(is_rb_black_node(sibling, red, far, rb_reparent(rl, sibling)));
        apply(black_height_black_node(parent, red, rb_reparent(rr, parent), t));
        apply(black_height_black_node(sibling, red, far, rb_reparent(rl, sibling)));
        have black_height(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling))) == black_height(RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)) by {
            rewrite(black_height(RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)) == Nat::Succ(black_height(rb_reparent(rr, parent))));
            rewrite(black_height(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling))) == Nat::Succ(black_height(far)));
            rewrite(black_height(rb_reparent(rr, parent)) == black_height(t));
            rewrite(black_height(far) == black_height(t));
            normalize();
        }
        apply(rb_color_node(parent, red, Color::Black, rb_reparent(rr, parent), t));
        apply(rb_color_node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)));
        apply(node_color_ok_black_children(pcolor));
        have node_color_ok(pcolor, rb_color(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling))), rb_color(RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))) == 1 by {
            rewrite(rb_color(RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)) == Color::Black);
            rewrite(rb_color(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling))) == Color::Black);
            assumption();
        }
        apply(is_rb_node_from_parts(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)));
        apply(black_height_node_frame(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)));
        apply(rb_color_node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)));
        have black_height(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling))) == Nat::Succ(black_height(t)) by auto;
        have ctx_rb(up, black_height(RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))), rb_color(RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)))) == 1 by {
            rewrite(black_height(RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))) == frame_black_height(pcolor, black_height(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)))));
            rewrite(black_height(RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling))) == Nat::Succ(black_height(t)));
            rewrite(rb_color(RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))) == pcolor);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(up, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))));
        assumption();
    }

    ensures rb_parent_consistent(plug(up, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t))), 0) == 1 by {
        apply(plug_parent_consistent_ctx(Context::Right(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up), t, 0));
        apply(ctx_consistent_right_focus(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t, 0));
        apply(ctx_consistent_right_sibling(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t, 0));
        apply(ctx_consistent_right_up(parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), up, t, 0));
        apply(rb_parent_consistent_node_left(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr), parent));
        apply(rb_parent_consistent_node_right(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr), parent));
        apply(rb_parent_consistent_node_left(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_parent_consistent_node_right(red, sibling, Color::Red, rl, rr, sibling));
        apply(rb_reparent_parent_consistent(rl, red, sibling));
        apply(rb_reparent_parent_consistent(rr, red, parent));
        apply(rb_node_is_reflexive(red));
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(parent, red, Color::Black, rb_reparent(rr, parent), t, red));
        apply(rb_parent_consistent_node(sibling, red, Color::Black, far, rb_reparent(rl, sibling), red));
        apply(rb_parent_consistent_node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t), above));
        apply(ctx_consistent_swap(up, parent, above, pcolor, RbTree::Node(sibling, parent, Color::Black, far, RbTree::Node(red, sibling, Color::Red, rl, rr)), t, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)), 0));
        apply(plug_parent_consistent_transport(up, RbTree::Node(red, above, pcolor, RbTree::Node(sibling, red, Color::Black, far, rb_reparent(rl, sibling)), RbTree::Node(parent, red, Color::Black, rb_reparent(rr, parent), t)), 0));
        assumption();
    }
}

theorem ctx_erase_left_sibling_is_node(above: struct rb_node*, parent: struct rb_node*,
                                      pcolor: Color, sibling_model: RbTree, up: Context,
                                      bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Left(parent, above, pcolor, sibling_model, up), Nat::Succ(bh),
        focus_color) == 1;

    ensures sibling_model != RbTree::Empty by {
        induct(sibling_model) as ih {
            RbTree::Empty => {
                apply(ctx_rb_left_height(parent, above, pcolor, RbTree::Empty, up, Nat::Succ(bh), focus_color));
                have black_height(RbTree::Empty) == Nat::Zero by auto;
                have Nat::Succ(bh) == Nat::Zero by auto;
                contradiction(Nat::Succ(bh) == Nat::Zero);
            }
            RbTree::Node(node, node_parent, color, left, right) => {
                normalize();
            }
        }
    }
}

theorem ctx_erase_right_sibling_is_node(above: struct rb_node*, parent: struct rb_node*,
                                      pcolor: Color, sibling_model: RbTree, up: Context,
                                      bh: Nat, focus_color: Color) {
    requires ctx_rb(Context::Right(parent, above, pcolor, sibling_model, up), Nat::Succ(bh),
        focus_color) == 1;

    ensures sibling_model != RbTree::Empty by {
        induct(sibling_model) as ih {
            RbTree::Empty => {
                apply(ctx_rb_right_height(parent, above, pcolor, RbTree::Empty, up, Nat::Succ(bh), focus_color));
                have black_height(RbTree::Empty) == Nat::Zero by auto;
                have Nat::Zero == Nat::Succ(bh) by auto;
                contradiction(Nat::Zero == Nat::Succ(bh));
            }
            RbTree::Node(node, node_parent, color, left, right) => {
                normalize();
            }
        }
    }
}
