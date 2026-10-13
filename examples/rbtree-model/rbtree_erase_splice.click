import "rbtree_model.click";

# The minimum's identity, original color, and right child. The parent is
# deliberately absent: moving the right subtree changes only that payload.
spec enum RbMinimum {
    Absent,
    Found(struct rb_node*, Color, RbTree),
}

function rb_minimum(tree: RbTree) -> RbMinimum
    decreases tree
{
    match tree {
        RbTree::Empty => RbMinimum::Absent,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => RbMinimum::Found(node, color, right),
            RbTree::Node(a, b, c, l, r) => rb_minimum(left),
        },
    }
}

# This accumulator is the context carried by the C successor descent loop.
# At an immediate successor no frame is pushed. At a deeper successor the
# nearest Left frame identifies the parent whose left link becomes empty.
function rb_min_context(tree: RbTree, up: Context) -> Context
    decreases tree
{
    match tree {
        RbTree::Empty => up,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => up,
            RbTree::Node(a, b, c, l, r) =>
                rb_min_context(left, Context::Left(node, parent, color, right, up)),
        },
    }
}

theorem rb_reparent_twice(tree: RbTree, first: struct rb_node*, last: struct rb_node*) {
    ensures rb_reparent(rb_reparent(tree, first), last) == rb_reparent(tree, last) by {
        induct(tree) as tree_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, first));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), first));
                unfold(rb_reparent(RbTree::Node(node, first, color, left, right), last));
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), last));
                normalize();
            }
        }
    }
}

theorem rb_reparent_preserves_color(tree: RbTree, parent: struct rb_node*) {
    ensures rb_color(rb_reparent(tree, parent)) == rb_color(tree) by {
        induct(tree) as tree_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, parent));
                normalize();
            }
            RbTree::Node(node, old_parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, old_parent, color, left, right), parent));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_color(RbTree::Node(node, old_parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_minimum_reparent(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_minimum(rb_reparent(tree, new_parent)) == rb_minimum(tree) by {
        induct(tree) as tree_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent));
                unfold(rb_minimum(RbTree::Node(node, parent, color, left, right)));
                unfold(rb_minimum(RbTree::Node(node, new_parent, color, left, right)));
                normalize();
            }
        }
    }
}

theorem rb_remove_min_node_reparent(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree, new_parent: struct rb_node*) {
    ensures rb_remove_min(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent))
        == rb_reparent(rb_remove_min(RbTree::Node(node, parent, color, left, right)), new_parent) by {
        induct(left) as left_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, RbTree::Empty, right), new_parent));
                unfold(rb_remove_min(RbTree::Node(node, new_parent, color, RbTree::Empty, right)));
                unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                apply(rb_reparent_twice(right, parent, new_parent));
                rewrite(rb_reparent(rb_reparent(right, parent), new_parent) == rb_reparent(right,
                    new_parent));
                normalize();
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right), new_parent));
                unfold(rb_remove_min(RbTree::Node(node, new_parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                unfold(rb_remove_min(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                unfold(rb_reparent(RbTree::Node(node, parent, color,
                    rb_remove_min(RbTree::Node(a, b, c, l, r)), right), new_parent));
                normalize();
            }
        }
    }
}

theorem rb_remove_min_reparent(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_remove_min(rb_reparent(tree, new_parent))
        == rb_reparent(rb_remove_min(tree), new_parent) by {
        induct(tree) as tree_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                unfold(rb_remove_min(RbTree::Empty));
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_remove_min_node_reparent(node, parent, color, left, right, new_parent));
                assumption();
            }
        }
    }
}

theorem rb_min_list_nonempty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree) {
    requires not(left == RbTree::Empty);

    ensures rb_min_list(RbTree::Node(node, parent, color, left, right)) == rb_min_list(left) by {
        induct(left) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_min_list(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                normalize();
            }
        }
    }
}

theorem rb_remove_min_nonempty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree) {
    requires not(left == RbTree::Empty);

    ensures rb_remove_min(RbTree::Node(node, parent, color, left, right)) == RbTree::Node(node, parent,
        color, rb_remove_min(left), right) by {
        induct(left) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_remove_min(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                normalize();
            }
        }
    }
}

theorem rb_minimum_nonempty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree) {
    requires not(left == RbTree::Empty);

    ensures rb_minimum(RbTree::Node(node, parent, color, left, right)) == rb_minimum(left) by {
        induct(left) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_minimum(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                normalize();
            }
        }
    }
}

theorem rb_min_context_nonempty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree, up: Context) {
    requires not(left == RbTree::Empty);

    ensures rb_min_context(RbTree::Node(node, parent, color, left, right), up) == rb_min_context(left,
        Context::Left(node, parent, color, right, up)) by {
        induct(left) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_min_context(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right), up));
                normalize();
            }
        }
    }
}

theorem rb_minimum_list(tree: RbTree, successor: struct rb_node*, color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, color, child);

    ensures rb_min_list(tree) == List<struct rb_node*>::Cons(successor, List<struct rb_node*>::Nil) by {
        induct(tree) as ih {
            RbTree::Empty => {
                have rb_minimum(RbTree::Empty) != RbMinimum::Found(successor, color, child) by auto;
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, color, child));
            }
            RbTree::Node(node, parent, ncolor, left, right) => {
                if left == RbTree::Empty {
                    have rb_minimum(RbTree::Node(node, parent, ncolor, left, right))
                        == RbMinimum::Found(node, ncolor, right) by {
                        rewrite(left == RbTree::Empty);
                        unfold(rb_minimum(RbTree::Node(node, parent, ncolor, RbTree::Empty, right)));
                        normalize();
                    }
                    have RbMinimum::Found(node, ncolor, right)
                        == RbMinimum::Found(successor, color, child) by {
                        rewrite(RbMinimum::Found(node, ncolor, right)
                            == rb_minimum(RbTree::Node(node, parent, ncolor, left, right)));
                        assumption();
                    }
                    extract(node == successor);
                    rewrite(left == RbTree::Empty);
                    unfold(rb_min_list(RbTree::Node(node, parent, ncolor, RbTree::Empty, right)));
                    rewrite(node == successor);
                    normalize();
                } else {
                    have rb_minimum(RbTree::Node(node, parent, ncolor, left, right))
                        == rb_minimum(left) by {
                        apply(rb_minimum_nonempty_left(node, parent, ncolor, left, right));
                        assumption();
                    }
                    have rb_minimum(left) == RbMinimum::Found(successor, color, child) by auto;
                    apply(ih(left, successor, color, child));
                    apply(rb_min_list_nonempty_left(node, parent, ncolor, left, right));
                    rewrite(rb_min_list(RbTree::Node(node, parent, ncolor, left, right))
                        == rb_min_list(left));
                    assumption();
                }
            }
        }
    }
}

theorem rb_minimum_child_empty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree,
        successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires left == RbTree::Empty;
    requires rb_minimum(RbTree::Node(node, parent, color, left, right))
        == RbMinimum::Found(successor, min_color, child);
    ensures RbMinimum::Found(node, color, right)
        == RbMinimum::Found(successor, min_color, child) by {
        have rb_minimum(RbTree::Node(node, parent, color, left, right))
            == RbMinimum::Found(node, color, right) by {
            rewrite(left == RbTree::Empty);
            unfold(rb_minimum(RbTree::Node(node, parent, color, RbTree::Empty, right)));
            normalize();
        }
        rewrite(RbMinimum::Found(node, color, right)
            == rb_minimum(RbTree::Node(node, parent, color, left, right)));
        assumption();
    }
}

theorem rb_minimum_empty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree,
        successor: struct rb_node*, min_color: Color) {
    requires left == RbTree::Empty;
    requires rb_minimum(RbTree::Node(node, parent, color, left, right))
        == RbMinimum::Found(successor, min_color, RbTree::Empty);

    ensures RbMinimum::Found(node, color, right)
        == RbMinimum::Found(successor, min_color, RbTree::Empty) by {
        have rb_minimum(RbTree::Node(node, parent, color, left, right))
            == RbMinimum::Found(node, color, right) by {
            rewrite(left == RbTree::Empty);
            unfold(rb_minimum(RbTree::Node(node, parent, color, RbTree::Empty, right)));
            normalize();
        }
        rewrite(RbMinimum::Found(node, color, right)
            == rb_minimum(RbTree::Node(node, parent, color, left, right)));
        assumption();
    }
}

theorem rb_min_context_cut_leaf(tree: RbTree, up: Context, successor: struct rb_node*, min_color: Color) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, RbTree::Empty);

    ensures plug(rb_min_context(tree, up), RbTree::Empty) == plug(up, rb_remove_min(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, RbTree::Empty))
                    by {
                    unfold(rb_minimum(RbTree::Empty));
                    normalize();
                }
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color,
                    RbTree::Empty));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_empty_left(node, parent, color, left, right, successor, min_color));
                    extract(right == RbTree::Empty);
                    rewrite(left == RbTree::Empty);
                    unfold(rb_min_context(RbTree::Node(node, parent, color, RbTree::Empty, right), up));
                    unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    rewrite(right == RbTree::Empty);
                    unfold(rb_reparent(RbTree::Empty, parent));
                    normalize();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, RbTree::Empty) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(ih(left, Context::Left(node, parent, color, right, up), successor, min_color));
                    apply(rb_remove_min_nonempty_left(node, parent, color, left, right));
                    rewrite(rb_remove_min(RbTree::Node(node, parent, color, left, right))
                        == RbTree::Node(node, parent, color, rb_remove_min(left), right));
                    apply(rb_min_context_nonempty_left(node, parent, color, left, right, up));
                    rewrite(rb_min_context(RbTree::Node(node, parent, color, left, right), up)
                        == rb_min_context(left, Context::Left(node, parent, color, right, up)));
                    rewrite(plug(rb_min_context(left, Context::Left(node, parent, color, right, up)),
                        RbTree::Empty)
                        == plug(Context::Left(node, parent, color, right, up), rb_remove_min(left)));
                    unfold(plug(Context::Left(node, parent, color, right, up), rb_remove_min(left)));
                    normalize();
                }
            }
        }
    }
}

theorem rb_min_context_child(tree: RbTree, up: Context, successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;

    ensures ctx_rb(rb_min_context(tree, up), frame_black_height(min_color, Nat::Zero), min_color) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color,
                    child)) by {
                    unfold(rb_minimum(RbTree::Empty));
                    normalize();
                }
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color,
                    child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor, min_color, child));
                    extract(color == min_color);
                    apply(black_height_node_frame(node, parent, color, left, right));
                    have black_height(RbTree::Node(node, parent, color, left, right))
                        == frame_black_height(min_color, Nat::Zero) by {
                        rewrite(black_height(RbTree::Node(node, parent, color, left, right))
                            == frame_black_height(color, black_height(left)));
                        rewrite(color == min_color);
                        rewrite(left == RbTree::Empty);
                        unfold(black_height(RbTree::Empty));
                        normalize();
                    }
                    have rb_color(RbTree::Node(node, parent, color, left, right)) == min_color by auto;
                    have ctx_rb(up, frame_black_height(min_color, Nat::Zero), min_color) == 1 by auto;
                    rewrite(left == RbTree::Empty);
                    unfold(rb_min_context(RbTree::Node(node, parent, color, RbTree::Empty, right), up));
                    assumption();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(is_rb_node_right(node, parent, color, left, right));
                    apply(is_rb_node_black_heights(node, parent, color, left, right));
                    apply(is_rb_node_colors(node, parent, color, left, right));
                    apply(black_height_node_frame(node, parent, color, left, right));
                    apply(rb_color_node(node, parent, color, left, right));
                    have ctx_rb(up, black_height(RbTree::Node(node, parent, color, left, right)),
                            rb_color(RbTree::Node(node, parent, color, left, right)))
                        == ctx_rb(up, frame_black_height(color, black_height(left)), color) by {
                        rewrite(black_height(RbTree::Node(node, parent, color, left, right))
                            == frame_black_height(color, black_height(left)));
                        rewrite(rb_color(RbTree::Node(node, parent, color, left, right)) == color);
                        normalize();
                    }
                    have ctx_rb(up, frame_black_height(color, black_height(left)), color) == 1 by auto;
                    apply(ctx_rb_left_frame(node, parent, color, right, up, black_height(left),
                        rb_color(left)));
                    apply(ih(left, Context::Left(node, parent, color, right, up), successor, min_color, child));
                    apply(rb_min_context_nonempty_left(node, parent, color, left, right, up));
                    rewrite(rb_min_context(RbTree::Node(node, parent, color, left, right), up)
                        == rb_min_context(left, Context::Left(node, parent, color, right, up)));
                    assumption();
                }
            }
        }
    }
}


theorem rb_min_context_leaf(tree: RbTree, up: Context, successor: struct rb_node*, min_color: Color) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, RbTree::Empty);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;
    ensures ctx_rb(rb_min_context(tree, up), frame_black_height(min_color, Nat::Zero), min_color) == 1 by {
        apply(rb_min_context_child(tree, up, successor, min_color, RbTree::Empty)); assumption();
    }
}

theorem rb_min_context_black_deficit(tree: RbTree, up: Context, successor: struct rb_node*) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, Color::Black, RbTree::Empty);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;
    ensures ctx_rb(rb_min_context(tree, up), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
        apply(rb_min_context_leaf(tree, up, successor, Color::Black));
        unfold(frame_black_height(Color::Black, Nat::Zero));
        rewrite(Nat::Succ(Nat::Zero) == frame_black_height(Color::Black, Nat::Zero));
        assumption();
    }
}

theorem rb_min_context_red_exit(tree: RbTree, up: Context, successor: struct rb_node*) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, Color::Red, RbTree::Empty);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;
    ensures ctx_rb(rb_min_context(tree, up), Nat::Zero, Color::Black) == 1 by {
        apply(rb_min_context_leaf(tree, up, successor, Color::Red));
        unfold(frame_black_height(Color::Red, Nat::Zero));
        have ctx_rb(rb_min_context(tree, up), Nat::Zero, Color::Red) == 1 by {
            rewrite(Nat::Zero == frame_black_height(Color::Red, Nat::Zero));
            assumption();
        }
        apply(ctx_rb_black_focus(rb_min_context(tree, up), Nat::Zero, Color::Red));
        assumption();
    }
}

function rb_successor_splice(successor: struct rb_node*, parent: struct rb_node*,
                             color: Color, left: RbTree, right: RbTree) -> RbTree {
    RbTree::Node(successor, parent, color, rb_reparent(left, successor),
        rb_reparent(rb_remove_min(right), successor))
}

function rb_successor_context(successor: struct rb_node*, parent: struct rb_node*,
                              color: Color, left: RbTree, right: RbTree, up: Context) -> Context {
    rb_min_context(rb_reparent(right, successor),
        Context::Right(successor, parent, color, rb_reparent(left, successor), up))
}

theorem ctx_rb_node_right_summary(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree, up: Context) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(node, parent, color, left, right)),
        rb_color(RbTree::Node(node, parent, color, left, right))) == 1;

    ensures ctx_rb(up, frame_black_height(color, black_height(right)), color) == 1 by {
        apply(black_height_node_frame(node, parent, color, left, right));
        apply(rb_color_node(node, parent, color, left, right));
        apply(is_rb_node_black_heights(node, parent, color, left, right));
        have ctx_rb(up, black_height(RbTree::Node(node, parent, color, left, right)),
                rb_color(RbTree::Node(node, parent, color, left, right)))
            == ctx_rb(up, frame_black_height(color, black_height(right)), color) by {
            rewrite(black_height(RbTree::Node(node, parent, color, left, right))
                == frame_black_height(color, black_height(left)));
            rewrite(rb_color(RbTree::Node(node, parent, color, left, right)) == color);
            rewrite(black_height(left) == black_height(right));
            normalize();
        }
        rewrite(ctx_rb(up, frame_black_height(color, black_height(right)), color)
            == ctx_rb(up, black_height(RbTree::Node(node, parent, color, left, right)),
                rb_color(RbTree::Node(node, parent, color, left, right))));
        assumption();
    }
}

theorem ctx_rb_successor_right(erased: struct rb_node*, successor: struct rb_node*,
        parent: struct rb_node*, color: Color, left: RbTree, right: RbTree, up: Context) {
    requires is_rb(RbTree::Node(erased, parent, color, left, right)) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left, right)),
        rb_color(RbTree::Node(erased, parent, color, left, right))) == 1;

    ensures ctx_rb(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
        black_height(rb_reparent(right, successor)), rb_color(rb_reparent(right, successor))) == 1 by {
        apply(is_rb_node_left(erased, parent, color, left, right));
        apply(is_rb_node_black_heights(erased, parent, color, left, right));
        apply(is_rb_node_colors(erased, parent, color, left, right));
        apply(ctx_rb_node_right_summary(erased, parent, color, left, right, up));
        apply(rb_reparent_preserves_is_rb(left, successor));
        apply(rb_reparent_preserves_black_height(left, successor));
        apply(rb_reparent_preserves_black_height(right, successor));
        apply(rb_reparent_preserves_color(left, successor));
        apply(rb_reparent_preserves_color(right, successor));
        have is_rb(rb_reparent(left, successor)) == 1 by auto;
        have black_height(rb_reparent(left, successor)) == black_height(rb_reparent(right, successor)) by {
            rewrite(black_height(rb_reparent(left, successor)) == black_height(left));
            rewrite(black_height(rb_reparent(right, successor)) == black_height(right));
            assumption();
        }
        have node_color_ok(color, rb_color(rb_reparent(left, successor)),
            rb_color(rb_reparent(right, successor))) == 1 by {
            rewrite(rb_color(rb_reparent(left, successor)) == rb_color(left));
            rewrite(rb_color(rb_reparent(right, successor)) == rb_color(right));
            assumption();
        }
        have ctx_rb(up, frame_black_height(color, black_height(rb_reparent(right, successor))), color) == 1
            by {
            rewrite(black_height(rb_reparent(right, successor)) == black_height(right));
            assumption();
        }
        apply(ctx_rb_right_frame(successor, parent, color, rb_reparent(left, successor), up,
            black_height(rb_reparent(right, successor)), rb_color(rb_reparent(right, successor))));
        assumption();
    }
}

theorem rb_successor_splice_cut(successor: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree, up: Context, min_color: Color) {
    requires rb_minimum(right) == RbMinimum::Found(successor, min_color, RbTree::Empty);

    ensures plug(rb_successor_context(successor, parent, color, left, right, up), RbTree::Empty)
        == plug(up, rb_successor_splice(successor, parent, color, left, right)) by {
        apply(rb_minimum_reparent(right, successor));
        have rb_minimum(rb_reparent(right, successor))
            == RbMinimum::Found(successor, min_color, RbTree::Empty) by {
            rewrite(rb_minimum(rb_reparent(right, successor)) == rb_minimum(right));
            assumption();
        }
        apply(rb_min_context_cut_leaf(rb_reparent(right, successor),
            Context::Right(successor, parent, color, rb_reparent(left, successor), up),
            successor, min_color));
        apply(rb_remove_min_reparent(right, successor));
        unfold(rb_successor_context(successor, parent, color, left, right, up));
        rewrite(plug(rb_min_context(rb_reparent(right, successor),
                Context::Right(successor, parent, color, rb_reparent(left, successor), up)), RbTree::Empty)
            == plug(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
                rb_remove_min(rb_reparent(right, successor))));
        unfold(plug(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
            rb_remove_min(rb_reparent(right, successor))));
        rewrite(rb_remove_min(rb_reparent(right, successor)) == rb_reparent(rb_remove_min(right),
            successor));
        unfold(rb_successor_splice(successor, parent, color, left, right));
        normalize();
    }
}

# The black-successor/no-right-child branch of __rb_erase_augmented.
# The result is deliberately a deficit context, not a red-black whole tree.
theorem rb_erase_black_successor_splice(erased: struct rb_node*, successor: struct rb_node*,
        parent: struct rb_node*, color: Color, left: RbTree, right: RbTree,
        up: Context, root_parent: struct rb_node*) {
    requires rb_minimum(right) == RbMinimum::Found(successor, Color::Black, RbTree::Empty);
    requires is_rb(RbTree::Node(erased, parent, color, left, right)) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left, right)),
        rb_color(RbTree::Node(erased, parent, color, left, right))) == 1;
    requires ctx_consistent(up, RbTree::Node(erased, parent, color, left, right), root_parent) == 1;

    ensures ctx_rb(rb_successor_context(successor, parent, color, left, right, up),
        Nat::Succ(Nat::Zero), Color::Black) == 1 by {
        apply(ctx_rb_successor_right(erased, successor, parent, color, left, right, up));
        apply(is_rb_node_right(erased, parent, color, left, right));
        apply(rb_reparent_preserves_is_rb(right, successor));
        have is_rb(rb_reparent(right, successor)) == 1 by auto;
        apply(rb_minimum_reparent(right, successor));
        have rb_minimum(rb_reparent(right, successor))
            == RbMinimum::Found(successor, Color::Black, RbTree::Empty) by {
            rewrite(rb_minimum(rb_reparent(right, successor)) == rb_minimum(right));
            assumption();
        }
        apply(rb_min_context_black_deficit(rb_reparent(right, successor),
            Context::Right(successor, parent, color, rb_reparent(left, successor), up), successor));
        unfold(rb_successor_context(successor, parent, color, left, right, up));
        assumption();
    }

    ensures plug(rb_successor_context(successor, parent, color, left, right, up), RbTree::Empty)
        == plug(up, rb_successor_splice(successor, parent, color, left, right)) by {
        apply(rb_successor_splice_cut(successor, parent, color, left, right, up, Color::Black));
        assumption();
    }

    ensures rb_inorder(rb_successor_splice(successor, parent, color, left, right))
        == list_append(rb_inorder(left), rb_inorder(right)) by {
        apply(rb_minimum_list(right, successor, Color::Black, RbTree::Empty));
        apply(rb_erase_two_child_splice(erased, successor, parent, color, left, right));
        unfold(rb_successor_splice(successor, parent, color, left, right));
        assumption();
    }

    ensures ctx_consistent(rb_successor_context(successor, parent, color, left, right, up),
        RbTree::Empty, root_parent) == 1 by {
        apply(ctx_consistent_node_children(up, erased, parent, color, left, right, root_parent));
        apply(rb_node_is_reflexive(parent));
        apply(rb_parent_consistent_node(erased, parent, color, left, right, parent));
        apply(rb_erase_two_child_splice_parent_consistent(erased, successor, parent, color,
            left, right, parent));
        have rb_parent_consistent(rb_successor_splice(successor, parent, color, left, right), parent) == 1
            by {
            unfold(rb_successor_splice(successor, parent, color, left, right));
            assumption();
        }
        apply(ctx_consistent_swap(up, erased, parent, color, left, right,
            rb_successor_splice(successor, parent, color, left, right), root_parent));
        apply(plug_parent_consistent_transport(up,
            rb_successor_splice(successor, parent, color, left, right), root_parent));
        apply(rb_successor_splice_cut(successor, parent, color, left, right, up, Color::Black));
        have rb_parent_consistent(
            plug(rb_successor_context(successor, parent, color, left, right, up), RbTree::Empty),
                root_parent) == 1 by {
            rewrite(plug(rb_successor_context(successor, parent, color, left, right, up), RbTree::Empty)
                == plug(up, rb_successor_splice(successor, parent, color, left, right)));
            assumption();
        }
        apply(plug_parent_consistent_ctx(rb_successor_context(successor, parent, color, left, right, up),
            RbTree::Empty, root_parent));
        assumption();
    }
}

# A red leaf successor removes no black level. Its empty hole can be plugged
# immediately, and the returned whole tree needs no erase-color fixup.
theorem rb_erase_red_successor_splice(erased: struct rb_node*, successor: struct rb_node*,
        parent: struct rb_node*, color: Color, left: RbTree, right: RbTree,
        up: Context, root_parent: struct rb_node*) {
    requires rb_minimum(right) == RbMinimum::Found(successor, Color::Red, RbTree::Empty);
    requires is_rb(RbTree::Node(erased, parent, color, left, right)) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left, right)),
        rb_color(RbTree::Node(erased, parent, color, left, right))) == 1;
    requires ctx_consistent(up, RbTree::Node(erased, parent, color, left, right), root_parent) == 1;

    ensures is_rb_root(plug(up, rb_successor_splice(successor, parent, color, left, right))) == 1 by {
        apply(ctx_rb_successor_right(erased, successor, parent, color, left, right, up));
        apply(is_rb_node_right(erased, parent, color, left, right));
        apply(rb_reparent_preserves_is_rb(right, successor));
        have is_rb(rb_reparent(right, successor)) == 1 by auto;
        apply(rb_minimum_reparent(right, successor));
        have rb_minimum(rb_reparent(right, successor))
            == RbMinimum::Found(successor, Color::Red, RbTree::Empty) by {
            rewrite(rb_minimum(rb_reparent(right, successor)) == rb_minimum(right)); assumption();
        }
        apply(rb_min_context_red_exit(rb_reparent(right, successor),
            Context::Right(successor, parent, color, rb_reparent(left, successor), up), successor));
        have ctx_rb(rb_successor_context(successor, parent, color, left, right, up),
            black_height(RbTree::Empty), rb_color(RbTree::Empty)) == 1 by {
            unfold(rb_successor_context(successor, parent, color, left, right, up));
            unfold(black_height(RbTree::Empty)); unfold(rb_color(RbTree::Empty)); assumption();
        }
        unfold(is_rb(RbTree::Empty));
        apply(plug_rb_from_ctx_rb(rb_successor_context(successor, parent, color, left, right, up),
            RbTree::Empty));
        apply(rb_successor_splice_cut(successor, parent, color, left, right, up, Color::Red));
        rewrite(plug(up, rb_successor_splice(successor, parent, color, left, right))
            == plug(rb_successor_context(successor, parent, color, left, right, up), RbTree::Empty));
        assumption();
    }

    ensures rb_inorder(rb_successor_splice(successor, parent, color, left, right))
        == list_append(rb_inorder(left), rb_inorder(right)) by {
        apply(rb_minimum_list(right, successor, Color::Red, RbTree::Empty));
        apply(rb_erase_two_child_splice(erased, successor, parent, color, left, right));
        unfold(rb_successor_splice(successor, parent, color, left, right)); assumption();
    }

    ensures rb_parent_consistent(plug(up, rb_successor_splice(successor, parent, color, left, right)),
        root_parent) == 1 by {
        apply(ctx_consistent_node_children(up, erased, parent, color, left, right, root_parent));
        apply(rb_node_is_reflexive(parent));
        apply(rb_parent_consistent_node(erased, parent, color, left, right, parent));
        apply(rb_erase_two_child_splice_parent_consistent(erased, successor, parent, color,
            left, right, parent));
        have rb_parent_consistent(rb_successor_splice(successor, parent, color, left, right), parent) == 1 by {
            unfold(rb_successor_splice(successor, parent, color, left, right)); assumption();
        }
        apply(ctx_consistent_swap(up, erased, parent, color, left, right,
            rb_successor_splice(successor, parent, color, left, right), root_parent));
        apply(plug_parent_consistent_transport(up,
            rb_successor_splice(successor, parent, color, left, right), root_parent));
        assumption();
    }
}

# Exact leaf-successor replacement, retaining the erased node's parent and color.
function rb_erase_immediate_leaf_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match right {
            RbTree::Empty => RbTree::Empty,
            RbTree::Node(successor, sp, sc, sl, sr) =>
                rb_successor_splice(successor, parent, color, left, right),
        },
    }
}

function rb_erase_immediate_black_context(tree: RbTree, up: Context) -> Context {
    match tree {
        RbTree::Empty => up,
        RbTree::Node(node, parent, color, left, right) => match right {
            RbTree::Empty => up,
            RbTree::Node(successor, sp, sc, sl, sr) =>
                rb_successor_context(successor, parent, color, left, right, up),
        },
    }
}

# The parent whose child link is replaced when removing this subtree's minimum.
# Reparenting the subtree first makes the immediate case name the successor;
# every deeper minimum keeps its original parent.
function rb_min_parent(tree: RbTree) -> struct rb_node*
    decreases tree
{
    match tree {
        RbTree::Empty => 0,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => parent,
            RbTree::Node(a, b, c, l, r) => rb_min_parent(left),
        },
    }
}

theorem rb_min_parent_nonempty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree) {
    requires not(left == RbTree::Empty);
    ensures rb_min_parent(RbTree::Node(node, parent, color, left, right)) == rb_min_parent(left) by {
        induct(left) as cases {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_min_parent(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right))); normalize();
            }
        }
    }
}

# Reconstruct the exact cut for both empty and nonempty replacement children.
theorem rb_min_context_cut_child(tree: RbTree, up: Context, successor: struct rb_node*,
        min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    ensures plug(rb_min_context(tree, up), rb_reparent(child, rb_min_parent(tree)))
        == plug(up, rb_remove_min(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by auto;
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right,
                        successor, min_color, child));
                    extract(right == child);
                    rewrite(left == RbTree::Empty);
                    unfold(rb_min_context(RbTree::Node(node, parent, color, RbTree::Empty, right), up));
                    unfold(rb_min_parent(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    rewrite(right == child); normalize();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left, right)));
                        assumption();
                    }
                    apply(ih(left, Context::Left(node, parent, color, right, up), successor, min_color, child));
                    apply(rb_remove_min_nonempty_left(node, parent, color, left, right));
                    apply(rb_min_context_nonempty_left(node, parent, color, left, right, up));
                    apply(rb_min_parent_nonempty_left(node, parent, color, left, right));
                    rewrite(rb_min_parent(RbTree::Node(node, parent, color, left, right)) == rb_min_parent(left));
                    rewrite(rb_min_context(RbTree::Node(node, parent, color, left, right), up)
                        == rb_min_context(left, Context::Left(node, parent, color, right, up)));
                    rewrite(plug(rb_min_context(left, Context::Left(node, parent, color, right, up)),
                        rb_reparent(child, rb_min_parent(left)))
                        == plug(Context::Left(node, parent, color, right, up), rb_remove_min(left)));
                    unfold(plug(Context::Left(node, parent, color, right, up), rb_remove_min(left)));
                    rewrite(rb_remove_min(RbTree::Node(node, parent, color, left, right))
                        == RbTree::Node(node, parent, color, rb_remove_min(left), right)); normalize();
                }
            }
        }
    }
}
