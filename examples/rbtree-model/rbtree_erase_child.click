import "rbtree_erase_splice.click";
import "rbtree_erase_root.click";

// The replacement child of the minimum has height zero. If nonempty,
// it is red and its parent is black; blackening it closes the hole.

theorem rb_minimum_child_valid(tree: RbTree, successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    ensures is_rb(child) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by auto;
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor,
                        min_color, child));
                    extract(right == child);
                    apply(is_rb_node_right(node, parent, color, left, right));
                    rewrite(child == right); assumption();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(ih(left, successor, min_color, child)); assumption();
                }
            }
        }
    }
}

theorem rb_minimum_child_height(tree: RbTree, successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    ensures black_height(child) == Nat::Zero by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by auto;
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor,
                        min_color, child));
                    extract(right == child);
                    apply(is_rb_node_black_heights(node, parent, color, left, right));
                    rewrite(child == right);
                    rewrite(black_height(right) == black_height(left));
                    rewrite(left == RbTree::Empty);
                    unfold(black_height(RbTree::Empty)); normalize();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(ih(left, successor, min_color, child)); assumption();
                }
            }
        }
    }
}

theorem zero_frame_is_red(color: Color, height: Nat) {
    requires frame_black_height(color, height) == Nat::Zero;
    ensures color == Color::Red by {
        induct(color) as ih {
            Color::Red => { normalize(); }
            Color::Black => {
                have not(frame_black_height(Color::Black, height) == Nat::Zero) by auto;
                contradiction(frame_black_height(Color::Black, height) == Nat::Zero);
            }
        }
    }
}

theorem nonempty_zero_height_is_red(tree: RbTree) {
    requires not(tree == RbTree::Empty);
    requires black_height(tree) == Nat::Zero;
    ensures rb_color(tree) == Color::Red by {
        induct(tree) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(black_height_node_frame(node, parent, color, left, right));
                have frame_black_height(color, black_height(left)) == Nat::Zero by auto;
                apply(zero_frame_is_red(color, black_height(left)));
                unfold(rb_color(RbTree::Node(node, parent, color, left, right))); assumption();
            }
        }
    }
}

theorem red_right_child_has_black_parent(node: struct rb_node*, parent: struct rb_node*, color: Color, left:
    RbTree, right: RbTree) {
    requires is_rb(RbTree::Node(node, parent, color, left, right)) == 1;
    requires rb_color(right) == Color::Red;
    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                apply(is_rb_red_node_right_child_is_black(node, parent, left, right));
                apply(rb_root_black_is_color_black(right));
                have not(rb_root_black(right) == 1) by {
                    rewrite(rb_root_black(right) == color_black(rb_color(right)));
                    rewrite(rb_color(right) == Color::Red);
                    unfold(color_black(Color::Red)); normalize();
                }
                contradiction(rb_root_black(right) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}

theorem rb_minimum_nonempty_child_parent_color(tree: RbTree, successor: struct rb_node*, min_color: Color,
    child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    requires not(child == RbTree::Empty);
    ensures min_color == Color::Black by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child)) by auto;
                contradiction(rb_minimum(RbTree::Empty) == RbMinimum::Found(successor, min_color, child));
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_minimum_child_height(RbTree::Node(node, parent, color, left, right), successor,
                    min_color, child));
                apply(nonempty_zero_height_is_red(child));
                if left == RbTree::Empty {
                    apply(rb_minimum_child_empty_left(node, parent, color, left, right, successor,
                        min_color, child));
                    extract(right == child);
                    extract(color == min_color);
                    have rb_color(right) == Color::Red by { rewrite(right == child); assumption(); }
                    apply(red_right_child_has_black_parent(node, parent, color, left, right));
                    rewrite(min_color == color); assumption();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left,
                            right)));
                        assumption();
                    }
                    apply(is_rb_node_left(node, parent, color, left, right));
                    apply(ih(left, successor, min_color, child)); assumption();
                }
            }
        }
    }
}


theorem blackening_red_adds_one(tree: RbTree) {
    requires rb_color(tree) == Color::Red;
    ensures black_height(rb_recolor(tree, Color::Black)) == Nat::Succ(black_height(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                have not(rb_color(RbTree::Empty) == Color::Red) by auto;
                contradiction(rb_color(RbTree::Empty) == Color::Red);
            }
            RbTree::Node(node, parent, color, left, right) => {
                have color == Color::Red by auto;
                rewrite(color == Color::Red);
                unfold(rb_recolor(RbTree::Node(node, parent, Color::Red, left, right), Color::Black));
                unfold(black_height(RbTree::Node(node, parent, Color::Black, left, right)));
                unfold(black_height(RbTree::Node(node, parent, Color::Red, left, right)));
                normalize();
            }
        }
    }
}

theorem black_color_is_black(color: Color) {
    requires color_black(color) == 1;
    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Red => {
                have not(color_black(Color::Red) == 1) by auto;
                contradiction(color_black(Color::Red) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}

theorem rb_minimum_child_blackens_without_deficit(tree: RbTree, up: Context, successor: struct rb_node*,
    min_color: Color, child: RbTree, parent: struct rb_node*) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;
    requires not(child == RbTree::Empty);
    ensures is_rb_root(plug(rb_min_context(tree, up), rb_reparent(rb_recolor(child, Color::Black), parent)))
        == 1 by {
        apply(rb_minimum_child_valid(tree, successor, min_color, child));
        apply(rb_minimum_child_height(tree, successor, min_color, child));
        apply(nonempty_zero_height_is_red(child));
        apply(rb_minimum_nonempty_child_parent_color(tree, successor, min_color, child));
        apply(rb_min_context_child(tree, up, successor, min_color, child));
        apply(blackening_red_adds_one(child));
        apply(rb_blacken_reparent_is_rb_root(child, parent));
        apply(is_rb_root_is_rb(rb_reparent(rb_recolor(child, Color::Black), parent)));
        apply(rb_reparent_preserves_black_height(rb_recolor(child, Color::Black), parent));
        apply(is_rb_root_root_black(rb_reparent(rb_recolor(child, Color::Black), parent)));
        apply(rb_root_black_is_color_black(rb_reparent(rb_recolor(child, Color::Black), parent)));
        have black_height(rb_reparent(rb_recolor(child, Color::Black), parent)) == Nat::Succ(Nat::Zero) by {
            rewrite(black_height(rb_reparent(rb_recolor(child, Color::Black), parent)) ==
                black_height(rb_recolor(child, Color::Black)));
            rewrite(black_height(rb_recolor(child, Color::Black)) == Nat::Succ(black_height(child)));
            rewrite(black_height(child) == Nat::Zero); normalize();
        }
        have ctx_rb(rb_min_context(tree, up), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
            unfold(frame_black_height(Color::Black, Nat::Zero));
            rewrite(Nat::Succ(Nat::Zero) == frame_black_height(Color::Black, Nat::Zero));
            rewrite(Color::Black == min_color); assumption();
        }
        have color_black(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by auto;
        apply(black_color_is_black(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))));
        have ctx_rb(rb_min_context(tree, up), black_height(rb_reparent(rb_recolor(child, Color::Black),
            parent)), rb_color(rb_reparent(rb_recolor(child, Color::Black), parent))) == 1 by {
            rewrite(black_height(rb_reparent(rb_recolor(child, Color::Black), parent)) ==
                Nat::Succ(Nat::Zero));
            rewrite(rb_color(rb_reparent(rb_recolor(child, Color::Black), parent)) == Color::Black);
            assumption();
        }
        apply(plug_rb_from_ctx_rb(rb_min_context(tree, up), rb_reparent(rb_recolor(child, Color::Black),
            parent)));
        assumption();
    }
}

// The immediate successor keeps its right child and blackens that child's root.
function rb_immediate_successor_child(successor: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, child: RbTree) -> RbTree {
    RbTree::Node(successor, parent, color, rb_reparent(left, successor),
        rb_reparent(rb_recolor(child, Color::Black), successor))
}

theorem rb_erase_immediate_successor_child(erased: struct rb_node*, successor: struct rb_node*,
        parent: struct rb_node*, color: Color, left: RbTree, sc: Color, child: RbTree, up: Context) {
    requires is_rb(RbTree::Node(erased, parent, color, left,
        RbTree::Node(successor, erased, sc, RbTree::Empty, child))) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left,
        RbTree::Node(successor, erased, sc, RbTree::Empty, child))), color) == 1;
    requires rb_parent_consistent(RbTree::Node(erased, parent, color, left,
        RbTree::Node(successor, erased, sc, RbTree::Empty, child)), parent) == 1;
    requires not(child == RbTree::Empty);

    ensures is_rb_root(plug(up, rb_immediate_successor_child(successor, parent, color, left, child))) == 1 by {
        apply(rb_color_node(erased, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child)));
        have ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child))),
            rb_color(RbTree::Node(erased, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child)))) == 1 by {
            rewrite(rb_color(RbTree::Node(erased, parent, color, left,
                RbTree::Node(successor, erased, sc, RbTree::Empty, child))) == color); assumption();
        }
        apply(ctx_rb_successor_right(erased, successor, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child), up));
        apply(is_rb_node_right(erased, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child)));
        apply(rb_reparent_preserves_is_rb(RbTree::Node(successor, erased, sc, RbTree::Empty, child), successor));
        unfold(rb_reparent(RbTree::Node(successor, erased, sc, RbTree::Empty, child), successor));
        have is_rb(RbTree::Node(successor, successor, sc, RbTree::Empty, child)) == 1 by {
            rewrite(RbTree::Node(successor, successor, sc, RbTree::Empty, child)
                == rb_reparent(RbTree::Node(successor, erased, sc, RbTree::Empty, child), successor));
            rewrite(is_rb(rb_reparent(RbTree::Node(successor, erased, sc, RbTree::Empty, child), successor))
                == is_rb(RbTree::Node(successor, erased, sc, RbTree::Empty, child))); assumption();
        }
        have rb_minimum(RbTree::Node(successor, successor, sc, RbTree::Empty, child))
            == RbMinimum::Found(successor, sc, child) by {
            unfold(rb_minimum(RbTree::Node(successor, successor, sc, RbTree::Empty, child))); normalize();
        }
        have ctx_rb(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
            black_height(RbTree::Node(successor, successor, sc, RbTree::Empty, child)),
            rb_color(RbTree::Node(successor, successor, sc, RbTree::Empty, child))) == 1 by {
            rewrite(RbTree::Node(successor, successor, sc, RbTree::Empty, child)
                == rb_reparent(RbTree::Node(successor, erased, sc, RbTree::Empty, child), successor)); assumption();
        }
        apply(rb_minimum_child_blackens_without_deficit(
            RbTree::Node(successor, successor, sc, RbTree::Empty, child),
            Context::Right(successor, parent, color, rb_reparent(left, successor), up),
            successor, sc, child, successor));
        have plug(rb_min_context(RbTree::Node(successor, successor, sc, RbTree::Empty, child),
            Context::Right(successor, parent, color, rb_reparent(left, successor), up)),
            rb_reparent(rb_recolor(child, Color::Black), successor))
            == plug(up, rb_immediate_successor_child(successor, parent, color, left, child)) by {
            unfold(rb_min_context(RbTree::Node(successor, successor, sc, RbTree::Empty, child),
                Context::Right(successor, parent, color, rb_reparent(left, successor), up)));
            unfold(plug(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
                rb_reparent(rb_recolor(child, Color::Black), successor)));
            unfold(rb_immediate_successor_child(successor, parent, color, left, child)); normalize();
        }
        rewrite(plug(up, rb_immediate_successor_child(successor, parent, color, left, child))
            == plug(rb_min_context(RbTree::Node(successor, successor, sc, RbTree::Empty, child),
                Context::Right(successor, parent, color, rb_reparent(left, successor), up)),
                rb_reparent(rb_recolor(child, Color::Black), successor))); assumption();
    }

    ensures rb_parent_consistent(rb_immediate_successor_child(successor, parent, color, left, child), parent) == 1 by {
        apply(rb_parent_consistent_node_left(erased, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child), parent));
        apply(rb_parent_consistent_node_right(erased, parent, color, left,
            RbTree::Node(successor, erased, sc, RbTree::Empty, child), parent));
        apply(rb_parent_consistent_node_right(successor, erased, sc, RbTree::Empty, child, erased));
        apply(rb_reparent_parent_consistent(left, erased, successor));
        apply(rb_recolor_parent_consistent(child, Color::Black, successor));
        apply(rb_reparent_parent_consistent(rb_recolor(child, Color::Black), successor, successor));
        apply(rb_node_is_reflexive(parent));
        apply(rb_parent_consistent_node(successor, parent, color, rb_reparent(left, successor),
            rb_reparent(rb_recolor(child, Color::Black), successor), parent));
        unfold(rb_immediate_successor_child(successor, parent, color, left, child)); assumption();
    }

    ensures rb_inorder(rb_immediate_successor_child(successor, parent, color, left, child))
        == list_append(rb_inorder(left), rb_inorder(RbTree::Node(successor, erased, sc, RbTree::Empty, child))) by {
        apply(rb_reparent_preserves_inorder(left, successor));
        apply(rb_reparent_preserves_inorder(rb_recolor(child, Color::Black), successor));
        apply(rb_recolor_preserves_inorder(child, Color::Black));
        apply(rb_erase_no_left_child(successor, erased, sc, child));
        unfold(rb_immediate_successor_child(successor, parent, color, left, child));
        unfold(rb_inorder(RbTree::Node(successor, parent, color, rb_reparent(left, successor),
            rb_reparent(rb_recolor(child, Color::Black), successor))));
        rewrite(rb_inorder(rb_reparent(left, successor)) == rb_inorder(left));
        rewrite(rb_inorder(rb_reparent(rb_recolor(child, Color::Black), successor)) == rb_inorder(rb_recolor(child, Color::Black)));
        rewrite(rb_inorder(rb_recolor(child, Color::Black)) == rb_inorder(child));
        rewrite(rb_inorder(RbTree::Node(successor, erased, sc, RbTree::Empty, child))
            == List<struct rb_node*>::Cons(successor, rb_inorder(child))); normalize();
    }
}

function rb_erase_immediate_child_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match right {
            RbTree::Empty => RbTree::Empty,
            RbTree::Node(successor, sp, sc, sl, child) =>
                rb_immediate_successor_child(successor, parent, color, left, child),
        },
    }
}

// The minimum's nonempty right child is blackened when it replaces the minimum.
function rb_remove_min_blackened(tree: RbTree) -> RbTree
    decreases tree
{
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => match left {
            RbTree::Empty => rb_reparent(rb_recolor(right, Color::Black), parent),
            RbTree::Node(a, b, c, l, r) =>
                RbTree::Node(node, parent, color, rb_remove_min_blackened(left), right),
        },
    }
}

theorem rb_remove_min_blackened_nonempty_left(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree) {
    requires not(left == RbTree::Empty);

    ensures rb_remove_min_blackened(RbTree::Node(node, parent, color, left, right)) == RbTree::Node(node, parent,
        color, rb_remove_min_blackened(left), right) by {
        induct(left) as ih {
            RbTree::Empty => {
                have RbTree::Empty == RbTree::Empty by auto;
                contradiction(RbTree::Empty == RbTree::Empty);
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                normalize();
            }
        }
    }
}

theorem rb_min_context_cut_blackened_child(tree: RbTree, up: Context, successor: struct rb_node*,
        min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    ensures plug(rb_min_context(tree, up), rb_reparent(rb_recolor(child, Color::Black), rb_min_parent(tree)))
        == plug(up, rb_remove_min_blackened(tree)) by {
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
                    unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    rewrite(right == child); normalize();
                } else {
                    apply(rb_minimum_nonempty_left(node, parent, color, left, right));
                    have rb_minimum(left) == RbMinimum::Found(successor, min_color, child) by {
                        rewrite(rb_minimum(left) == rb_minimum(RbTree::Node(node, parent, color, left, right)));
                        assumption();
                    }
                    apply(ih(left, Context::Left(node, parent, color, right, up), successor, min_color, child));
                    apply(rb_remove_min_blackened_nonempty_left(node, parent, color, left, right));
                    apply(rb_min_context_nonempty_left(node, parent, color, left, right, up));
                    apply(rb_min_parent_nonempty_left(node, parent, color, left, right));
                    rewrite(rb_min_parent(RbTree::Node(node, parent, color, left, right)) == rb_min_parent(left));
                    rewrite(rb_min_context(RbTree::Node(node, parent, color, left, right), up)
                        == rb_min_context(left, Context::Left(node, parent, color, right, up)));
                    rewrite(plug(rb_min_context(left, Context::Left(node, parent, color, right, up)),
                        rb_reparent(rb_recolor(child, Color::Black), rb_min_parent(left)))
                        == plug(Context::Left(node, parent, color, right, up), rb_remove_min_blackened(left)));
                    unfold(plug(Context::Left(node, parent, color, right, up), rb_remove_min_blackened(left)));
                    rewrite(rb_remove_min_blackened(RbTree::Node(node, parent, color, left, right))
                        == RbTree::Node(node, parent, color, rb_remove_min_blackened(left), right)); normalize();
                }
            }
        }
    }
}

theorem rb_remove_min_blackened_preserves_balance(tree: RbTree, up: Context,
        successor: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, min_color, child);
    requires is_rb(tree) == 1;
    requires ctx_rb(up, black_height(tree), rb_color(tree)) == 1;
    requires not(child == RbTree::Empty);
    ensures is_rb_root(plug(up, rb_remove_min_blackened(tree))) == 1 by {
        apply(rb_minimum_child_blackens_without_deficit(tree, up, successor,
            min_color, child, rb_min_parent(tree)));
        apply(rb_min_context_cut_blackened_child(tree, up, successor, min_color, child));
        rewrite(plug(up, rb_remove_min_blackened(tree)) == plug(rb_min_context(tree, up),
            rb_reparent(rb_recolor(child, Color::Black), rb_min_parent(tree))));
        assumption();
    }
}

theorem rb_remove_min_blackened_node_parent_consistent(node: struct rb_node*, parent: struct rb_node*,
                                             color: Color, left: RbTree, right: RbTree,
                                             p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(node, parent, color, left, right), p) == 1;
    requires rb_parent_consistent(rb_remove_min_blackened(left), node) == 1;

    ensures rb_parent_consistent(
        rb_remove_min_blackened(RbTree::Node(node, parent, color, left, right)), p) == 1 by {
        induct(left) as ih {
            RbTree::Empty => {
                apply(rb_parent_consistent_node_right(node, parent, color, RbTree::Empty,
                    right, p));
                apply(rb_parent_consistent_node_parent(node, parent, color, RbTree::Empty,
                    right, p));
                apply(rb_recolor_parent_consistent(right, Color::Black, node));
                apply(rb_reparent_parent_consistent_at(rb_recolor(right, Color::Black), node, parent, p));
                unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color, RbTree::Empty, right)));
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
                    rb_remove_min_blackened(RbTree::Node(inner_node, inner_parent, inner_color,
                        inner_left, inner_right)),
                    right, p));
                unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color,
                    RbTree::Node(inner_node, inner_parent, inner_color, inner_left, inner_right),
                    right)));
                assumption();
            }
        }
    }
}

theorem rb_remove_min_blackened_parent_consistent(tree: RbTree, p: struct rb_node*) {
    requires rb_parent_consistent(tree, p) == 1;

    ensures rb_parent_consistent(rb_remove_min_blackened(tree), p) == 1 by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_remove_min_blackened(RbTree::Empty));
                assumption();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_parent_consistent_node_left(node, parent, color, left, right, p));
                apply(ih(left, node));
                apply(rb_remove_min_blackened_node_parent_consistent(node, parent, color, left, right, p));
                assumption();
            }
        }
    }
}

theorem rb_remove_min_blackened_node_reparent(node: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree, new_parent: struct rb_node*) {
    ensures rb_remove_min_blackened(rb_reparent(RbTree::Node(node, parent, color, left, right), new_parent))
        == rb_reparent(rb_remove_min_blackened(RbTree::Node(node, parent, color, left, right)), new_parent) by {
        induct(left) as left_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Node(node, parent, color, RbTree::Empty, right), new_parent));
                unfold(rb_remove_min_blackened(RbTree::Node(node, new_parent, color, RbTree::Empty, right)));
                unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                apply(rb_reparent_twice(rb_recolor(right, Color::Black), parent, new_parent));
                rewrite(rb_reparent(rb_reparent(rb_recolor(right, Color::Black), parent), new_parent) == rb_reparent(rb_recolor(right, Color::Black),
                    new_parent));
                normalize();
            }
            RbTree::Node(a, b, c, l, r) => {
                unfold(rb_reparent(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right), new_parent));
                unfold(rb_remove_min_blackened(RbTree::Node(node, new_parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color,
                    RbTree::Node(a, b, c, l, r), right)));
                unfold(rb_reparent(RbTree::Node(node, parent, color,
                    rb_remove_min_blackened(RbTree::Node(a, b, c, l, r)), right), new_parent));
                normalize();
            }
        }
    }
}

theorem rb_remove_min_blackened_reparent(tree: RbTree, new_parent: struct rb_node*) {
    ensures rb_remove_min_blackened(rb_reparent(tree, new_parent))
        == rb_reparent(rb_remove_min_blackened(tree), new_parent) by {
        induct(tree) as tree_cases {
            RbTree::Empty => {
                unfold(rb_reparent(RbTree::Empty, new_parent));
                unfold(rb_remove_min_blackened(RbTree::Empty));
                unfold(rb_reparent(RbTree::Empty, new_parent));
                normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                apply(rb_remove_min_blackened_node_reparent(node, parent, color, left, right, new_parent));
                assumption();
            }
        }
    }
}


theorem rb_remove_min_blackened_preserves_inorder(tree: RbTree) {
    ensures rb_inorder(rb_remove_min_blackened(tree)) == rb_inorder(rb_remove_min(tree)) by {
        induct(tree) as ih {
            RbTree::Empty => {
                unfold(rb_remove_min_blackened(RbTree::Empty));
                unfold(rb_remove_min(RbTree::Empty)); normalize();
            }
            RbTree::Node(node, parent, color, left, right) => {
                if left == RbTree::Empty {
                    rewrite(left == RbTree::Empty);
                    unfold(rb_remove_min_blackened(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    unfold(rb_remove_min(RbTree::Node(node, parent, color, RbTree::Empty, right)));
                    apply(rb_reparent_preserves_inorder(rb_recolor(right, Color::Black), parent));
                    apply(rb_reparent_preserves_inorder(right, parent));
                    apply(rb_recolor_preserves_inorder(right, Color::Black));
                    rewrite(rb_inorder(rb_reparent(rb_recolor(right, Color::Black), parent))
                        == rb_inorder(rb_recolor(right, Color::Black)));
                    rewrite(rb_inorder(rb_recolor(right, Color::Black)) == rb_inorder(right));
                    rewrite(rb_inorder(rb_reparent(right, parent)) == rb_inorder(right)); normalize();
                } else {
                    apply(rb_remove_min_blackened_nonempty_left(node, parent, color, left, right));
                    apply(rb_remove_min_nonempty_left(node, parent, color, left, right));
                    apply(ih(left));
                    rewrite(rb_remove_min_blackened(RbTree::Node(node, parent, color, left, right))
                        == RbTree::Node(node, parent, color, rb_remove_min_blackened(left), right));
                    rewrite(rb_remove_min(RbTree::Node(node, parent, color, left, right))
                        == RbTree::Node(node, parent, color, rb_remove_min(left), right));
                    unfold(rb_inorder(RbTree::Node(node, parent, color, rb_remove_min_blackened(left), right)));
                    unfold(rb_inorder(RbTree::Node(node, parent, color, rb_remove_min(left), right)));
                    rewrite(rb_inorder(rb_remove_min_blackened(left)) == rb_inorder(rb_remove_min(left)));
                    normalize();
                }
            }
        }
    }
}

theorem rb_erase_two_child_blackened_splice_parent_consistent(erased: struct rb_node*,
                                                    successor: struct rb_node*,
                                                    parent: struct rb_node*, color: Color,
                                                    left: RbTree, right: RbTree,
                                                    p: struct rb_node*) {
    requires rb_parent_consistent(RbTree::Node(erased, parent, color, left, right), p) == 1;

    ensures rb_parent_consistent(RbTree::Node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min_blackened(right), successor)), p) == 1 by {
        apply(rb_parent_consistent_node_left(erased, parent, color, left, right, p));
        apply(rb_parent_consistent_node_right(erased, parent, color, left, right, p));
        apply(rb_parent_consistent_node_parent(erased, parent, color, left, right, p));
        apply(rb_reparent_parent_consistent(left, erased, successor));
        apply(rb_remove_min_blackened_parent_consistent(right, erased));
        apply(rb_reparent_parent_consistent(rb_remove_min_blackened(right), erased, successor));
        apply(rb_parent_consistent_node(successor, parent, color,
            rb_reparent(left, successor),
            rb_reparent(rb_remove_min_blackened(right), successor), p));
        assumption();
    }
}

function rb_successor_child_splice(successor: struct rb_node*, parent: struct rb_node*,
        color: Color, left: RbTree, right: RbTree) -> RbTree {
    RbTree::Node(successor, parent, color, rb_reparent(left, successor),
        rb_reparent(rb_remove_min_blackened(right), successor))
}

theorem rb_erase_nonempty_successor_splice(erased: struct rb_node*, successor: struct rb_node*,
        parent: struct rb_node*, color: Color, left: RbTree, right: RbTree,
        up: Context, root_parent: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(right) == RbMinimum::Found(successor, min_color, child);
    requires not(child == RbTree::Empty);
    requires is_rb(RbTree::Node(erased, parent, color, left, right)) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left, right)),
        rb_color(RbTree::Node(erased, parent, color, left, right))) == 1;
    requires ctx_consistent(up, RbTree::Node(erased, parent, color, left, right), root_parent) == 1;

    ensures is_rb_root(plug(up, rb_successor_child_splice(successor, parent, color, left, right))) == 1 by {
        apply(ctx_rb_successor_right(erased, successor, parent, color, left, right, up));
        apply(is_rb_node_right(erased, parent, color, left, right));
        apply(rb_reparent_preserves_is_rb(right, successor));
        have is_rb(rb_reparent(right, successor)) == 1 by auto;
        apply(rb_minimum_reparent(right, successor));
        have rb_minimum(rb_reparent(right, successor)) == RbMinimum::Found(successor, min_color, child) by auto;
        apply(rb_remove_min_blackened_preserves_balance(rb_reparent(right, successor),
            Context::Right(successor, parent, color, rb_reparent(left, successor), up),
            successor, min_color, child));
        apply(rb_remove_min_blackened_reparent(right, successor));
        have plug(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
                rb_remove_min_blackened(rb_reparent(right, successor)))
            == plug(up, rb_successor_child_splice(successor, parent, color, left, right)) by {
            unfold(plug(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
                rb_remove_min_blackened(rb_reparent(right, successor))));
            rewrite(rb_remove_min_blackened(rb_reparent(right, successor))
                == rb_reparent(rb_remove_min_blackened(right), successor));
            unfold(rb_successor_child_splice(successor, parent, color, left, right)); normalize();
        }
        rewrite(plug(up, rb_successor_child_splice(successor, parent, color, left, right))
            == plug(Context::Right(successor, parent, color, rb_reparent(left, successor), up),
                rb_remove_min_blackened(rb_reparent(right, successor)))); assumption();
    }

    ensures rb_inorder(rb_successor_child_splice(successor, parent, color, left, right))
        == list_append(rb_inorder(left), rb_inorder(right)) by {
        apply(rb_minimum_list(right, successor, min_color, child));
        apply(rb_erase_two_child_splice(erased, successor, parent, color, left, right));
        apply(rb_remove_min_blackened_preserves_inorder(right));
        apply(rb_reparent_preserves_inorder(rb_remove_min_blackened(right), successor));
        apply(rb_reparent_preserves_inorder(rb_remove_min(right), successor));
        have rb_inorder(rb_successor_child_splice(successor, parent, color, left, right))
            == rb_inorder(rb_successor_splice(successor, parent, color, left, right)) by {
            unfold(rb_successor_child_splice(successor, parent, color, left, right));
            unfold(rb_successor_splice(successor, parent, color, left, right));
            unfold(rb_inorder(RbTree::Node(successor, parent, color, rb_reparent(left, successor),
                rb_reparent(rb_remove_min_blackened(right), successor))));
            unfold(rb_inorder(RbTree::Node(successor, parent, color, rb_reparent(left, successor),
                rb_reparent(rb_remove_min(right), successor))));
            rewrite(rb_inorder(rb_reparent(rb_remove_min_blackened(right), successor))
                == rb_inorder(rb_remove_min_blackened(right)));
            rewrite(rb_inorder(rb_reparent(rb_remove_min(right), successor)) == rb_inorder(rb_remove_min(right)));
            rewrite(rb_inorder(rb_remove_min_blackened(right)) == rb_inorder(rb_remove_min(right))); normalize();
        }
        rewrite(rb_inorder(rb_successor_child_splice(successor, parent, color, left, right))
            == rb_inorder(rb_successor_splice(successor, parent, color, left, right)));
        unfold(rb_successor_splice(successor, parent, color, left, right)); assumption();
    }

    ensures ctx_consistent(up, rb_successor_child_splice(successor, parent, color, left, right), root_parent) == 1 by {
        apply(ctx_consistent_node_children(up, erased, parent, color, left, right, root_parent));
        apply(rb_node_is_reflexive(parent));
        apply(rb_parent_consistent_node(erased, parent, color, left, right, parent));
        apply(rb_erase_two_child_blackened_splice_parent_consistent(erased, successor, parent, color, left, right, parent));
        have rb_parent_consistent(rb_successor_child_splice(successor, parent, color, left, right), parent) == 1 by {
            unfold(rb_successor_child_splice(successor, parent, color, left, right)); assumption();
        }
        apply(ctx_consistent_swap(up, erased, parent, color, left, right,
            rb_successor_child_splice(successor, parent, color, left, right), root_parent)); assumption();
    }
}

theorem rb_remove_min_blackened_leaf(tree: RbTree, successor: struct rb_node*, color: Color) {
    requires rb_minimum(tree) == RbMinimum::Found(successor, color, RbTree::Empty);
    ensures rb_remove_min_blackened(tree) == rb_remove_min(tree) by {
        apply(rb_min_context_cut_blackened_child(tree, Context::Top, successor, color, RbTree::Empty));
        apply(rb_min_context_cut_leaf(tree, Context::Top, successor, color));
        have rb_reparent(rb_recolor(RbTree::Empty, Color::Black), rb_min_parent(tree)) == RbTree::Empty by {
            unfold(rb_recolor(RbTree::Empty, Color::Black));
            unfold(rb_reparent(RbTree::Empty, rb_min_parent(tree))); normalize();
        }
        have plug(Context::Top, rb_remove_min_blackened(tree)) == rb_remove_min_blackened(tree) by auto;
        have plug(rb_min_context(tree, Context::Top), RbTree::Empty) == rb_remove_min_blackened(tree) by auto;
        have plug(Context::Top, rb_remove_min(tree)) == rb_remove_min(tree) by auto;
        rewrite(rb_remove_min_blackened(tree) == plug(rb_min_context(tree, Context::Top), RbTree::Empty));
        rewrite(rb_remove_min(tree) == plug(Context::Top, rb_remove_min(tree)));
        assumption();
    }
}

theorem rb_erase_no_fixup_successor_splice(erased: struct rb_node*, successor: struct rb_node*,
        parent: struct rb_node*, color: Color, left: RbTree, right: RbTree,
        up: Context, root_parent: struct rb_node*, min_color: Color, child: RbTree) {
    requires rb_minimum(right) == RbMinimum::Found(successor, min_color, child);
    requires not(child == RbTree::Empty) or min_color == Color::Red;
    requires is_rb(RbTree::Node(erased, parent, color, left, right)) == 1;
    requires ctx_rb(up, black_height(RbTree::Node(erased, parent, color, left, right)),
        rb_color(RbTree::Node(erased, parent, color, left, right))) == 1;
    requires ctx_consistent(up, RbTree::Node(erased, parent, color, left, right), root_parent) == 1;

    ensures is_rb_root(plug(up, rb_successor_child_splice(successor, parent, color, left, right))) == 1
        and rb_inorder(rb_successor_child_splice(successor, parent, color, left, right))
            == list_append(rb_inorder(left), rb_inorder(right))
        and ctx_consistent(up, rb_successor_child_splice(successor, parent, color, left, right), root_parent) == 1 by {
        if child == RbTree::Empty {
            have min_color == Color::Red by {
                cases {
                    not(child == RbTree::Empty) => { contradiction(child == RbTree::Empty); }
                    min_color == Color::Red => { assumption(); }
                }
            }
            have rb_minimum(right) == RbMinimum::Found(successor, Color::Red, RbTree::Empty) by auto;
            apply(rb_erase_red_successor_splice(erased, successor, parent, color, left, right, up, root_parent));
            apply(rb_remove_min_blackened_leaf(right, successor, Color::Red));
            have rb_successor_child_splice(successor, parent, color, left, right)
                == rb_successor_splice(successor, parent, color, left, right) by {
                unfold(rb_successor_child_splice(successor, parent, color, left, right));
                unfold(rb_successor_splice(successor, parent, color, left, right));
                rewrite(rb_remove_min_blackened(right) == rb_remove_min(right)); normalize();
            }
            apply(plug_parent_consistent_ctx(up, rb_successor_splice(successor, parent, color, left, right), root_parent));
            rewrite(rb_successor_child_splice(successor, parent, color, left, right)
                == rb_successor_splice(successor, parent, color, left, right));
            simp();
        } else {
            apply(rb_erase_nonempty_successor_splice(erased, successor, parent, color, left, right, up, root_parent, min_color, child));
            simp();
        }
    }
}
