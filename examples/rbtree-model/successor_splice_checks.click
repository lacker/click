import "rbtree_erase_splice.click";

function splice_black_leaf(node: struct rb_node*, parent: struct rb_node*) -> RbTree {
    RbTree::Node(node, parent, Color::Black, RbTree::Empty, RbTree::Empty)
}

theorem splice_black_leaf_facts(node: struct rb_node*, parent: struct rb_node*) {
    ensures is_rb(splice_black_leaf(node, parent)) == 1 by {
        unfold(splice_black_leaf(node, parent));
        unfold(is_rb(RbTree::Node(node, parent, Color::Black, RbTree::Empty, RbTree::Empty)));
        unfold(is_rb(RbTree::Empty));
        normalize();
    }

    ensures black_height(splice_black_leaf(node, parent)) == Nat::Succ(Nat::Zero) by {
        unfold(splice_black_leaf(node, parent));
        unfold(black_height(RbTree::Node(node, parent, Color::Black, RbTree::Empty, RbTree::Empty)));
        unfold(black_height(RbTree::Empty));
        normalize();
    }

    ensures rb_root_black(splice_black_leaf(node, parent)) == 1 by {
        unfold(splice_black_leaf(node, parent));
        unfold(rb_root_black(RbTree::Node(node, parent, Color::Black, RbTree::Empty, RbTree::Empty)));
        normalize();
    }

    ensures rb_parent_consistent(splice_black_leaf(node, parent), parent) == 1 by {
        unfold(splice_black_leaf(node, parent));
        unfold(rb_parent_consistent(RbTree::Node(node, parent, Color::Black, RbTree::Empty, RbTree::Empty),
            parent));
        unfold(rb_parent_consistent(RbTree::Empty, node));
        unfold(rb_node_is(parent, parent));
        normalize();
    }
}

theorem immediate_successor(erased: struct rb_node*, successor: struct rb_node*, l: struct rb_node*, above:
    struct rb_node*) {
    ensures ctx_rb(rb_successor_context(successor, above, Color::Black, splice_black_leaf(l, erased),
        splice_black_leaf(successor, erased), Context::Top), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
        apply(splice_black_leaf_facts(l, erased));
        apply(splice_black_leaf_facts(successor, erased));
        have black_height(splice_black_leaf(l, erased)) == black_height(splice_black_leaf(successor,
            erased)) by {
            rewrite(black_height(splice_black_leaf(l, erased)) == Nat::Succ(Nat::Zero));
            rewrite(black_height(splice_black_leaf(successor, erased)) == Nat::Succ(Nat::Zero));
            normalize();
        }
        apply(is_rb_black_node(erased, above, splice_black_leaf(l, erased), splice_black_leaf(successor,
            erased)));
        have ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black,
            splice_black_leaf(l, erased), splice_black_leaf(successor, erased))),
            rb_color(RbTree::Node(erased, above, Color::Black, splice_black_leaf(l, erased),
            splice_black_leaf(successor, erased)))) == 1 by {
            unfold(rb_color(RbTree::Node(erased, above, Color::Black, splice_black_leaf(l, erased),
                splice_black_leaf(successor, erased))));
            unfold(ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black,
                splice_black_leaf(l, erased), splice_black_leaf(successor, erased))), Color::Black));
            unfold(color_black(Color::Black));
            normalize();
        }
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(erased, above, Color::Black, splice_black_leaf(l, erased),
            splice_black_leaf(successor, erased), above));
        apply(ctx_consistent_top_frame(RbTree::Node(erased, above, Color::Black, splice_black_leaf(l,
            erased), splice_black_leaf(successor, erased)), above));
        have rb_minimum(splice_black_leaf(successor, erased)) == RbMinimum::Found(successor, Color::Black,
            RbTree::Empty) by {
            unfold(splice_black_leaf(successor, erased));
            unfold(rb_minimum(RbTree::Node(successor, erased, Color::Black, RbTree::Empty, RbTree::Empty)));
            normalize();
        }
        apply(rb_erase_black_successor_splice(erased, successor, above, Color::Black,
            splice_black_leaf(l, erased), splice_black_leaf(successor, erased), Context::Top, above));
        assumption();
    }

    ensures rb_successor_context(successor, above, Color::Black, splice_black_leaf(l, erased),
        splice_black_leaf(successor, erased), Context::Top) == Context::Right(successor, above,
        Color::Black, rb_reparent(splice_black_leaf(l, erased), successor), Context::Top) by {
        unfold(rb_successor_context(successor, above, Color::Black, splice_black_leaf(l, erased),
            splice_black_leaf(successor, erased), Context::Top));
        unfold(splice_black_leaf(successor, erased));
        unfold(rb_reparent(RbTree::Node(successor, erased, Color::Black, RbTree::Empty, RbTree::Empty),
            successor));
        unfold(rb_min_context(RbTree::Node(successor, successor, Color::Black, RbTree::Empty,
            RbTree::Empty), Context::Right(successor, above, Color::Black, rb_reparent(splice_black_leaf(l,
            erased), successor), Context::Top)));
        normalize();
    }
}

theorem deep_red_right_subtree(erased: struct rb_node*, successor: struct rb_node*, l: struct rb_node*,
    above: struct rb_node*, r: struct rb_node*, far: struct rb_node*) {
    ensures ctx_rb(rb_successor_context(successor, above, Color::Black, splice_black_leaf(l, erased),
        RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r), splice_black_leaf(far, r)),
        Context::Top), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
        apply(splice_black_leaf_facts(l, erased));
        apply(splice_black_leaf_facts(successor, r));
        apply(splice_black_leaf_facts(far, r));
        have black_height(splice_black_leaf(successor, r)) == black_height(splice_black_leaf(far, r)) by {
            rewrite(black_height(splice_black_leaf(successor, r)) == Nat::Succ(Nat::Zero));
            rewrite(black_height(splice_black_leaf(far, r)) == Nat::Succ(Nat::Zero));
            normalize();
        }
        apply(is_rb_red_node(r, erased, splice_black_leaf(successor, r), splice_black_leaf(far, r)));
        apply(rb_node_is_reflexive(erased));
        apply(rb_parent_consistent_node(r, erased, Color::Red,
            splice_black_leaf(successor, r), splice_black_leaf(far, r), erased));
        have black_height(splice_black_leaf(l, erased)) == black_height(RbTree::Node(r, erased, Color::Red,
            splice_black_leaf(successor, r), splice_black_leaf(far, r))) by {
            rewrite(black_height(splice_black_leaf(l, erased)) == Nat::Succ(Nat::Zero));
            unfold(black_height(RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r),
                splice_black_leaf(far, r))));
            rewrite(black_height(splice_black_leaf(successor, r)) == Nat::Succ(Nat::Zero));
            normalize();
        }
        apply(is_rb_black_node(erased, above, splice_black_leaf(l, erased), RbTree::Node(r, erased,
            Color::Red, splice_black_leaf(successor, r), splice_black_leaf(far, r))));
        have ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black,
            splice_black_leaf(l, erased), RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor,
            r), splice_black_leaf(far, r)))), rb_color(RbTree::Node(erased, above, Color::Black,
            splice_black_leaf(l, erased), RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor,
            r), splice_black_leaf(far, r))))) == 1 by {
            unfold(rb_color(RbTree::Node(erased, above, Color::Black, splice_black_leaf(l, erased),
                RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r), splice_black_leaf(far,
                r)))));
            unfold(ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black,
                splice_black_leaf(l, erased), RbTree::Node(r, erased, Color::Red,
                splice_black_leaf(successor, r), splice_black_leaf(far, r)))), Color::Black));
            unfold(color_black(Color::Black));
            normalize();
        }
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(erased, above, Color::Black, splice_black_leaf(l, erased),
            RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r), splice_black_leaf(far, r)),
            above));
        apply(ctx_consistent_top_frame(RbTree::Node(erased, above, Color::Black, splice_black_leaf(l,
            erased), RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r),
            splice_black_leaf(far, r))), above));
        have rb_minimum(RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r),
            splice_black_leaf(far, r))) == RbMinimum::Found(successor, Color::Black, RbTree::Empty) by {
            unfold(splice_black_leaf(successor, r));
            unfold(rb_minimum(RbTree::Node(r, erased, Color::Red,
                RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Empty),
                    splice_black_leaf(far, r))));
            unfold(rb_minimum(RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Empty)));
            normalize();
        }
        apply(rb_erase_black_successor_splice(erased, successor, above, Color::Black,
            splice_black_leaf(l, erased), RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor,
                r), splice_black_leaf(far, r)), Context::Top, above));
        assumption();
    }

    ensures rb_successor_context(successor, above, Color::Black, splice_black_leaf(l, erased),
        RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r), splice_black_leaf(far, r)),
        Context::Top) == Context::Left(r, successor, Color::Red, splice_black_leaf(far, r),
        Context::Right(successor, above, Color::Black, rb_reparent(splice_black_leaf(l, erased), successor),
        Context::Top)) by {
        unfold(rb_successor_context(successor, above, Color::Black, splice_black_leaf(l, erased),
            RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r), splice_black_leaf(far, r)),
            Context::Top));
        unfold(rb_reparent(RbTree::Node(r, erased, Color::Red, splice_black_leaf(successor, r),
            splice_black_leaf(far, r)), successor));
        unfold(splice_black_leaf(successor, r));
        unfold(rb_min_context(RbTree::Node(r, successor, Color::Red,
            RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Empty), splice_black_leaf(far,
                r)), Context::Right(successor, above, Color::Black, rb_reparent(splice_black_leaf(l,
                erased), successor), Context::Top)));
        unfold(rb_min_context(RbTree::Node(successor, r, Color::Black, RbTree::Empty, RbTree::Empty),
            Context::Left(r, successor, Color::Red, splice_black_leaf(far, r), Context::Right(successor,
            above, Color::Black, rb_reparent(splice_black_leaf(l, erased), successor), Context::Top))));
        normalize();
    }
}

// The empty cursor has height zero, but the context needs one missing black.
theorem immediate_successor_rejects_zero_height(erased: struct rb_node*,
        successor: struct rb_node*, l: struct rb_node*, above: struct rb_node*) {
    ensures ctx_rb(rb_successor_context(successor, above, Color::Black,
        splice_black_leaf(l, erased), splice_black_leaf(successor, erased), Context::Top),
        Nat::Zero, Color::Black) == 0 by {
        apply(immediate_successor(erased, successor, l, above));
        apply(splice_black_leaf_facts(l, erased));
        apply(rb_reparent_preserves_black_height(splice_black_leaf(l, erased), successor));
        have not(black_height(rb_reparent(splice_black_leaf(l, erased), successor)) == Nat::Zero) by {
            rewrite(black_height(rb_reparent(splice_black_leaf(l, erased), successor))
                == black_height(splice_black_leaf(l, erased)));
            rewrite(black_height(splice_black_leaf(l, erased)) == Nat::Succ(Nat::Zero));
            normalize();
        }
        apply(rb_reparent_preserves_is_rb(splice_black_leaf(l, erased), successor));
        have is_rb(rb_reparent(splice_black_leaf(l, erased), successor)) == 1 by auto;
        rewrite(rb_successor_context(successor, above, Color::Black,
                splice_black_leaf(l, erased), splice_black_leaf(successor, erased), Context::Top)
            == Context::Right(successor, above, Color::Black,
                rb_reparent(splice_black_leaf(l, erased), successor), Context::Top));
        unfold(ctx_rb(Context::Right(successor, above, Color::Black,
            rb_reparent(splice_black_leaf(l, erased), successor), Context::Top), Nat::Zero, Color::Black));
        normalize() using {
            is_rb(rb_reparent(splice_black_leaf(l, erased), successor)) == 1;
            not(black_height(rb_reparent(splice_black_leaf(l, erased), successor)) == Nat::Zero);
        }
    }
}

// A red successor needs no black-deficit fixup; a successor with a child takes
// the separate child-recoloring branch. Neither satisfies the leaf theorem.
theorem other_successor_cases(successor: struct rb_node*, parent: struct rb_node*,
                              child: struct rb_node*) {
    ensures not(rb_minimum(RbTree::Node(successor, parent, Color::Red, RbTree::Empty, RbTree::Empty))
        == RbMinimum::Found(successor, Color::Black, RbTree::Empty)) by {
        unfold(rb_minimum(RbTree::Node(successor, parent, Color::Red, RbTree::Empty, RbTree::Empty)));
        normalize();
    }

    ensures not(rb_minimum(RbTree::Node(successor, parent, Color::Black, RbTree::Empty,
            RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty)))
        == RbMinimum::Found(successor, Color::Black, RbTree::Empty)) by {
        unfold(rb_minimum(RbTree::Node(successor, parent, Color::Black, RbTree::Empty,
            RbTree::Node(child, successor, Color::Red, RbTree::Empty, RbTree::Empty))));
        normalize();
    }
}

function splice_red_leaf(node: struct rb_node*, parent: struct rb_node*) -> RbTree {
    RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)
}

theorem splice_red_leaf_facts(node: struct rb_node*, parent: struct rb_node*) {
    ensures is_rb(splice_red_leaf(node, parent)) == 1 by {
        unfold(splice_red_leaf(node, parent));
        unfold(is_rb(RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)));
        unfold(is_rb(RbTree::Empty));
        unfold(rb_root_black(RbTree::Empty));
        normalize();
    }

    ensures black_height(splice_red_leaf(node, parent)) == Nat::Zero by {
        unfold(splice_red_leaf(node, parent));
        unfold(black_height(RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)));
        unfold(black_height(RbTree::Empty));
        normalize();
    }

    ensures rb_root_black(splice_red_leaf(node, parent)) == 0 by {
        unfold(splice_red_leaf(node, parent));
        unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty)));
        normalize();
    }

    ensures rb_parent_consistent(splice_red_leaf(node, parent), parent) == 1 by {
        unfold(splice_red_leaf(node, parent));
        unfold(rb_parent_consistent(RbTree::Node(node, parent, Color::Red, RbTree::Empty, RbTree::Empty),
            parent));
        unfold(rb_parent_consistent(RbTree::Empty, node));
        unfold(rb_node_is(parent, parent));
        normalize();
    }
}

theorem immediate_red_successor(erased: struct rb_node*, successor: struct rb_node*, l: struct rb_node*,
    above: struct rb_node*) {
    ensures is_rb_root(plug(Context::Top, rb_successor_splice(successor, above, Color::Black,
        splice_red_leaf(l, erased), splice_red_leaf(successor, erased)))) == 1 by {
        apply(splice_red_leaf_facts(l, erased));
        apply(splice_red_leaf_facts(successor, erased));
        have black_height(splice_red_leaf(l, erased)) == black_height(splice_red_leaf(successor, erased)) by
            {
            rewrite(black_height(splice_red_leaf(l, erased)) == Nat::Zero);
            rewrite(black_height(splice_red_leaf(successor, erased)) == Nat::Zero);
            normalize();
        }
        apply(is_rb_black_node(erased, above, splice_red_leaf(l, erased), splice_red_leaf(successor,
            erased)));
        have ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black, splice_red_leaf(l,
            erased), splice_red_leaf(successor, erased))), rb_color(RbTree::Node(erased, above,
            Color::Black, splice_red_leaf(l, erased), splice_red_leaf(successor, erased)))) == 1 by {
            unfold(rb_color(RbTree::Node(erased, above, Color::Black, splice_red_leaf(l, erased),
                splice_red_leaf(successor, erased))));
            unfold(ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black,
                splice_red_leaf(l, erased), splice_red_leaf(successor, erased))), Color::Black));
            unfold(color_black(Color::Black));
            normalize();
        }
        apply(rb_node_is_reflexive(above));
        apply(rb_parent_consistent_node(erased, above, Color::Black, splice_red_leaf(l, erased),
            splice_red_leaf(successor, erased), above));
        apply(ctx_consistent_top_frame(RbTree::Node(erased, above, Color::Black, splice_red_leaf(l, erased),
            splice_red_leaf(successor, erased)), above));
        have rb_minimum(splice_red_leaf(successor, erased)) == RbMinimum::Found(successor, Color::Red,
            RbTree::Empty) by {
            unfold(splice_red_leaf(successor, erased));
            unfold(rb_minimum(RbTree::Node(successor, erased, Color::Red, RbTree::Empty, RbTree::Empty)));
            normalize();
        }
        apply(rb_erase_red_successor_splice(erased, successor, above, Color::Black, splice_red_leaf(l,
            erased), splice_red_leaf(successor, erased), Context::Top, above));
        assumption();
    }
}

theorem deep_red_successor(erased: struct rb_node*, successor: struct rb_node*, l: struct rb_node*, above:
    struct rb_node*, r: struct rb_node*) {
    ensures is_rb_root(plug(Context::Top, rb_successor_splice(successor, above, Color::Black,
        RbTree::Node(l, erased, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased,
        Color::Black, RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty),
        RbTree::Empty)))) == 1 by {
        have is_rb(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased, Color::Black,
            RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r,
            Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty))) == 1 by {
            unfold(is_rb(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased, Color::Black,
                RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black, RbTree::Node(successor,
                r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty))));
            unfold(black_height(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased,
                Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
                RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty))));
            unfold(rb_root_black(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased,
                Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
                RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty))));
            unfold(is_rb(RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r, Color::Red,
                RbTree::Empty, RbTree::Empty), RbTree::Empty)));
            unfold(black_height(RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r, Color::Red,
                RbTree::Empty, RbTree::Empty), RbTree::Empty)));
            unfold(rb_root_black(RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r,
                Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty)));
            unfold(is_rb(RbTree::Node(l, erased, Color::Black, RbTree::Empty, RbTree::Empty)));
            unfold(black_height(RbTree::Node(l, erased, Color::Black, RbTree::Empty, RbTree::Empty)));
            unfold(rb_root_black(RbTree::Node(l, erased, Color::Black, RbTree::Empty, RbTree::Empty)));
            unfold(is_rb(RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(black_height(RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(rb_root_black(RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty)));
            unfold(is_rb(RbTree::Empty));
            unfold(black_height(RbTree::Empty));
            unfold(rb_root_black(RbTree::Empty));
            normalize();
        }
        have rb_parent_consistent(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased,
            Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
            RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty)), above) ==
        1 by {
            unfold(rb_parent_consistent(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased,
                Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
                RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty)),
                above));
            unfold(rb_parent_consistent(RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r,
                Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty), erased));
            unfold(rb_parent_consistent(RbTree::Node(l, erased, Color::Black, RbTree::Empty, RbTree::Empty),
                erased));
            unfold(rb_parent_consistent(RbTree::Node(successor, r, Color::Red, RbTree::Empty,
                RbTree::Empty), r));
            unfold(rb_parent_consistent(RbTree::Empty, r));
            unfold(rb_parent_consistent(RbTree::Empty, l));
            unfold(rb_parent_consistent(RbTree::Empty, successor));
            unfold(rb_node_is(r, r));
            unfold(rb_node_is(erased, erased));
            unfold(rb_node_is(above, above));
            normalize();
        }
        apply(ctx_consistent_top_frame(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased,
            Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
            RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty)), above));
        have ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black, RbTree::Node(l,
            erased, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
            RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty))),
            rb_color(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased, Color::Black,
            RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r,
            Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty)))) == 1 by
        {
            unfold(ctx_rb(Context::Top, black_height(RbTree::Node(erased, above, Color::Black,
                RbTree::Node(l, erased, Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased,
                Color::Black, RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty),
                RbTree::Empty))), rb_color(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased,
                Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
                RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty)))));
            unfold(rb_color(RbTree::Node(erased, above, Color::Black, RbTree::Node(l, erased, Color::Black,
                RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black, RbTree::Node(successor,
                r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty))));
            unfold(color_black(Color::Black)); normalize();
        }
        have rb_minimum(RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r, Color::Red,
            RbTree::Empty, RbTree::Empty), RbTree::Empty)) == RbMinimum::Found(successor, Color::Red,
            RbTree::Empty) by {
            unfold(rb_minimum(RbTree::Node(r, erased, Color::Black, RbTree::Node(successor, r, Color::Red,
                RbTree::Empty, RbTree::Empty), RbTree::Empty)));
            unfold(rb_minimum(RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty)));
                normalize();
        }
        apply(rb_erase_red_successor_splice(erased, successor, above, Color::Black, RbTree::Node(l, erased,
            Color::Black, RbTree::Empty, RbTree::Empty), RbTree::Node(r, erased, Color::Black,
            RbTree::Node(successor, r, Color::Red, RbTree::Empty, RbTree::Empty), RbTree::Empty),
            Context::Top, above));
        assumption();
    }
}
