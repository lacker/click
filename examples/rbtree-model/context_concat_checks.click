// Red boundary, exact height/color matching, and whole-root blackness checks.
import "rbtree_model.click";

theorem red_boundary_fragment() {
    ensures ctx_rb_between(Context::Top, Nat::Zero, Color::Red,
        Nat::Zero, Color::Red) == 1 by {
        apply(ctx_rb_between_top(Nat::Zero, Color::Red));
        assumption();
    }

    ensures ctx_rb(Context::Top, Nat::Zero, Color::Red) == 0 by {
        unfold(ctx_rb(Context::Top, Nat::Zero, Color::Red));
        unfold(color_black(Color::Red));
        normalize();
    }

    ensures ctx_rb_between(Context::Top, Nat::Zero, Color::Red,
        Nat::Succ(Nat::Zero), Color::Red) == 0 by {
        unfold(ctx_rb_between(Context::Top, Nat::Zero, Color::Red,
            Nat::Succ(Nat::Zero), Color::Red));
        normalize();
    }

    ensures ctx_rb_between(Context::Top, Nat::Zero, Color::Red,
        Nat::Zero, Color::Black) == 0 by {
        unfold(ctx_rb_between(Context::Top, Nat::Zero, Color::Red,
            Nat::Zero, Color::Black));
        normalize();
    }
}

theorem red_boundary_under_black_parent(id: struct rb_node*, parent: struct rb_node*) {
    ensures ctx_rb(ctx_concat(Context::Top,
        Context::Left(id, parent, Color::Black, RbTree::Empty, Context::Top)),
        Nat::Zero, Color::Red) == 1 by {
        have ctx_rb(Context::Left(id, parent, Color::Black, RbTree::Empty, Context::Top),
            Nat::Zero, Color::Red) == 1 by {
            unfold(ctx_rb(Context::Left(id, parent, Color::Black,
                RbTree::Empty, Context::Top), Nat::Zero, Color::Red));
            unfold(is_rb(RbTree::Empty));
            unfold(black_height(RbTree::Empty));
            unfold(rb_color(RbTree::Empty));
            unfold(node_color_ok(Color::Black, Color::Red, Color::Black));
            unfold(frame_black_height(Color::Black, Nat::Zero));
            unfold(ctx_rb(Context::Top, Nat::Succ(Nat::Zero), Color::Black));
            unfold(color_black(Color::Black));
            normalize();
        }
        apply(ctx_rb_between_top(Nat::Zero, Color::Red));
        apply(ctx_rb_concat(Context::Top,
            Context::Left(id, parent, Color::Black, RbTree::Empty, Context::Top),
            Nat::Zero, Color::Red, Nat::Zero, Color::Red));
        assumption();
    }
}

theorem red_spine_under_black_parent(id: struct rb_node*, parent: struct rb_node*,
                                     above: struct rb_node*) {
    ensures ctx_rb(ctx_concat(
        Context::Left(id, parent, Color::Red, RbTree::Empty, Context::Top),
        Context::Right(parent, above, Color::Black, RbTree::Empty, Context::Top)),
        Nat::Zero, Color::Black) == 1 by {
        have ctx_rb_between(
            Context::Left(id, parent, Color::Red, RbTree::Empty, Context::Top),
            Nat::Zero, Color::Black, Nat::Zero, Color::Red) == 1 by {
            unfold(ctx_rb_between(
                Context::Left(id, parent, Color::Red, RbTree::Empty, Context::Top),
                Nat::Zero, Color::Black, Nat::Zero, Color::Red));
            unfold(is_rb(RbTree::Empty));
            unfold(black_height(RbTree::Empty));
            unfold(rb_color(RbTree::Empty));
            unfold(node_color_ok(Color::Red, Color::Black, Color::Black));
            unfold(color_black(Color::Black));
            unfold(frame_black_height(Color::Red, Nat::Zero));
            unfold(ctx_rb_between(Context::Top, Nat::Zero, Color::Red,
                Nat::Zero, Color::Red));
            normalize();
        }
        have ctx_rb(Context::Right(parent, above, Color::Black,
            RbTree::Empty, Context::Top), Nat::Zero, Color::Red) == 1 by {
            unfold(ctx_rb(Context::Right(parent, above, Color::Black,
                RbTree::Empty, Context::Top), Nat::Zero, Color::Red));
            unfold(is_rb(RbTree::Empty));
            unfold(black_height(RbTree::Empty));
            unfold(rb_color(RbTree::Empty));
            unfold(node_color_ok(Color::Black, Color::Black, Color::Red));
            unfold(frame_black_height(Color::Black, Nat::Zero));
            unfold(ctx_rb(Context::Top, Nat::Succ(Nat::Zero), Color::Black));
            unfold(color_black(Color::Black));
            normalize();
        }
        apply(ctx_rb_concat(
            Context::Left(id, parent, Color::Red, RbTree::Empty, Context::Top),
            Context::Right(parent, above, Color::Black, RbTree::Empty, Context::Top),
            Nat::Zero, Color::Black, Nat::Zero, Color::Red));
        assumption();
    }
}
