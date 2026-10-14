verifying "rb_erase_augmented.c";

import "../rbtree-model/rbtree_resources.click";
import "../rbtree-model/rbtree_erase_root.click";

contract void AugmentRotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
}

contract void ErasePropagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
}

contract void EraseCopy(struct rb_node* node, struct rb_node* successor) {
    requires node != 0;
    requires successor != 0;
    ensures 1 == 1;
}

resource erase_callbacks(augment: const struct rb_augment_callbacks*) {
    owns augment->propagate;
    owns augment->copy;
    owns augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

// Red-leaf deletion below the root, retaining a balanced context.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) == RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires rb_color(tree.model) == Color::Red;
    requires up.model != Context::Top;
    requires ctx_rb(up.model, Nat::Zero, Color::Red) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    owns erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces hole: rb_at(0);
    produces remaining: ctx_at(0, root);
    ensures hole.model == RbTree::Empty;
    ensures remaining.model == old(up.model);
    ensures ctx_rb(remaining.model, Nat::Zero, Color::Black) == 1;
    ensures ctx_consistent(remaining.model, hole.model, 0) == 1;
    ensures result == 0;
} by {
    apply(ctx_rb_black_focus(up.model, Nat::Zero, Color::Red));
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(id, parent, color, left, right) => {
            have left == RbTree::Empty by {
                unfold(rb_left(RbTree::Node(id, parent, color, left, right)));
                rewrite(left == rb_left(RbTree::Node(id, parent, color, left, right)));
                rewrite(RbTree::Node(id, parent, color, left, right) == tree.model); assumption();
            }
            have right == RbTree::Empty by {
                unfold(rb_right(RbTree::Node(id, parent, color, left, right)));
                rewrite(right == rb_right(RbTree::Node(id, parent, color, left, right)));
                rewrite(RbTree::Node(id, parent, color, left, right) == tree.model); assumption();
            }
            have color == Color::Red by {
                unfold(rb_color(RbTree::Node(id, parent, color, left, right)));
                rewrite(color == rb_color(RbTree::Node(id, parent, color, left, right)));
                rewrite(RbTree::Node(id, parent, color, left, right) == tree.model); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(id, parent, color, left, right), 0) == 1 by {
                rewrite(RbTree::Node(id, parent, color, left, right) == tree.model); assumption();
            }
            apply(rb_parent_consistent_empty(parent));
            apply(ctx_consistent_swap(up.model, id, parent, color, left, right, RbTree::Empty, 0));
            let { left: l, right: r } = unfold(tree);
            unfold(l); unfold(r);
            have (node->__rb_parent_color & 1) == 0 by {
                rewrite((node->__rb_parent_color & 1) == color_bit(color));
                rewrite(color == Color::Red); unfold(color_bit(Color::Red)); normalize();
            }
            match up.model {
                Context::Top => { contradiction(up.model == Context::Top); },
                Context::Left(pid, gp, pc, sibling_model, above_model) => {
                    have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model),
                        RbTree::Node(id, parent, color, left, right), 0) == 1 by {
                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                    }
                    apply(ctx_consistent_left_focus(pid, gp, pc, sibling_model, above_model,
                        RbTree::Node(id, parent, color, left, right), 0));
                    apply(rb_parent_consistent_node_fixes_parent(id, parent, color, left, right, pid));
                    have ctx_rb(Context::Left(pid, gp, pc, sibling_model, above_model), Nat::Zero, Color::Black) == 1 by auto;
                    have ctx_consistent(Context::Left(pid, gp, pc, sibling_model, above_model), RbTree::Empty, 0) == 1 by {
                        rewrite(Context::Left(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                    }
                    let { sibling: sibling, up: above } = unfold(up);
                    unfold(erase_callbacks(augment));
                    execute();
                    fold(erase_callbacks(augment));
                    let hole = fold(rb_at(0), { model: RbTree::Empty });
                    let remaining = fold(ctx_at(0, root), {
                        model: Context::Left(pid, gp, pc, sibling_model, above_model)
                    }, { sibling: sibling, up: above });
                    simp();
                },
                Context::Right(pid, gp, pc, sibling_model, above_model) => {
                    have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model),
                        RbTree::Node(id, parent, color, left, right), 0) == 1 by {
                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                    }
                    apply(ctx_consistent_right_focus(pid, gp, pc, sibling_model, above_model,
                        RbTree::Node(id, parent, color, left, right), 0));
                    apply(rb_parent_consistent_node_fixes_parent(id, parent, color, left, right, pid));
                    have ctx_rb(Context::Right(pid, gp, pc, sibling_model, above_model), Nat::Zero, Color::Black) == 1 by {
                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                    }
                    have ctx_consistent(Context::Right(pid, gp, pc, sibling_model, above_model), RbTree::Empty, 0) == 1 by {
                        rewrite(Context::Right(pid, gp, pc, sibling_model, above_model) == up.model); assumption();
                    }
                    let { sibling: sibling, up: above } = unfold(up);
                    match sibling.model {
                        RbTree::Empty => {
                            unfold(sibling);
                            unfold(erase_callbacks(augment));
                            execute();
                            fold(erase_callbacks(augment));
                            let sibling = fold(rb_at(0), { model: RbTree::Empty });
                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                            let remaining = fold(ctx_at(0, root), {
                                model: Context::Right(pid, gp, pc, sibling_model, above_model)
                            }, { sibling: sibling, up: above });
                            simp();
                        },
                        RbTree::Node(sid, sp, sc, sl, sr) => {
                            let { left: sl_tree, right: sr_tree } = unfold(sibling);
                            unfold(erase_callbacks(augment));
                            execute();
                            fold(erase_callbacks(augment));
                            let sibling = fold(rb_at(sid), { model: RbTree::Node(sid, sp, sc, sl, sr) }, { left: sl_tree, right: sr_tree });
                            let hole = fold(rb_at(0), { model: RbTree::Empty });
                            let remaining = fold(ctx_at(0, root), {
                                model: Context::Right(pid, gp, pc, sibling_model, above_model)
                            }, { sibling: sibling, up: above });
                            simp();
                        },
                    }
                },
            }
        },
    }
}
