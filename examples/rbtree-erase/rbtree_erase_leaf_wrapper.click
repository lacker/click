verifying "rb_erase.c";
import "rbtree_erase_color_flips_red_all.click";

function erase_leaf_result(ctx: Context, color: Color) -> RbTree {
    match color {
        Color::Red => plug(ctx, RbTree::Empty),
        Color::Black => erase_flips_red_all_result(ctx, RbTree::Empty),
    }
}

// Leaf deletion at any position: return either a balanced context or a deficit.
struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
                                    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) == RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces hole: rb_at(0);
    produces remaining: ctx_at(0, root);
    ensures hole.model == RbTree::Empty;
    ensures remaining.model == old(up.model);
    ensures ctx_consistent(remaining.model, hole.model, 0) == 1;
    ensures result != 0 implies remaining.model != Context::Top;
    ensures result != 0 implies ctx_node_is(remaining.model, result) == 1;
    ensures result != 0 implies ctx_rb(remaining.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
    ensures result == 0 implies is_rb_root(plug(remaining.model, RbTree::Empty)) == 1;
    ensures result == 0 implies erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(remaining.model, RbTree::Empty);
    ensures result != 0 implies erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(remaining.model, RbTree::Empty);
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(id, parent_model, color, left, right) => {
            have left == RbTree::Empty by {
                unfold(rb_left(RbTree::Node(id, parent_model, color, left, right)));
                rewrite(left == rb_left(RbTree::Node(id, parent_model, color, left, right)));
                rewrite(RbTree::Node(id, parent_model, color, left, right) == tree.model); assumption();
            }
            have right == RbTree::Empty by {
                unfold(rb_right(RbTree::Node(id, parent_model, color, left, right)));
                rewrite(right == rb_right(RbTree::Node(id, parent_model, color, left, right)));
                rewrite(RbTree::Node(id, parent_model, color, left, right) == tree.model); assumption();
            }
            have ctx_consistent(up.model, RbTree::Node(id, parent_model, color, left, right), 0) == 1 by {
                rewrite(RbTree::Node(id, parent_model, color, left, right) == tree.model); assumption();
            }
            apply(rb_parent_consistent_empty(parent_model));
            apply(ctx_consistent_swap(up.model, id, parent_model, color, left, right, RbTree::Empty, 0));
            let { left: l, right: r } = unfold(tree);
            unfold(l); unfold(r);
            have rb_color(old(tree.model)) == color by {
                rewrite(old(tree.model) == RbTree::Node(id, parent_model, color, left, right));
                unfold(rb_color(RbTree::Node(id, parent_model, color, left, right))); normalize();
            }
            apply(erase_context_parent(up.model, id, parent_model, color, left, right));
            have ctx_consistent(old(up.model), RbTree::Empty, 0) == 1 by { rewrite(old(up.model) == up.model); assumption(); }
            have ctx_node_is(old(up.model), parent_model) == 1 by { rewrite(old(up.model) == up.model); assumption(); }
            if color == Color::Black {
                have black_height(old(tree.model)) == Nat::Succ(Nat::Zero) by {
                    rewrite(old(tree.model) == RbTree::Node(id, parent_model, color, left, right));
                    rewrite(color == Color::Black); rewrite(left == RbTree::Empty);
                    unfold(black_height(RbTree::Node(id, parent_model, Color::Black, RbTree::Empty, right)));
                    unfold(black_height(RbTree::Empty)); normalize();
                }
                have ctx_rb(old(up.model), Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                    rewrite(Nat::Succ(Nat::Zero) == black_height(old(tree.model)));
                    rewrite(Color::Black == color);
                    rewrite(color == rb_color(old(tree.model))); assumption();
                }
                have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(old(up.model), RbTree::Empty) by {
                    rewrite(rb_color(old(tree.model)) == color); rewrite(color == Color::Black);
                    unfold(erase_leaf_result(old(up.model), Color::Black)); normalize();
                }
                have (node->__rb_parent_color & 1) == 1 by {
                    rewrite((node->__rb_parent_color & 1) == color_bit(color));
                    rewrite(color == Color::Black); unfold(color_bit(Color::Black)); normalize();
                }
                execute_until(statement(10));
                have child == 0;
                have parent == parent_model;
                have ctx_node_is(up.model, parent) == 1 by { rewrite(parent == parent_model); assumption(); }
                let { after: remaining } = step(__rb_change_child(node, child, parent, root), { before: up });
                have remaining.model == old(up.model);
                have ctx_rb(remaining.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by { rewrite(remaining.model == old(up.model)); assumption(); }
                have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(remaining.model, RbTree::Empty) by { rewrite(remaining.model == old(up.model)); assumption(); }
                match remaining.model {
                    Context::Top => {
                        have ctx_node_is(Context::Top, parent_model) == 1 by {
                            rewrite(Context::Top == remaining.model); rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have parent_model == 0 by {
                            if parent_model == 0 { assumption(); } else {
                                have ctx_node_is(Context::Top, parent_model) != 1 by {
                                    unfold(ctx_node_is(Context::Top, parent_model)); normalize() using { not(parent_model == 0); };
                                }
                                contradiction(ctx_node_is(Context::Top, parent_model) == 1);
                            }
                        }
                        have parent == 0;
                        have erase_flips_red_all_result(remaining.model, RbTree::Empty) == plug(remaining.model, RbTree::Empty) by {
                            rewrite(remaining.model == Context::Top);
                            unfold(erase_flips_red_all_result(Context::Top, RbTree::Empty));
                            unfold(plug(Context::Top, RbTree::Empty)); normalize();
                        }
                        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(remaining.model, RbTree::Empty) by {
                            rewrite(plug(remaining.model, RbTree::Empty) == erase_flips_red_all_result(remaining.model, RbTree::Empty)); assumption();
                        }
                        have is_rb_root(plug(remaining.model, RbTree::Empty)) == 1 by {
                            rewrite(remaining.model == Context::Top); unfold(plug(Context::Top, RbTree::Empty));
                            unfold(is_rb_root(RbTree::Empty)); unfold(is_rb(RbTree::Empty)); unfold(rb_root_black(RbTree::Empty)); normalize();
                        }
                        open(erase_callbacks(augment)) { execute(); }
                        let hole = fold(rb_at(0), { model: RbTree::Empty });
                        have ctx_consistent(remaining.model, hole.model, 0) == 1 by {
                            rewrite(remaining.model == old(up.model)); rewrite(hole.model == RbTree::Empty); assumption();
                        }
                        have result == 0;
                        simp();
                    },
                    Context::Left(pid, gp, pc_model, sibling_model, above_model) => {
                        have Context::Left(pid, gp, pc_model, sibling_model, above_model) == old(up.model) by {
                            rewrite(Context::Left(pid, gp, pc_model, sibling_model, above_model) == remaining.model); assumption();
                        }
                        have ctx_node_is(Context::Left(pid, gp, pc_model, sibling_model, above_model), parent_model) == 1 by {
                            rewrite(Context::Left(pid, gp, pc_model, sibling_model, above_model) == remaining.model);
                            rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have parent_model == pid by {
                            if parent_model == pid { assumption(); } else {
                                have ctx_node_is(Context::Left(pid, gp, pc_model, sibling_model, above_model), parent_model) != 1 by {
                                    unfold(ctx_node_is(Context::Left(pid, gp, pc_model, sibling_model, above_model), parent_model)); normalize() using { not(parent_model == pid); };
                                }
                                contradiction(ctx_node_is(Context::Left(pid, gp, pc_model, sibling_model, above_model), parent_model) == 1);
                            }
                        }
                        let { sibling: sibling, up: above } = unfold(remaining);
                        have parent_model != 0;
                        let remaining = fold(ctx_at(0, root), { model: Context::Left(pid, gp, pc_model, sibling_model, above_model) }, { sibling: sibling, up: above });
                        have remaining.model == old(up.model) by { rewrite(remaining.model == Context::Left(pid, gp, pc_model, sibling_model, above_model)); assumption(); }
                        open(erase_callbacks(augment)) { execute(); }
                        let hole = fold(rb_at(0), { model: RbTree::Empty });
                        have result == parent_model;
                        have ctx_rb(remaining.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                            rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have ctx_consistent(remaining.model, hole.model, 0) == 1 by {
                            rewrite(remaining.model == old(up.model)); rewrite(hole.model == RbTree::Empty); assumption();
                        }
                        have ctx_node_is(remaining.model, result) == 1 by {
                            rewrite(result == parent_model);
                            rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have result != 0;
                        have remaining.model != Context::Top by { rewrite(remaining.model == Context::Left(pid, gp, pc_model, sibling_model, above_model)); normalize(); }
                        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(remaining.model, RbTree::Empty) by { rewrite(remaining.model == old(up.model)); assumption(); }
                        simp();
                    },
                    Context::Right(pid, gp, pc_model, sibling_model, above_model) => {
                        have Context::Right(pid, gp, pc_model, sibling_model, above_model) == old(up.model) by {
                            rewrite(Context::Right(pid, gp, pc_model, sibling_model, above_model) == remaining.model); assumption();
                        }
                        have ctx_node_is(Context::Right(pid, gp, pc_model, sibling_model, above_model), parent_model) == 1 by {
                            rewrite(Context::Right(pid, gp, pc_model, sibling_model, above_model) == remaining.model);
                            rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have parent_model == pid by {
                            if parent_model == pid { assumption(); } else {
                                have ctx_node_is(Context::Right(pid, gp, pc_model, sibling_model, above_model), parent_model) != 1 by {
                                    unfold(ctx_node_is(Context::Right(pid, gp, pc_model, sibling_model, above_model), parent_model)); normalize() using { not(parent_model == pid); };
                                }
                                contradiction(ctx_node_is(Context::Right(pid, gp, pc_model, sibling_model, above_model), parent_model) == 1);
                            }
                        }
                        let { sibling: sibling, up: above } = unfold(remaining);
                        have parent_model != 0;
                        let remaining = fold(ctx_at(0, root), { model: Context::Right(pid, gp, pc_model, sibling_model, above_model) }, { sibling: sibling, up: above });
                        have remaining.model == old(up.model) by { rewrite(remaining.model == Context::Right(pid, gp, pc_model, sibling_model, above_model)); assumption(); }
                        open(erase_callbacks(augment)) { execute(); }
                        let hole = fold(rb_at(0), { model: RbTree::Empty });
                        have result == parent_model;
                        have ctx_rb(remaining.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                            rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have ctx_consistent(remaining.model, hole.model, 0) == 1 by {
                            rewrite(remaining.model == old(up.model)); rewrite(hole.model == RbTree::Empty); assumption();
                        }
                        have ctx_node_is(remaining.model, result) == 1 by {
                            rewrite(result == parent_model);
                            rewrite(remaining.model == old(up.model)); assumption();
                        }
                        have result != 0;
                        have remaining.model != Context::Top by { rewrite(remaining.model == Context::Right(pid, gp, pc_model, sibling_model, above_model)); normalize(); }
                        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(remaining.model, RbTree::Empty) by { rewrite(remaining.model == old(up.model)); assumption(); }
                        simp();
                    },
                }
            } else {
                apply(erase_color_not_black(color));
                have black_height(old(tree.model)) == Nat::Zero by {
                    rewrite(old(tree.model) == RbTree::Node(id, parent_model, color, left, right));
                    rewrite(color == Color::Red); rewrite(left == RbTree::Empty);
                    unfold(black_height(RbTree::Node(id, parent_model, Color::Red, RbTree::Empty, right)));
                    unfold(black_height(RbTree::Empty)); normalize();
                }
                have ctx_rb(old(up.model), Nat::Zero, Color::Red) == 1 by {
                    rewrite(Nat::Zero == black_height(old(tree.model)));
                    rewrite(Color::Red == color);
                    rewrite(color == rb_color(old(tree.model))); assumption();
                }
                have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(old(up.model), RbTree::Empty) by {
                    rewrite(rb_color(old(tree.model)) == color); rewrite(color == Color::Red);
                    unfold(erase_leaf_result(old(up.model), Color::Red)); normalize();
                }
                have (node->__rb_parent_color & 1) == 0 by {
                    rewrite((node->__rb_parent_color & 1) == color_bit(color));
                    rewrite(color == Color::Red); unfold(color_bit(Color::Red)); normalize();
                }
                execute_until(statement(10));
                have child == 0;
                have parent == parent_model;
                have ctx_node_is(up.model, parent) == 1 by { rewrite(parent == parent_model); assumption(); }
                let { after: remaining } = step(__rb_change_child(node, child, parent, root), { before: up });
                have remaining.model == old(up.model);
                apply(ctx_rb_black_focus(old(up.model), Nat::Zero, Color::Red));
                have is_rb(RbTree::Empty) == 1 by { unfold(is_rb(RbTree::Empty)); normalize(); }
                have ctx_rb(old(up.model), black_height(RbTree::Empty), rb_color(RbTree::Empty)) == 1 by {
                    unfold(black_height(RbTree::Empty)); unfold(rb_color(RbTree::Empty)); assumption();
                }
                apply(plug_rb_from_ctx_rb(old(up.model), RbTree::Empty));
                have is_rb_root(plug(remaining.model, RbTree::Empty)) == 1 by { rewrite(remaining.model == old(up.model)); assumption(); }
                have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(remaining.model, RbTree::Empty) by { rewrite(remaining.model == old(up.model)); assumption(); }
                open(erase_callbacks(augment)) { execute(); }
                let hole = fold(rb_at(0), { model: RbTree::Empty });
                have ctx_consistent(remaining.model, hole.model, 0) == 1 by {
                    rewrite(remaining.model == old(up.model)); rewrite(hole.model == RbTree::Empty); assumption();
                }
                have result == 0;
                simp();
            }
        },
    }
}


void rb_erase(struct rb_node* node, struct rb_root* root) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) == RbTree::Empty;
    requires rb_right(tree.model) == RbTree::Empty;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_leaf_result(old(up.model), rb_color(old(tree.model)));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(up.model), RbTree::Empty));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step(); // Declare rebalance.
    let { hole: hole, remaining: deficit } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    have deficit.model == old(up.model);
    have ctx_consistent(deficit.model, RbTree::Empty, 0) == 1 by { rewrite(RbTree::Empty == hole.model); assumption(); }
    apply(plug_parent_consistent_transport(deficit.model, RbTree::Empty, 0));
    have rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty)) == 1 by {
        unfold(rb_tree_parent_consistent(plug(deficit.model, RbTree::Empty))); assumption();
    }
    if rebalance != 0 {
        have deficit.model != Context::Top;
        have ctx_node_is(deficit.model, rebalance) == 1;
        have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
        have ctx_rb(deficit.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1 by {
            unfold(black_height(RbTree::Empty)); assumption();
        }
        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(deficit.model, RbTree::Empty);
        unfold(hole);
        step(); // Select the nonnull rebalance branch.
        mark repair;
        let { whole: whole } = step(____rb_erase_color(rebalance, root, dummy_rotate), { c: deficit });
        have whole.model == erase_leaf_result(old(up.model), rb_color(old(tree.model))) by {
            rewrite(whole.model == erase_flips_red_all_result(at(repair, deficit.model), RbTree::Empty));
            rewrite(erase_leaf_result(old(up.model), rb_color(old(tree.model))) == erase_flips_red_all_result(at(repair, deficit.model), RbTree::Empty)); normalize();
        }
        have rb_inorder(whole.model) == rb_inorder(plug(old(up.model), RbTree::Empty)) by {
            rewrite(old(up.model) == at(repair, deficit.model)); assumption();
        }
        execute(); simp();
    } else {
        have rebalance == 0;
        have is_rb_root(plug(deficit.model, RbTree::Empty)) == 1;
        have erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(deficit.model, RbTree::Empty);
        have rb_tree_parent_consistent(plug(deficit.model, hole.model)) == 1 by { rewrite(hole.model == RbTree::Empty); assumption(); }
        mark balanced;
        let { whole: whole } = refold_to_root(0, root, { c: deficit, t: hole });
        have whole.model == plug(old(up.model), RbTree::Empty) by {
            rewrite(whole.model == plug(at(balanced, deficit.model), at(balanced, hole.model)));
            rewrite(at(balanced, hole.model) == RbTree::Empty);
            rewrite(at(balanced, deficit.model) == old(up.model)); normalize();
        }
        have whole.model == erase_leaf_result(old(up.model), rb_color(old(tree.model))) by {
            rewrite(whole.model == plug(old(up.model), RbTree::Empty));
            rewrite(erase_leaf_result(old(up.model), rb_color(old(tree.model))) == plug(at(balanced, deficit.model), RbTree::Empty));
            rewrite(old(up.model) == at(balanced, deficit.model)); normalize();
        }
        have is_rb_root(whole.model) == 1 by {
            rewrite(whole.model == plug(old(up.model), RbTree::Empty));
            rewrite(old(up.model) == at(balanced, deficit.model)); assumption();
        }
        have rb_tree_parent_consistent(whole.model) == 1 by {
            rewrite(whole.model == plug(old(up.model), RbTree::Empty));
            rewrite(old(up.model) == at(balanced, deficit.model)); assumption();
        }
        have rb_inorder(whole.model) == rb_inorder(plug(old(up.model), RbTree::Empty)) by { rewrite(whole.model == plug(old(up.model), RbTree::Empty)); normalize(); }
        execute(); simp();
    }
}
