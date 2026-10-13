verifying "rb_erase.c";

import "../rbtree-model/rbtree_spine_resources.click";
import "../rbtree-model/rbtree_context_depth.click";

void __rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: ctx_at(old, root);
    owns old->__rb_parent_color;
    requires old != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(before.model);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
} by {
    have old != 0 by assumption();
    match before.model {
        Context::Top => {
            have parent == 0 by {
                have ctx_node_is(Context::Top, parent) == 1 by {
                    rewrite(Context::Top == before.model); assumption();
                }
                if parent == 0 { assumption(); } else {
                    have ctx_node_is(Context::Top, parent) != 1 by {
                        unfold(ctx_node_is(Context::Top, parent)); normalize() using { not(parent == 0); };
                    }
                    contradiction(ctx_node_is(Context::Top, parent) == 1);
                }
            }
            unfold(before);
            execute();
            let after = fold(ctx_at(new, root), { model: Context::Top });
            simp();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Left(identity, grandparent, color, sibling_model, outer_model) == before.model); assumption();
                }
                if parent == identity { assumption(); } else {
                    have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            execute();
            let after = fold(ctx_at(new, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model)
            }, { sibling: sibling, up: outer });
            simp();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Right(identity, grandparent, color, sibling_model, outer_model) == before.model); assumption();
                }
                if parent == identity { assumption(); } else {
                    have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            match sibling.model {
                RbTree::Empty => {
                    unfold(sibling);
                    have identity->rb_left == 0;
                    have parent->rb_left == 0;
                    have old != 0 by assumption();
                    have parent->rb_left != old by {
                        if parent->rb_left == old {
                            have old == 0 by { normalize() using { parent->rb_left == old; parent->rb_left == 0; } }
                            contradiction(old != 0);
                        } else { assumption(); }
                    }
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { sibling: sibling, up: outer });
                    simp();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    let { left: left, right: right } = unfold(sibling);
                    execute();
                    let sibling = fold(rb_at(parent->rb_left), {
                        model: RbTree::Node(sid, sp, sc, sl, sr)
                    }, { left: left, right: right });
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model)
                    }, { sibling: sibling, up: outer });
                    simp();
                },
            }
        },
    }
}

function erase_child_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_child_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

tactic refold_to_root(focus: struct rb_node*, root: struct rb_root*) {
    consumes c: ctx_at(focus, root);
    decreases ctx_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == plug(old(c.model), old(t.model));
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let whole = fold(rb_root_at(root), { model: t.model }, { tree: t });
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model)));
                normalize();
            }
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Top);
                rewrite(plug(Context::Top, old(t.model)) == old(t.model));
                simp();
            }
        },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, up_model) == c.model);
                have rb_parent_consistent(plug(c.model, t.model), 0)
                    == rb_tree_parent_consistent(plug(c.model, t.model)) by {
                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                    normalize();
                }
                rewrite(rb_parent_consistent(plug(c.model, t.model), 0)
                    == rb_tree_parent_consistent(plug(c.model, t.model)));
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(ctx_depth_is_nonnegative(up_model));
            have 0 <= ctx_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { ctx_depth(old(c.model)) == ctx_depth(up_model) + 1; }
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                normalize();
            }
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) == plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                simp();
            }
        },
        Context::Right(identity, grandparent, color, sibling_model, up_model) => {
            have rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1 by {
                rewrite(Context::Right(identity, grandparent, color, sibling_model, up_model) == c.model);
                have rb_parent_consistent(plug(c.model, t.model), 0)
                    == rb_tree_parent_consistent(plug(c.model, t.model)) by {
                    unfold(rb_tree_parent_consistent(plug(c.model, t.model)));
                    normalize();
                }
                rewrite(rb_parent_consistent(plug(c.model, t.model), 0)
                    == rb_tree_parent_consistent(plug(c.model, t.model)));
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0)) using {
                rb_parent_consistent(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model), 0) == 1;
            }
            apply(ctx_consistent_right_focus(identity, grandparent, color, sibling_model, up_model, t.model, 0)) using {
                ctx_consistent(Context::Right(identity, grandparent, color, sibling_model, up_model), t.model, 0) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)) }, { left: s, right: t });
            apply(ctx_depth_is_nonnegative(up_model));
            have 0 <= ctx_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have ctx_depth(old(c.model)) == ctx_depth(up_model) + 1 by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                unfold(ctx_depth(Context::Right(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have ctx_depth(u.model) < ctx_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { ctx_depth(old(c.model)) == ctx_depth(up_model) + 1; }
            }
            have plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) by {
                unfold(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                normalize();
            }
            have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, sibling_model, old(t.model)));
                rewrite(plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))) == plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)));
                rewrite(Context::Right(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_to_root(identity, root, { c: u, t: sub });
            have whole.model == plug(old(c.model), old(t.model)) by {
                rewrite(old(c.model) == Context::Right(identity, grandparent, color, sibling_model, up_model));
                rewrite(plug(Context::Right(identity, grandparent, color, sibling_model, up_model), old(t.model)) == plug(up_model, RbTree::Node(identity, grandparent, color, sibling_model, old(t.model))));
                simp();
            }
        },
    }
}

tactic refold_erase_spine(focus: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    decreases erase_spine_depth(c.model);
    consumes t: rb_at(focus);
    requires rb_parent_consistent(plug(erase_context(c.model), t.model), anchor) == 1;
    produces whole: erase_left_at(anchor);
    ensures whole.model == plug(erase_context(old(c.model)), old(t.model));
} by {
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let whole = fold(erase_left_at(anchor), { model: t.model }, { tree: t });
            have plug(Context::Top, old(t.model)) == old(t.model) by {
                unfold(plug(Context::Top, old(t.model))); normalize();
            }
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model) == EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                rewrite(plug(Context::Top, old(t.model)) == old(t.model)); simp();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))
                == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) by {
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); normalize();
            }
            have rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1 by {
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) == erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == c.model);
                assumption();
            }
            apply(plug_parent_consistent_ctx(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor)) using {
                rb_parent_consistent(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model), anchor) == 1;
            }
            apply(ctx_consistent_left_focus(identity, grandparent, color, sibling_model, erase_context(up_model), t.model, anchor)) using {
                ctx_consistent(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), t.model, anchor) == 1;
            }
            apply(erase_parent_consistent_parent_is(t.model, identity)) using {
                rb_parent_consistent(t.model, identity) == 1;
            }
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { model: RbTree::Node(identity, grandparent, color, old(t.model), sibling_model) }, { left: t, right: s });
            apply(erase_spine_depth_is_nonnegative(up_model));
            have 0 <= erase_spine_depth(u.model) by {
                rewrite(u.model == up_model);
                assumption();
            }
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                normalize();
            }
            have erase_spine_depth(u.model) < erase_spine_depth(old(c.model)) by {
                rewrite(u.model == up_model);
                arithmetic() using { erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1; }
            }
            have plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) by {
                unfold(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                normalize();
            }
            have rb_parent_consistent(plug(erase_context(u.model), sub.model), anchor) == 1 by {
                rewrite(u.model == up_model);
                rewrite(sub.model == RbTree::Node(identity, grandparent, color, old(t.model), sibling_model));
                rewrite(plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)) == plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)));
                rewrite(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)) == erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model));
                assumption();
            }
            let { whole: whole } = refold_erase_spine(identity, anchor, { c: u, t: sub });
            have whole.model == plug(erase_context(old(c.model)), old(t.model)) by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                rewrite(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)) == Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)));
                rewrite(plug(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)), old(t.model)) == plug(erase_context(up_model), RbTree::Node(identity, grandparent, color, old(t.model), sibling_model)));
                simp();
            }
        },
    }
}

# A nonempty focus is still the leftmost candidate through every spine frame.

tactic open_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes c: erase_spine_at(focus, anchor);
    requires parent == erase_spine_parent(c.model, anchor);
    produces parent->rb_left;
    produces frame: erase_spine_frame(parent, anchor);
    ensures parent->rb_left == focus;
    ensures parent != 0;
    ensures frame.model == old(c.model);
} by {
    match c.model {
        EraseSpine::Top => {
            have erase_spine_parent(c.model, anchor) == anchor by {
                rewrite(c.model == EraseSpine::Top);
                unfold(erase_spine_parent(EraseSpine::Top, anchor)); normalize();
            }
            have parent == anchor by { normalize() using { } }
            unfold(c);
            have parent != 0;
            let frame = fold(erase_spine_frame(parent, anchor), { model: EraseSpine::Top });
            have parent->rb_left == focus;
            have frame.model == old(c.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_parent(c.model, anchor) == identity by {
                rewrite(c.model == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_parent(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor)); normalize();
            }
            have parent == identity by { normalize() using { } }
            let { sibling: sibling, up: up } = unfold(c);
            have parent != 0;
            let frame = fold(erase_spine_frame(parent, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have parent->rb_left == focus;
            have frame.model == old(c.model);
        },
    }
}

tactic close_erase_spine_link(focus: struct rb_node*, parent: struct rb_node*, anchor: struct rb_node*) {
    consumes parent->rb_left;
    consumes frame: erase_spine_frame(parent, anchor);
    requires parent->rb_left == focus;
    produces c: erase_spine_at(focus, anchor);
    ensures c.model == old(frame.model);
} by {
    match frame.model {
        EraseSpine::Top => {
            unfold(frame);
            have anchor->rb_left == focus;
            let c = fold(erase_spine_at(focus, anchor), { model: EraseSpine::Top });
            have c.model == old(frame.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: sibling, up: up } = unfold(frame);
            have parent != 0 by { rewrite(parent == identity); assumption(); }
            have aligned(parent, 8) by { rewrite(parent == identity); assumption(); }
            have rb_parent_is(sibling_model, parent) == 1 by { rewrite(parent == identity); assumption(); }
            let c = fold(erase_spine_at(focus, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have c.model == old(frame.model);
        },
    }
}

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
    views augment->propagate;
    views augment->copy;
    views augment->rotate;
    fact ErasePropagate(augment->propagate);
    fact EraseCopy(augment->copy);
    fact AugmentRotate(augment->rotate);
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    requires not(erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty)
        or erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Red;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires is_rb(tree.model) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces remaining: rb_root_at(root);
    ensures remaining.model == plug(old(up.model), erase_child_deep_model(old(tree.model)));
    ensures is_rb_root(remaining.model) == 1;
    ensures rb_parent_consistent(remaining.model, 0) == 1;
    ensures rb_inorder(erase_child_deep_model(old(tree.model))) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == 0;
} by {
    match tree.model {
        RbTree::Empty => { contradiction(tree.model == RbTree::Empty); },
        RbTree::Node(identity, parent_model, color, left_model, right_model) => {
            have rb_left(tree.model) == left_model by {
                rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
            }
            have rb_right(tree.model) == right_model by {
                rewrite(tree.model == RbTree::Node(identity, parent_model, color, left_model, right_model));
                unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model))); normalize();
            }
            have left_model != RbTree::Empty by { rewrite(left_model == rb_left(tree.model)); assumption(); }
            have right_model != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have not(erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty)
                or erase_minimum_color(rb_minimum(right_model)) == Color::Red by {
                rewrite(right_model == rb_right(tree.model)); assumption();
            }
            have rb_left(right_model) != RbTree::Empty by { rewrite(right_model == rb_right(tree.model)); assumption(); }
            have ctx_consistent(up.model, RbTree::Node(identity, parent_model, color, left_model, right_model), 0) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            apply(erase_context_parent(up.model, identity, parent_model, color, left_model, right_model));
            apply(ctx_consistent_node_children(up.model, identity, parent_model, color, left_model, right_model, 0));
            have is_rb(RbTree::Node(identity, parent_model, color, left_model, right_model)) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            have ctx_rb(up.model, black_height(RbTree::Node(identity, parent_model, color, left_model, right_model)), rb_color(RbTree::Node(identity, parent_model, color, left_model, right_model))) == 1 by {
                rewrite(RbTree::Node(identity, parent_model, color, left_model, right_model) == tree.model); assumption();
            }
            have rb_left(old(tree.model)) == left_model;
            have rb_right(old(tree.model)) == right_model;
            let { left: l, right: r } = unfold(tree);
            match left_model {
                RbTree::Empty => { contradiction(left_model == RbTree::Empty); },
                RbTree::Node(lid, lp, lc, ll, lr) => {
                    let { left: ll_tree, right: lr_tree } = unfold(l);
                    match right_model {
                        RbTree::Empty => { contradiction(right_model == RbTree::Empty); },
                        RbTree::Node(rid, rp, rc, rl, rr) => {
                            have rl != RbTree::Empty by {
                                unfold(rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                rewrite(rl == rb_left(RbTree::Node(rid, rp, rc, rl, rr)));
                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                            }
                            have rb_parent_consistent(RbTree::Node(rid, rp, rc, rl, rr), identity) == 1 by {
                                rewrite(RbTree::Node(rid, rp, rc, rl, rr) == right_model); assumption();
                            }
                            apply(rb_parent_consistent_node_left(rid, rp, rc, rl, rr, identity));
                            apply(rb_remove_min_blackened_parent_consistent(rl, rid));
                            let { left: t, right: right_sibling } = unfold(r);
                            match rl {
                                RbTree::Empty => { contradiction(rl == RbTree::Empty); },
                                RbTree::Node(iid, ip, ic, il, ir) => {
                                    let { left: init_l, right: init_r } = unfold(t);
                                    let t = fold(rb_at(iid), { model: RbTree::Node(iid, ip, ic, il, ir) }, { left: init_l, right: init_r });
                                    step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step(); step();
                                    let c = fold(erase_spine_at(tmp, child), { model: EraseSpine::Top });
                                    have plug(erase_context(c.model), t.model) == rl by {
                                        rewrite(c.model == EraseSpine::Top);
                                        unfold(erase_context(EraseSpine::Top));
                                        unfold(plug(Context::Top, t.model)); simp();
                                    }
                                    have successor == erase_spine_parent(c.model, child) by {
                                        rewrite(c.model == EraseSpine::Top);
                                        unfold(erase_spine_parent(EraseSpine::Top, child)); simp();
                                    }
                                    loop {
                                        owns c: erase_spine_at(tmp, child);
                                        owns t: rb_at(tmp);
                                        decreases t;
                                        invariant tmp != 0;
                                        invariant successor == erase_spine_parent(c.model, child);
                                        invariant plug(erase_context(c.model), t.model) == rl;
                                        initialize by simp;
                                        preserve by {
                                            match t.model {
                                                RbTree::Empty => { unfold(t); have tmp != 0 by { simp(); } contradiction(tmp == 0); },
                                                RbTree::Node(tid, tp, tc, tl, tr) => {
                                                    have plug(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)), tl) == rl by {
                                                        unfold(erase_context(EraseSpine::Left(tid, tp, tc, tr, c.model)));
                                                        unfold(plug(Context::Left(tid, tp, tc, tr, erase_context(c.model)), tl));
                                                        rewrite(RbTree::Node(tid, tp, tc, tl, tr) == t.model); assumption();
                                                    }
                                                    let { left: next, right: sibling } = unfold(t);
                                                    have tmp == tid by assumption();
                                                    have tid != 0 by { rewrite(tid == tmp); assumption(); }
                                                    have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by {
                                                        unfold(erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child)); normalize();
                                                    }
                                                    let frame = fold(erase_spine_at(tmp->rb_left, child),
                                                        { model: EraseSpine::Left(tid, tp, tc, tr, c.model) }, { sibling: sibling, up: c });
                                                    step(); step(); step();
                                                    have successor == erase_spine_parent(frame.model, child);
                                                    if tmp == 0 {
                                                    } else {
                                                        close_invariants();
                                                    }
                                                },
                                            }
                                        }
                                    }
                                    have node->rb_left == lid;
                                    have tmp == 0;
                                    match t.model {
                                        RbTree::Node(a, b, col, lt, rt) => {
                                            have t.model == RbTree::Empty by assumption();
                                            have t.model != RbTree::Empty by { rewrite(t.model == RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                            contradiction(t.model == RbTree::Empty);
                                        },
                                        RbTree::Empty => {
                                            have c.model != EraseSpine::Top by normalize();
                                            match c.model {
                                                EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                    have plug(erase_context(c.model), t.model) == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) by {
                                                        rewrite(c.model == EraseSpine::Left(mid, mp, mc, mr, mu));
                                                        unfold(erase_context(EraseSpine::Left(mid, mp, mc, mr, mu)));
                                                        unfold(plug(Context::Left(mid, mp, mc, mr, erase_context(mu)), t.model));
                                                        rewrite(t.model == RbTree::Empty); normalize();
                                                    }
                                                    have plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl by {
                                                        rewrite(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == plug(erase_context(c.model), t.model)); assumption();
                                                    }
                                                    have RbTree::Node(mid, mp, mc, RbTree::Empty, mr) != RbTree::Empty by normalize();
                                                    apply(erase_spine_minimum(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    have rb_minimum(rl) == RbMinimum::Found(mid, mc, mr) by {
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_minimum(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                            == rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        unfold(rb_minimum(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    apply(rb_minimum_nonempty_left(rid, rp, rc, rl, rr));
                                                    have rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr) by {
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        rewrite(rb_minimum(RbTree::Node(rid, rp, rc, rl, rr)) == rb_minimum(rl)); assumption();
                                                    }
                                                    have not(mr == RbTree::Empty) or mc == Color::Red by {
                                                        have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                            rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                            unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                        }
                                                        have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                            rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                            unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                        }
                                                        rewrite(mr == erase_minimum_child(rb_minimum(right_model)));
                                                        rewrite(mc == erase_minimum_color(rb_minimum(right_model))); assumption();
                                                    }
                                                    apply(rb_erase_no_fixup_successor_splice(identity, mid, parent_model, color,
                                                        left_model, right_model, up.model, 0, mc, mr));
                                                    apply(rb_remove_min_blackened_nonempty_left(rid, rp, rc, rl, rr));
                                                    have erase_minimum_identity(rb_minimum(right_model)) == mid by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_identity(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have rb_parent_consistent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)), rid) == 1 by {
                                                        rewrite(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl); assumption();
                                                    }
                                                    apply(erase_spine_focus_parent_consistent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                    apply(erase_parent_consistent_parent_is(RbTree::Node(mid, mp, mc, RbTree::Empty, mr), erase_spine_parent(mu, rid)));
                                                    apply(rb_parent_is_node_parent(mid, mp, mc, RbTree::Empty, mr, erase_spine_parent(mu, rid)));
                                                    apply(erase_spine_remove_min_blackened(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    have rb_remove_min_blackened(rl) == plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) by {
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_remove_min_blackened(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                                == plug(erase_context(mu), rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))));
                                                        unfold(rb_remove_min_blackened(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    let { sibling: min_right, up: path } = unfold(c);
                                                    have (mid->__rb_parent_color & 1) == color_bit(mc) by assumption();
                                                    unfold(t);
                                                    have parent == erase_spine_parent(path.model, child);
                                                    have parent == mp by {
                                                        rewrite(parent == erase_spine_parent(path.model, child));
                                                        rewrite(path.model == mu); rewrite(child == rid);
                                                        rewrite(erase_spine_parent(mu, rid) == mp); normalize();
                                                    }
                                                    have path.model == mu;
                                                    mark opened_spine;
                                                    let { frame: link_frame } = open_erase_spine_link(successor, parent, child, { c: path });
                                                    have link_frame.model == at(opened_spine, path.model) by assumption();
                                                    have link_frame.model == mu;
                                                    mark moving;
                                                    step(); step(); step(); step();
                                                    have successor == mid;
                                                    have child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid));
                                                    have aligned(successor, 8);
                                                    apply(packed_parent_word(mid, at(moving, child->__rb_parent_color)));
                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                        rewrite(child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid)));
                                                        assumption();
                                                    }
                                                    have (child->__rb_parent_color & 1) == (at(moving, child->__rb_parent_color) & 1) by {
                                                        rewrite(child->__rb_parent_color == ((at(moving, child->__rb_parent_color) & 1) | address(mid)));
                                                        assumption();
                                                    }
                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                    have node->rb_left == lid;
                                                    observe(erase_callbacks(augment));
                                                    execute_until(statement(54));
                                                    have separate(memory(child->rb_right), memory(mid->__rb_parent_color));
                                                    have separate(memory(child->rb_right), memory(mid->rb_right));
                                                    have separate(memory(child->rb_right), memory(lid->__rb_parent_color));
                                                    have separate(memory(child->rb_right), memory(node->__rb_parent_color));
                                                    have separate(memory(child->rb_right), memory(parent->rb_left));
                                                    have separate(memory(child->rb_right), memory(mid->rb_left));
                                                    have separate(memory(child->rb_right), memory(child->__rb_parent_color));
                                                    let moved_left = fold(rb_at(lid), {
                                                        model: RbTree::Node(lid, mid, lc, ll, lr)
                                                    }, { left: ll_tree, right: lr_tree });
                                                    have moved_left.model == rb_reparent(left_model, mid) by {
                                                        rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                        unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid)); normalize();
                                                    }
                                                    have tmp == parent_model;
                                                    have ctx_node_is(up.model, tmp) == 1 by {
                                                        rewrite(tmp == parent_model); assumption();
                                                    }
                                                    have successor == mid;
                                                    have aligned(successor, 8);
                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                    have child == rid;
                                                    have separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));

                                                    have parent->rb_left == child2;
                                                    mark transplant;
                                                    let { after: context } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                    have child->rb_right == at(transplant, child->rb_right);
                                                    have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by { normalize() using { child == rid; }; }
                                                    have parent->rb_left == at(transplant, parent->rb_left) by normalize();
                                                    have parent->rb_left == child2 by {
                                                        rewrite(parent->rb_left == at(transplant, parent->rb_left)); assumption();
                                                    }
                                                    have node->rb_left == lid;
                                                    have context.model == at(transplant, up.model) by assumption();
                                                    have context.model == old(up.model);
                                                    have mid->__rb_parent_color == at(transplant, mid->__rb_parent_color);
                                                    have successor == mid;
                                                    have mid->rb_left == lid;
                                                    have mid->rb_right == child;
                                                    mark parent_link_changed;
                                                    // Join the replacement link and the successor fields needed
                                                    // by the shared descent-spine and outer-context rebuild.
                                                    match min_right.model ensuring {
                                                        owns moved_link: erase_left_at(parent);
                                                        fact moved_link.model == rb_reparent(rb_recolor(mr, Color::Black), mp);
                                                        fact child->rb_right == at(transplant, child->rb_right);
                                                        fact child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                        fact (child->__rb_parent_color & 1) == color_bit(rc);
                                                        fact child->__rb_parent_color == address(mid) + color_bit(rc);
                                                        fact mid->rb_left == lid;
                                                        fact mid->rb_right == child;
                                                    } {
                                                        RbTree::Empty => {
                                                            have mr == RbTree::Empty by { rewrite(mr == min_right.model); assumption(); }
                                                            have mc == Color::Red by {
                                                                cases {
                                                                    not(mr == RbTree::Empty) => { contradiction(mr == RbTree::Empty); }
                                                                    mc == Color::Red => { assumption(); }
                                                                }
                                                            }
                                                            unfold(min_right);
                                                            have color_bit(mc) == 0 by { rewrite(mc == Color::Red); unfold(color_bit(Color::Red)); normalize(); }
                                                            have (successor->__rb_parent_color & 1) == 0 by {
                                                                rewrite(successor == mid);
                                                                rewrite(mid->__rb_parent_color == at(transplant, mid->__rb_parent_color));
                                                                rewrite((at(transplant, mid->__rb_parent_color) & 1) == color_bit(mc));
                                                                rewrite(color_bit(mc) == 0);
                                                                normalize();
                                                            }
                                                            have child2 == 0;
                                                            have parent->rb_left == 0;
                                                            execute_until(statement(62));
                                                            have parent->rb_left == 0;
                                                            let moved_child = fold(rb_at(parent->rb_left), { model: RbTree::Empty });
                                                            have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                rewrite(mr == RbTree::Empty);
                                                                unfold(rb_recolor(RbTree::Empty, Color::Black));
                                                                unfold(rb_reparent(RbTree::Empty, mp)); normalize();
                                                            }
                                                            have child->rb_right == at(transplant, child->rb_right);
                                                            have child == rid;
                                                            have tmp == mid;
                                                            have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by {
                                                                transport(at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color), child->__rb_parent_color == at(transplant, child->__rb_parent_color)) using {
                                                                    at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color);
                                                                    at(parent_link_changed, successor) == mid;
                                                                    at(parent_link_changed, child) == rid;
                                                                    separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));
                                                                    child == rid;
                                                                    tmp == mid;
                                                                };
                                                            }
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                            have (child->__rb_parent_color & 1) == color_bit(rc);
                                                            have child->__rb_parent_color == address(mid) + color_bit(rc) by {
                                                                rewrite(color_bit(rc) == (child->__rb_parent_color & 1)); assumption();
                                                            }
                                                            have mid->rb_left == lid;
                                                            have mid->rb_right == child;
                                                            let moved_link = fold(erase_left_at(parent), { model: moved_child.model }, { tree: moved_child });
                                                        },
                                                        RbTree::Node(cid, cp, cc, cl, cr) => {
                                                            have mr == RbTree::Node(cid, cp, cc, cl, cr) by { rewrite(mr == min_right.model); assumption(); }
                                                            have rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr) by {
                                                                rewrite(mr == RbTree::Node(cid, cp, cc, cl, cr));
                                                                unfold(rb_recolor(RbTree::Node(cid, cp, cc, cl, cr), Color::Black));
                                                                unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, cl, cr), mp)); normalize();
                                                            }
                                                            let { left: child_left, right: child_right } = unfold(min_right);
                                                            have child2 == cid;
                                                            have parent == mp;
                                                            have parent->rb_left == cid by { rewrite(parent == mp); simp(); }
                                                            have child_left.model == cl;
                                                            have child_right.model == cr;
                                                            have mid->rb_left == lid;
                                                            have mid->rb_right == child;
                                                            execute_until(statement(62));
                                                            have mid->rb_left == lid;
                                                            have mid->rb_right == child;
                                                            have child_left.model == cl;
                                                            have child_right.model == cr;
                                                            have cid->__rb_parent_color == (address(mp) | 1);
                                                            have aligned(mp, 8);
                                                            have ((address(mp) | 1) & 1) == 1 by { arithmetic() using { aligned(mp, 8); } }
                                                            have (cid->__rb_parent_color & 1) == color_bit(Color::Black) by {
                                                                unfold(color_bit(Color::Black));
                                                            }
                                                            have (address(mp) | 1) == address(mp) + ((address(mp) | 1) & 1) by {
                                                                arithmetic() using { aligned(mp, 8); }
                                                            }
                                                            have cid->__rb_parent_color == address(mp) + (cid->__rb_parent_color & 1) by {
                                                                rewrite(cid->__rb_parent_color == (address(mp) | 1)); assumption();
                                                            }

                                                            have parent->rb_left == cid;
                                                            let moved_child = fold(rb_at(cid), { model: RbTree::Node(cid, mp, Color::Black, cl, cr) }, { left: child_left, right: child_right });
                                                            have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp) by {
                                                                rewrite(rb_reparent(rb_recolor(mr, Color::Black), mp) == RbTree::Node(cid, mp, Color::Black, cl, cr)); normalize();
                                                            }
                                                            have child->rb_right == at(transplant, child->rb_right);
                                                            have child == rid;
                                                            have tmp == mid;
                                                            have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by {
                                                                transport(at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color), child->__rb_parent_color == at(transplant, child->__rb_parent_color)) using {
                                                                    at(parent_link_changed, child->__rb_parent_color) == at(transplant, child->__rb_parent_color);
                                                                    at(parent_link_changed, successor) == mid;
                                                                    at(parent_link_changed, child) == rid;
                                                                    separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));
                                                                    child == rid;
                                                                    tmp == mid;
                                                                };
                                                            }
                                                            have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                            have (child->__rb_parent_color & 1) == color_bit(rc);
                                                            have child->__rb_parent_color == address(mid) + color_bit(rc) by {
                                                                rewrite(color_bit(rc) == (child->__rb_parent_color & 1)); assumption();
                                                            }
                                                            have mid->rb_left == lid;
                                                            have mid->rb_right == child;
                                                            let moved_link = fold(erase_left_at(parent), { model: moved_child.model }, { tree: moved_child });
                                                        },
                                                    }
                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                    have separate(memory(child->__rb_parent_color), memory(parent->rb_left));
                                                    have child->__rb_parent_color == address(mid) + color_bit(rc);
                                                    mark replacement_joined;
                                                    let { tree: moved_child } = unfold(moved_link);
                                                    have moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp);
                                                    have child == rid;
                                                    have tmp == mid;
                                                    mark closing_spine;
                                                    let { c: path2 } = close_erase_spine_link(parent->rb_left, parent, child, { frame: link_frame });
                                                    have path2.model == at(closing_spine, link_frame.model) by assumption();
                                                    have path2.model == mu;
                                                    have rb_parent_consistent(plug(erase_context(path2.model), moved_child.model), child) == 1 by {
                                                        rewrite(path2.model == mu);
                                                        rewrite(moved_child.model == rb_reparent(rb_recolor(mr, Color::Black), mp));
                                                        rewrite(plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)) == rb_remove_min_blackened(rl));
                                                        rewrite(child == rid); assumption();
                                                    }
                                                    mark rebuilding_spine;
                                                    let { whole: whole } = refold_erase_spine(parent->rb_left, child, { c: path2, t: moved_child });
                                                    have at(rebuilding_spine, path2.model) == mu by assumption();
                                                    have whole.model == plug(erase_context(at(rebuilding_spine, path2.model)), at(rebuilding_spine, moved_child.model)) by assumption();
                                                    have at(rebuilding_spine, moved_child.model) == rb_reparent(rb_recolor(mr, Color::Black), mp) by assumption();
                                                    have whole.model == rb_remove_min_blackened(rl) by {
                                                        rewrite(rb_remove_min_blackened(rl) == plug(erase_context(mu), rb_reparent(rb_recolor(mr, Color::Black), mp)));
                                                        rewrite(rb_reparent(rb_recolor(mr, Color::Black), mp) == at(rebuilding_spine, moved_child.model));
                                                        rewrite(mu == at(rebuilding_spine, path2.model));
                                                        assumption();
                                                    }
                                                    let { tree: rebuilt_left } = unfold(whole);
                                                    have rebuilt_left.model == rb_remove_min_blackened(rl);
                                                    have right_sibling.model == rr;
                                                    apply(erase_parent_consistent_parent_is(rb_remove_min_blackened(rl), rid));
                                                    have child == rid;
                                                    have child->rb_left == rid->rb_left;
                                                    have child->rb_right == rid->rb_right;
                                                    have rid->rb_right == at(transplant, rid->rb_right);
                                                    have child->__rb_parent_color == address(mid) + color_bit(rc);
                                                    have child->__rb_parent_color == at(replacement_joined, child->__rb_parent_color);
                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1) by {
                                                        rewrite(child->__rb_parent_color == at(replacement_joined, child->__rb_parent_color)); assumption();
                                                    }
                                                    have (child->__rb_parent_color & 1) == color_bit(rc) by {
                                                        rewrite(child->__rb_parent_color == at(replacement_joined, child->__rb_parent_color)); assumption();
                                                    }
                                                    let moved_right = fold(rb_at(child), {
                                                        model: RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)
                                                    }, { left: rebuilt_left, right: right_sibling });
                                                    have rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(lid, mid, lc, ll, lr), mid)); normalize(); }
                                                    have rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid) == 1 by { unfold(rb_parent_is(RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr), mid)); normalize(); }
                                                    have mid->rb_left == lid;
                                                    have mid->rb_right == child;
                                                    let subtree = fold(rb_at(mid), {
                                                        model: RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                            RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))
                                                    }, { left: moved_left, right: moved_right });
                                                    have subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model) by {
                                                        unfold(rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                        rewrite(left_model == RbTree::Node(lid, lp, lc, ll, lr));
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        rewrite(rb_remove_min_blackened(RbTree::Node(rid, rp, rc, rl, rr)) == RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr));
                                                        unfold(rb_reparent(RbTree::Node(lid, lp, lc, ll, lr), mid));
                                                        unfold(rb_reparent(RbTree::Node(rid, rp, rc, rb_remove_min_blackened(rl), rr), mid));
                                                        normalize();
                                                    }
                                                    have subtree.model == erase_child_deep_model(old(tree.model)) by {
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                        unfold(erase_child_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                        rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                    }
                                                    have context.model == old(up.model);
                                                    have is_rb_root(plug(context.model, subtree.model)) == 1 by {
                                                        rewrite(context.model == old(up.model));
                                                        rewrite(subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model)); assumption();
                                                    }
                                                    have ctx_consistent(context.model, subtree.model, 0) == 1 by {
                                                        rewrite(context.model == old(up.model));
                                                        rewrite(subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model)); assumption();
                                                    }
                                                    have rb_inorder(subtree.model) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(subtree.model == rb_successor_child_splice(mid, parent_model, color, left_model, right_model));
                                                        rewrite(rb_left(old(tree.model)) == left_model); rewrite(rb_right(old(tree.model)) == right_model); assumption();
                                                    }
                                                    apply(plug_parent_consistent_transport(context.model, subtree.model, 0));
                                                    have rb_tree_parent_consistent(plug(context.model, subtree.model)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(context.model, subtree.model))); assumption();
                                                    }
                                                    have plug(context.model, subtree.model) == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                        rewrite(context.model == old(up.model));
                                                        rewrite(subtree.model == erase_child_deep_model(old(tree.model))); normalize();
                                                    }
                                                    have rb_inorder(erase_child_deep_model(old(tree.model))) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(erase_child_deep_model(old(tree.model)) == subtree.model); assumption();
                                                    }
                                                    mark closing_root;
                                                    let { whole: remaining } = refold_to_root(mid, root, { c: context, t: subtree });
                                                    have remaining.model == plug(old(up.model), erase_child_deep_model(old(tree.model))) by {
                                                        rewrite(remaining.model == plug(at(closing_root, context.model),
                                                            RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr))));
                                                        assumption();
                                                    }
                                                    have is_rb_root(remaining.model) == 1 by {
                                                        rewrite(remaining.model == plug(at(closing_root, context.model),
                                                            RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)))); assumption();
                                                    }
                                                    have rb_parent_consistent(remaining.model, 0) == 1 by {
                                                        rewrite(remaining.model == plug(at(closing_root, context.model),
                                                            RbTree::Node(mid, parent_model, color, RbTree::Node(lid, mid, lc, ll, lr),
                                                                RbTree::Node(rid, mid, rc, rb_remove_min_blackened(rl), rr)))); assumption();
                                                    }
                                                    have rb_inorder(erase_child_deep_model(old(tree.model))) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
                                                    observe(erase_callbacks(augment));
                                                    execute(); simp();
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

void dummy_propagate(struct rb_node* node, struct rb_node* stop) {
    ensures 1 == 1;
} by { execute(); normalize(); }
void dummy_copy(struct rb_node* old, struct rb_node* new) {
    requires old != 0;
    requires new != 0;
    ensures 1 == 1;
} by { execute(); normalize(); }
void dummy_rotate(struct rb_node* old, struct rb_node* new) {
    requires new != 0;
    ensures 1 == 1;
} by { execute(); normalize(); }

theorem dummy_propagate_contract() {
    ensures ErasePropagate(&dummy_propagate) by { unfold(ErasePropagate); simp(); }
}
theorem dummy_copy_contract() {
    ensures EraseCopy(&dummy_copy) by { unfold(EraseCopy); simp(); }
}
theorem dummy_rotate_contract() {
    ensures AugmentRotate(&dummy_rotate) by { unfold(AugmentRotate); simp(); }
}

void rb_erase(struct rb_node* node, struct rb_root* root) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    requires not(erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty)
        or erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Red;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires is_rb(tree.model) == 1;
    views dummy_callbacks.propagate;
    views dummy_callbacks.copy;
    views dummy_callbacks.rotate;
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces whole: rb_root_at(root);
    ensures whole.model == plug(old(up.model), erase_child_deep_model(old(tree.model)));
    ensures is_rb_root(whole.model) == 1;
    ensures rb_parent_consistent(whole.model, 0) == 1;
    ensures rb_inorder(erase_child_deep_model(old(tree.model))) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
} by {
    apply(dummy_propagate_contract());
    apply(dummy_copy_contract());
    apply(dummy_rotate_contract());
    fold(erase_callbacks(&dummy_callbacks));
    step();
    let { remaining: whole } = step(__rb_erase_augmented(node, root, &dummy_callbacks), { tree: tree, up: up });
    have rebalance == 0;
    execute(); simp();
}
