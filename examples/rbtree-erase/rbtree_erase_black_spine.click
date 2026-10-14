// Deletion at any tree position with a deeper black-leaf successor identifies
// the nonnull parent at which erase-color repair must begin.
verifying "rb_erase.c";
import "rbtree_erase_callbacks.click";
import "rbtree_change_child.click";

import "../rbtree-model/rbtree_spine_resources.click";

function erase_deep_context(tree: RbTree, up: Context) -> Context {
    match tree {
        RbTree::Empty => up,
        RbTree::Node(node, parent, color, left, right) => rb_successor_context(erase_minimum_identity(rb_minimum(right)), parent, color, left, right, up),
    }
}

function erase_deep_model(tree: RbTree) -> RbTree {
    match tree {
        RbTree::Empty => RbTree::Empty,
        RbTree::Node(node, parent, color, left, right) => rb_successor_splice(erase_minimum_identity(rb_minimum(right)), parent, color, left, right),
    }
}

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
            have parent == anchor by auto;
            unfold(c);
            have parent != 0;
            let frame = fold(erase_spine_frame(parent, anchor), { model: EraseSpine::Top });
            have parent->rb_left == focus;
            have frame.model == old(c.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have parent == identity by auto;
            let { sibling: sibling, up: up } = unfold(c);
            have parent != 0;
            let frame = fold(erase_spine_frame(parent, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
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
            let c = fold(erase_spine_at(focus, anchor), { model: EraseSpine::Top });
            have c.model == old(frame.model);
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: sibling, up: up } = unfold(frame);
            let c = fold(erase_spine_at(focus, anchor), {
                model: EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)
            }, { sibling: sibling, up: up });
            have c.model == old(frame.model);
        },
    }
}

tactic graft_erase_spine(focus: struct rb_node*, anchor: struct rb_node*, root: struct rb_root*) {
    consumes c: erase_spine_at(focus, anchor);
    consumes base: erase_anchor_frame(anchor, root);
    decreases erase_spine_depth(c.model);
    requires erase_spine_links(c.model, anchor) == 1;
    produces context: ctx_at(focus, root);
    ensures context.model == ctx_concat(erase_context(old(c.model)),
        erase_anchor_context(anchor, old(base.model)));
} by {
    match base.model {
        EraseAnchorFrame::At(ap, ac, ar, au) => {
    have erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au) by {
        rewrite(old(base.model) == EraseAnchorFrame::At(ap, ac, ar, au));
        unfold(erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au))); normalize();
    }
    match c.model {
        EraseSpine::Top => {
            unfold(c);
            let { right: right, up: outer_context } = unfold(base);
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(anchor, ap, ac, ar, au)
            }, { sibling: right, up: outer_context });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model) == EraseSpine::Top);
                unfold(erase_context(EraseSpine::Top));
                unfold(ctx_concat(Context::Top, Context::Left(anchor, ap, ac, ar, au)));
                simp();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by {
                rewrite(erase_anchor_context(anchor, old(base.model)) == Context::Left(anchor, ap, ac, ar, au)); assumption();
            }
        },
        EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) => {
            have erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) == 1 by {
                rewrite(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model) == old(c.model)); assumption();
            }
            unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
            have grandparent == erase_spine_parent(up_model, anchor) by {
                if grandparent == erase_spine_parent(up_model, anchor) { assumption(); } else {
                    have erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) != 1 by {
                        unfold(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor));
                        normalize() using { not(grandparent == erase_spine_parent(up_model, anchor)); }
                    }
                    contradiction(erase_spine_links(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model), anchor) == 1);
                }
            }
            have erase_spine_links(up_model, anchor) == 1 by auto;
            let { sibling: sibling, up: path_tail } = unfold(c);
            apply(erase_spine_depth_is_nonnegative(up_model));
            have erase_spine_depth(old(c.model)) == erase_spine_depth(up_model) + 1 by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_spine_depth(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model))); normalize();
            }
            have erase_spine_depth(path_tail.model) < erase_spine_depth(old(c.model)) by auto;
            mark grafting_tail;
            let { context: above } = graft_erase_spine(identity, anchor, root, { c: path_tail, base: base });
            have above.model == ctx_concat(erase_context(at(grafting_tail, path_tail.model)),
                erase_anchor_context(anchor, at(grafting_tail, base.model))) by { assumption(); }
            have erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)) == Context::Left(anchor, ap, ac, ar, au) by auto;
            have above.model == ctx_concat(erase_context(up_model),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(up_model == at(grafting_tail, path_tail.model));
                rewrite(Context::Left(anchor, ap, ac, ar, au) == erase_anchor_context(anchor, EraseAnchorFrame::At(ap, ac, ar, au)));
                rewrite(EraseAnchorFrame::At(ap, ac, ar, au) == at(grafting_tail, base.model)); assumption();
            }
            apply(erase_spine_context_parent(up_model, anchor, ap, ac, ar, au));
            let context = fold(ctx_at(focus, root), {
                model: Context::Left(identity, grandparent, color, sibling_model,
                    ctx_concat(erase_context(up_model), Context::Left(anchor, ap, ac, ar, au)))
            }, { sibling: sibling, up: above });
            have context.model == ctx_concat(erase_context(old(c.model)),
                Context::Left(anchor, ap, ac, ar, au)) by {
                rewrite(old(c.model) == EraseSpine::Left(identity, grandparent, color, sibling_model, up_model));
                unfold(erase_context(EraseSpine::Left(identity, grandparent, color, sibling_model, up_model)));
                unfold(ctx_concat(Context::Left(identity, grandparent, color, sibling_model, erase_context(up_model)),
                    Context::Left(anchor, ap, ac, ar, au)));
                simp();
            }
            have context.model == ctx_concat(erase_context(old(c.model)), erase_anchor_context(anchor, old(base.model))) by auto;
        },
    }
        },
    }
}

struct rb_node* __rb_erase_augmented(struct rb_node* node, struct rb_root* root,
    const struct rb_augment_callbacks* augment) {
    consumes tree: rb_at(node);
    consumes up: ctx_at(node, root);
    requires tree.model != RbTree::Empty;
    requires rb_left(tree.model) != RbTree::Empty;
    requires rb_right(tree.model) != RbTree::Empty;
    requires rb_left(rb_right(tree.model)) != RbTree::Empty;
    requires erase_minimum_child(rb_minimum(rb_right(tree.model))) == RbTree::Empty;
    requires erase_minimum_color(rb_minimum(rb_right(tree.model))) == Color::Black;
    requires ctx_consistent(up.model, tree.model, 0) == 1;
    requires ctx_rb(up.model, black_height(tree.model), rb_color(tree.model)) == 1;
    requires is_rb(tree.model) == 1;
    views erase_callbacks(augment);
    produces node->__rb_parent_color;
    produces node->rb_left;
    produces node->rb_right;
    produces hole: rb_at(0);
    produces deficit: ctx_at(0, root);
    ensures hole.model == RbTree::Empty;
    ensures deficit.model == erase_deep_context(old(tree.model), old(up.model));
    ensures ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1;
    ensures ctx_consistent(deficit.model, hole.model, 0) == 1;
    ensures plug(deficit.model, hole.model) == plug(old(up.model), erase_deep_model(old(tree.model)));
    ensures rb_inorder(erase_deep_model(old(tree.model)))
        == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model))));
    ensures result == rb_min_parent(rb_right(old(tree.model)));
    ensures result != 0;
    ensures deficit.model != Context::Top;
    ensures ctx_node_is(deficit.model, result) == 1;
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
            have erase_minimum_child(rb_minimum(right_model)) == RbTree::Empty by {
                rewrite(right_model == rb_right(tree.model)); assumption();
            }
            have erase_minimum_color(rb_minimum(right_model)) == Color::Black by {
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
                                        unfold(plug(old(up.model), t.model)); simp();
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
                                                    have tmp == tid by auto;
                                                    have tid != 0 by auto;
                                                    have erase_spine_parent(EraseSpine::Left(tid, tp, tc, tr, c.model), child) == tid by auto;
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
                                            have t.model == RbTree::Empty by auto;
                                            have t.model != RbTree::Empty by { rewrite(t.model == RbTree::Node(a, b, col, lt, rt)); normalize(); }
                                            contradiction(t.model == RbTree::Empty);
                                        },
                                        RbTree::Empty => {
                                            have c.model != EraseSpine::Top by auto;
                                            match c.model {
                                                EraseSpine::Top => { contradiction(c.model == EraseSpine::Top); },
                                                EraseSpine::Left(mid, mp, mc, mr, mu) => {
                                                    have plug(erase_context(c.model), t.model) == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) by {
                                                        rewrite(c.model == EraseSpine::Left(mid, mp, mc, mr, mu));
                                                        unfold(erase_context(EraseSpine::Left(mid, mp, mc, mr, mu)));
                                                        unfold(plug(Context::Left(mid, mp, mc, mr, erase_context(mu)), t.model));
                                                        rewrite(t.model == RbTree::Empty); normalize();
                                                    }
                                                    have plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)) == rl by auto;
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
                                                    have erase_minimum_child(rb_minimum(right_model)) == mr by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_child(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have erase_minimum_color(rb_minimum(right_model)) == mc by {
                                                        rewrite(rb_minimum(right_model) == RbMinimum::Found(mid, mc, mr));
                                                        unfold(erase_minimum_color(RbMinimum::Found(mid, mc, mr))); normalize();
                                                    }
                                                    have mr == RbTree::Empty by auto;
                                                    have mc == Color::Black by auto;
                                                    have rb_minimum(right_model) == RbMinimum::Found(mid, Color::Black, RbTree::Empty) by auto;
                                                    apply(rb_erase_black_successor_splice(identity, mid, parent_model, color, left_model, right_model, up.model, 0));
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
                                                    apply(erase_spine_links_from_tree(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr), rid));
                                                    apply(erase_spine_min_parent(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                    apply(rb_min_parent_nonempty_left(rid, rp, rc, rl, rr));
                                                    have rb_min_parent(right_model) == mp by {
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        rewrite(rb_min_parent(RbTree::Node(rid, rp, rc, rl, rr)) == rb_min_parent(rl));
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_min_parent(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)))
                                                            == rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        unfold(rb_min_parent(RbTree::Node(mid, mp, mc, RbTree::Empty, mr))); normalize();
                                                    }
                                                    let { sibling: min_right, up: path } = unfold(c);
                                                    have (mid->__rb_parent_color & 1) == color_bit(mc) by auto;
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
                                                    have min_right.model == RbTree::Empty by { rewrite(min_right.model == mr); assumption(); }
                                                    unfold(min_right);
                                                    have color_bit(mc) == 1 by { rewrite(mc == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                                                    have (successor->__rb_parent_color & 1) == 1;
                                                    execute_until(statement(54));
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
                                                    have (successor->__rb_parent_color & 1) == 1;
                                                    have parent->rb_left == 0;
                                                    have successor == mid;
                                                    have aligned(successor, 8);
                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                    have child == rid;
                                                    have separate(memory(child->__rb_parent_color), memory(mid->__rb_parent_color));

                                                    mark transplant;
                                                    let { after: root_context } = step(__rb_change_child(node, successor, tmp, root), { before: up });
                                                    have child->rb_right == at(transplant, child->rb_right);
                                                    have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by { normalize() using { child == rid; }; }
                                                    have parent->rb_left == at(transplant, parent->rb_left) by normalize();
                                                    have node->rb_left == lid;
                                                    have parent->rb_left == 0;
                                                    have root_context.model == at(transplant, up.model) by assumption();
                                                    have root_context.model == old(up.model);
                                                    have mid->__rb_parent_color == at(transplant, mid->__rb_parent_color);
                                                    have successor == mid;
                                                    have (successor->__rb_parent_color & 1) == 1 by {
                                                        rewrite(successor == mid); assumption();
                                                    }
                                                    mark parent_link_changed;
                                                    execute_until(statement(62));
                                                    have tmp == mid;
                                                    let hole = fold(rb_at(0), { model: RbTree::Empty });
                                                    have parent->rb_left == 0;
                                                    mark closing_spine;
                                                    let { c: path2 } = close_erase_spine_link(0, parent, child, { frame: link_frame });
                                                    have path2.model == at(closing_spine, link_frame.model) by auto;
                                                    have path2.model == mu;
                                                    apply(rb_reparent_parent_is(left_model, mid));
                                                    have rb_parent_is(rb_reparent(left_model, mid), mid) == 1 by assumption();
                                                    have mid->rb_left == lid;
                                                    have mid->rb_right == child;
                                                    let above = fold(ctx_at(child, root), {
                                                        model: Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))
                                                    }, { sibling: moved_left, up: root_context });
                                                    have ctx_node_is(above.model, mid) == 1 by {
                                                        rewrite(above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                        unfold(ctx_node_is(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                    }
                                                    have above.model == ctx_reroot(above.model, mid) by {
                                                        rewrite(above.model == Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)));
                                                        unfold(ctx_reroot(Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)), mid)); normalize();
                                                    }
                                                    have child == rid;
                                                    have tmp == mid;
                                                    have child->rb_right == at(transplant, child->rb_right) by auto;
                                                    have child->__rb_parent_color == at(transplant, child->__rb_parent_color) by auto;
                                                    have child->__rb_parent_color == address(mid) + (child->__rb_parent_color & 1);
                                                    have (child->__rb_parent_color & 1) == color_bit(rc);
                                                    have right_sibling.model == rr;
                                                    let anchor_frame = fold(erase_anchor_frame(child, root), {
                                                        model: EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                    }, { right: right_sibling, up: above });
                                                    have erase_spine_links(path2.model, child) == 1 by {
                                                        rewrite(path2.model == mu); rewrite(child == rid); assumption();
                                                    }
                                                    mark grafting;
                                                    let { context: deficit } = graft_erase_spine(0, child, root, { c: path2, base: anchor_frame });
                                                    have deficit.model == ctx_concat(erase_context(at(grafting, path2.model)),
                                                        erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))) by { assumption(); }
                                                    have at(grafting, path2.model) == mu by assumption();
                                                    have erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                        == Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))) by {
                                                        unfold(erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                            Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        rewrite(child == rid); normalize();
                                                    }
                                                    have deficit.model == ctx_concat(erase_context(mu),
                                                        Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                        rewrite(mu == at(grafting, path2.model));
                                                        rewrite(Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                            == erase_anchor_context(child, EraseAnchorFrame::At(mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        assumption();
                                                    }
                                                    apply(erase_spine_min_context(mu, RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                        Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                    apply(rb_min_context_nonempty_left(rid, mid, rc, rl, rr,
                                                        Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                    have rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                        == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                            Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))) by {
                                                        unfold(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)));
                                                        rewrite(right_model == RbTree::Node(rid, rp, rc, rl, rr));
                                                        unfold(rb_reparent(RbTree::Node(rid, rp, rc, rl, rr), mid));
                                                        rewrite(rb_min_context(RbTree::Node(rid, mid, rc, rl, rr),
                                                            Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))
                                                            == rb_min_context(rl, Context::Left(rid, mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        rewrite(rl == plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)));
                                                        rewrite(rb_min_context(plug(erase_context(mu), RbTree::Node(mid, mp, mc, RbTree::Empty, mr)),
                                                            Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))
                                                            == rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                                ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))));
                                                        unfold(rb_min_context(RbTree::Node(mid, mp, mc, RbTree::Empty, mr),
                                                            ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))))); normalize();
                                                    }
                                                    have deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model)) by {
                                                        rewrite(rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))
                                                            == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr,
                                                                Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))))); assumption();
                                                    }
                                                    have deficit.model == erase_deep_context(old(tree.model), old(up.model)) by {
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                        unfold(erase_deep_context(RbTree::Node(identity, parent_model, color, left_model, right_model), old(up.model)));
                                                        rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                    }
                                                    have ctx_rb(deficit.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
                                                        rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                    }
                                                    have ctx_consistent(deficit.model, hole.model, 0) == 1 by {
                                                        rewrite(hole.model == RbTree::Empty);
                                                        rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                    }
                                                    have plug(deficit.model, hole.model) == plug(old(up.model), erase_deep_model(old(tree.model))) by {
                                                        rewrite(hole.model == RbTree::Empty);
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                        unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                        rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid);
                                                        rewrite(deficit.model == rb_successor_context(mid, parent_model, color, left_model, right_model, old(up.model))); assumption();
                                                    }
                                                    have rb_inorder(erase_deep_model(old(tree.model))) == list_append(rb_inorder(rb_left(old(tree.model))), rb_inorder(rb_right(old(tree.model)))) by {
                                                        rewrite(old(tree.model) == RbTree::Node(identity, parent_model, color, left_model, right_model));
                                                        unfold(erase_deep_model(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                        unfold(rb_left(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                        unfold(rb_right(RbTree::Node(identity, parent_model, color, left_model, right_model)));
                                                        rewrite(erase_minimum_identity(rb_minimum(right_model)) == mid); assumption();
                                                    }
                                                    have rebalance == rb_min_parent(rb_right(old(tree.model))) by {
                                                        rewrite(rb_right(old(tree.model)) == right_model);
                                                        rewrite(rb_min_parent(right_model) == mp); simp();
                                                    }
                                                    open(erase_callbacks(augment)) { execute(); }
                                                    have result == mp;
                                                    apply(erase_spine_context_parent(mu, rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model))));
                                                    have ctx_node_is(deficit.model, result) == 1 by {
                                                        rewrite(deficit.model == ctx_concat(erase_context(mu), Context::Left(rid, mid, rc, rr, Context::Right(mid, parent_model, color, rb_reparent(left_model, mid), old(up.model)))));
                                                        rewrite(result == mp); rewrite(mp == erase_spine_parent(mu, rid)); assumption();
                                                    }
                                                    have deficit.model != Context::Top by {
                                                        if deficit.model == Context::Top {
                                                            have ctx_node_is(Context::Top, result) == 1 by { rewrite(Context::Top == deficit.model); assumption(); }
                                                            have ctx_node_is(Context::Top, result) != 1 by auto;
                                                            contradiction(ctx_node_is(Context::Top, result) == 1);
                                                        } else { assumption(); }
                                                    }
                                                    simp();
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
