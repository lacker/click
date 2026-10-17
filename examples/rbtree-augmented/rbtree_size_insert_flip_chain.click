// Arbitrarily many insertion color flips, ending at the root or a black parent.
verifying "rb_insert_augmented.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_insert_flips.click";

void __rb_insert(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_flip_state(root);
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    match state.model {
        SizedTree::Empty => { unfold(state); contradiction(false); },
        SizedTree::Node(identity, ancestor, shade, value, left, right) => {
            have node == identity by {
                rewrite(node == sized_flip_node(state.model));
                rewrite(state.model == SizedTree::Node(identity, ancestor, shade, value, left, right));
                unfold(sized_flip_node(SizedTree::Node(identity, ancestor, shade, value, left, right))); normalize();
            }
            have color_bit(shade) == 0 by {
                unfold(sized_flip_color(SizedTree::Node(identity, ancestor, shade, value, left, right)));
                rewrite(color_bit(shade) == sized_flip_color(SizedTree::Node(identity, ancestor, shade, value, left, right)));
                rewrite(SizedTree::Node(identity, ancestor, shade, value, left, right) == state.model); assumption();
            }
            let { focus: focus, path: path } = unfold(state);
            let { metadata: metadata, left: l, right: r } = unfold(focus);
            have node->__rb_parent_color == address(ancestor) by {
                rewrite(node->__rb_parent_color == address(ancestor) + (node->__rb_parent_color & 1));
                rewrite((node->__rb_parent_color & 1) == color_bit(shade));
                rewrite(color_bit(shade) == 0); normalize();
            }
            step(); step(); step(); step();
            let focus = fold(sized_at(node), { model: SizedTree::Node(identity, ancestor, shade, value, left, right) }, { metadata: metadata, left: l, right: r });
            let state = fold(sized_flip_state(root), { chain: old(state.chain), model: old(state.model), context: old(state.context) }, { focus: focus, path: path });
            apply(sized_flip_context_parent(state.chain));
            apply(sized_flip_depth_nonnegative(state.chain));
            have parent == sized_flip_parent(state.chain) by {
                rewrite(parent == ancestor);
                rewrite(ancestor == sized_context_parent(state.context, 0));
                rewrite(state.context == sized_flip_context(state.chain)); assumption();
            }
            loop {
                owns state: sized_flip_state(root);
                decreases sized_flip_depth(state.chain);
                invariant sized_flip_allowed(state.chain) == 1;
                invariant state.context == sized_flip_context(state.chain);
                invariant node == sized_flip_node(state.model);
                invariant sized_flip_color(state.model) == 0;
                invariant parent == sized_flip_parent(state.chain);
                invariant sized_flip_result(state.chain, state.model) == sized_flip_result(old(state.chain), old(state.model));
                initialize by simp();
                preserve by {
                    mark iteration;
                    match state.model {
                        SizedTree::Empty => { unfold(state); contradiction(false); },
                        SizedTree::Node(current, above, red, count, lo, hi) => {
                            have node == current by {
                                rewrite(node == sized_flip_node(state.model));
                                rewrite(state.model == SizedTree::Node(current, above, red, count, lo, hi));
                                unfold(sized_flip_node(SizedTree::Node(current, above, red, count, lo, hi))); normalize();
                            }
                            have color_bit(red) == 0 by {
                                unfold(sized_flip_color(SizedTree::Node(current, above, red, count, lo, hi)));
                                rewrite(color_bit(red) == sized_flip_color(SizedTree::Node(current, above, red, count, lo, hi)));
                                rewrite(SizedTree::Node(current, above, red, count, lo, hi) == state.model); assumption();
                            }
                            let { focus: focus, path: path } = unfold(state);
                            apply(sized_flip_context_parent(at(iteration,state.chain)));
                            have parent == above by {
                                rewrite(parent == sized_flip_parent(at(iteration,state.chain)));
                                rewrite(sized_flip_parent(at(iteration,state.chain)) == sized_context_parent(sized_flip_context(at(iteration,state.chain)),0));
                                rewrite(sized_flip_context(at(iteration,state.chain)) == at(iteration,state.context)); assumption();
                            }
                            match at(iteration,state.chain) {
                                SizedFlipChain::LL(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model == at(iteration,state.context));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent == sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); normalize(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain) == SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Black); unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); normalize(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::LL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); normalize();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by assumption();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { assumption(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                normalize() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g) == 0); normalize();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by assumption();
                                                    have p != u by assumption();
                                                    mark before_recolor;
                                                    have p->rb_left != p by assumption();
                                                    have p->rb_right != p by assumption();
                                                    have g->rb_left != g by assumption();
                                                    have g->rb_right != g by assumption();
                                                    have u->rb_left != u by assumption();
                                                    have u->rb_right != u by assumption();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1) == color_bit(uc));
                                                        rewrite(uc == Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1) == color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red) == 0); normalize();
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have tmp == u by assumption();
                                                    have parent == p by assumption();
                                                    have parent != tmp by assumption();
                                                    step();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        transport(at(before_recolor, (u->__rb_parent_color & 1) == 0), (tmp->__rb_parent_color & 1) == 0);
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have p->rb_left != p by { transport(at(before_recolor,p->rb_left != p), p->rb_left != p); }
                                                    have p->rb_right != p by { transport(at(before_recolor,p->rb_right != p), p->rb_right != p); }
                                                    have g->rb_left != g by { transport(at(before_recolor,g->rb_left != g), g->rb_left != g); }
                                                    have g->rb_right != g by { transport(at(before_recolor,g->rb_right != g), g->rb_right != g); }
                                                    have u->rb_left != u by { transport(at(before_recolor,u->rb_left != u), u->rb_left != u); }
                                                    have u->rb_right != u by { transport(at(before_recolor,u->rb_right != u), u->rb_right != u); }
                                                    let uncle_tree = fold(sized_at(u), { model: SizedTree::Node(u, g, Color::Black, uv, ul, ur) }, { metadata: u_size, left: u_left, right: u_right });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(at(iteration,state.model))) + to_integer(sized_value(other)) by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); assumption();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other) }, { metadata: p_size, left: focus, right: other_tree });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur)) }, { metadata: g_size, left: parent_tree, right: uncle_tree });
                                                    let state = fold(sized_flip_state(root), { chain: up, model: focus.model, context: sized_flip_context(up) }, { focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by assumption();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain == up);
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LL(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::LL(p, g, pv, gv, other, uncle, up))); arithmetic();
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    step();
                                                    close_invariants() by simp();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::LR(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Left(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model == at(iteration,state.context));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent == sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); normalize(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain) == SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Black); unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); normalize(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::LR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); normalize();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by assumption();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { assumption(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                normalize() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g) == 0); normalize();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by assumption();
                                                    have p != u by assumption();
                                                    mark before_recolor;
                                                    have p->rb_left != p by assumption();
                                                    have p->rb_right != p by assumption();
                                                    have g->rb_left != g by assumption();
                                                    have g->rb_right != g by assumption();
                                                    have u->rb_left != u by assumption();
                                                    have u->rb_right != u by assumption();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1) == color_bit(uc));
                                                        rewrite(uc == Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1) == color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red) == 0); normalize();
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        transport(at(before_recolor, (u->__rb_parent_color & 1) == 0), (tmp->__rb_parent_color & 1) == 0);
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have p->rb_left != p by { transport(at(before_recolor,p->rb_left != p), p->rb_left != p); }
                                                    have p->rb_right != p by { transport(at(before_recolor,p->rb_right != p), p->rb_right != p); }
                                                    have g->rb_left != g by { transport(at(before_recolor,g->rb_left != g), g->rb_left != g); }
                                                    have g->rb_right != g by { transport(at(before_recolor,g->rb_right != g), g->rb_right != g); }
                                                    have u->rb_left != u by { transport(at(before_recolor,u->rb_left != u), u->rb_left != u); }
                                                    have u->rb_right != u by { transport(at(before_recolor,u->rb_right != u), u->rb_right != u); }
                                                    let uncle_tree = fold(sized_at(u), { model: SizedTree::Node(u, g, Color::Black, uv, ul, ur) }, { metadata: u_size, left: u_left, right: u_right });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(other)) + to_integer(sized_value(at(iteration,state.model))) by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); assumption();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)) }, { metadata: p_size, left: other_tree, right: focus });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur)) }, { metadata: g_size, left: parent_tree, right: uncle_tree });
                                                    let state = fold(sized_flip_state(root), { chain: up, model: focus.model, context: sized_flip_context(up) }, { focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by assumption();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain == up);
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::LR(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::LR(p, g, pv, gv, other, uncle, up))); arithmetic();
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), SizedTree::Node(u, g, Color::Black, uv, ul, ur))));
                                                    step();
                                                    close_invariants() by simp();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::RL(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Left(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model == at(iteration,state.context));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent == sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); normalize(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain) == SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Black); unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); normalize(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::RL(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); normalize();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by assumption();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { assumption(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                normalize() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g) == 0); normalize();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by assumption();
                                                    have p != u by assumption();
                                                    mark before_recolor;
                                                    have p->rb_left != p by assumption();
                                                    have p->rb_right != p by assumption();
                                                    have g->rb_left != g by assumption();
                                                    have g->rb_right != g by assumption();
                                                    have u->rb_left != u by assumption();
                                                    have u->rb_right != u by assumption();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1) == color_bit(uc));
                                                        rewrite(uc == Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1) == color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red) == 0); normalize();
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        transport(at(before_recolor, (u->__rb_parent_color & 1) == 0), (tmp->__rb_parent_color & 1) == 0);
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have p->rb_left != p by { transport(at(before_recolor,p->rb_left != p), p->rb_left != p); }
                                                    have p->rb_right != p by { transport(at(before_recolor,p->rb_right != p), p->rb_right != p); }
                                                    have g->rb_left != g by { transport(at(before_recolor,g->rb_left != g), g->rb_left != g); }
                                                    have g->rb_right != g by { transport(at(before_recolor,g->rb_right != g), g->rb_right != g); }
                                                    have u->rb_left != u by { transport(at(before_recolor,u->rb_left != u), u->rb_left != u); }
                                                    have u->rb_right != u by { transport(at(before_recolor,u->rb_right != u), u->rb_right != u); }
                                                    let uncle_tree = fold(sized_at(u), { model: SizedTree::Node(u, g, Color::Black, uv, ul, ur) }, { metadata: u_size, left: u_left, right: u_right });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(at(iteration,state.model))) + to_integer(sized_value(other)) by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); assumption();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other) }, { metadata: p_size, left: focus, right: other_tree });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other)) }, { metadata: g_size, left: uncle_tree, right: parent_tree });
                                                    let state = fold(sized_flip_state(root), { chain: up, model: focus.model, context: sized_flip_context(up) }, { focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by assumption();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain == up);
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RL(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::RL(p, g, pv, gv, other, uncle, up))); arithmetic();
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, at(iteration,state.model), other))));
                                                    step();
                                                    close_invariants() by simp();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::RR(p, g, pv, gv, other, uncle, up) => {
                                    have path.model == SizedContext::Right(p, g, Color::Red, pv, other, SizedContext::Right(g, sized_flip_parent(up), Color::Black, gv, uncle, sized_flip_context(up))) by {
                                        rewrite(path.model == at(iteration,state.context));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_context(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    let { metadata: p_size, sibling: other_tree, up: g_path } = unfold(path);
                                    let { metadata: g_size, sibling: uncle_tree, up: outer_path } = unfold(g_path);
                                    have parent == p by {
                                        rewrite(parent == sized_flip_parent(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                        unfold(sized_flip_parent(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); normalize();
                                    }
                                    match uncle {
                                        SizedTree::Empty => {
                                            unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                            unfold(sized_flip_uncle_red(SizedTree::Empty));
                                            have sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Empty); unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, SizedTree::Empty, up))); unfold(sized_flip_uncle_red(SizedTree::Empty)); normalize(); }
                                            have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                rewrite(at(iteration,state.chain) == SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                                rewrite(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                            }
                                            contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                        },
                                        SizedTree::Node(u, ug, uc, uv, ul, ur) => {
                                            match uc {
                                                Color::Black => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == 0 by { rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Black); unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Black, uv, ul, ur), up))); unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Black, uv, ul, ur))); normalize(); }
                                                    have not (sized_flip_allowed(at(iteration,state.chain)) == 1) by {
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                                        rewrite(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == 0); normalize();
                                                    }
                                                    contradiction(sized_flip_allowed(at(iteration,state.chain)) == 1);
                                                },
                                                Color::Red => {
                                                    unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                                    unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)) == sized_flip_allowed(up) by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur)); rewrite(uc == Color::Red);
                                                        unfold(sized_flip_allowed(SizedFlipChain::RR(p, g, pv, gv, other, SizedTree::Node(u, ug, Color::Red, uv, ul, ur), up)));
                                                        unfold(sized_flip_uncle_red(SizedTree::Node(u, ug, Color::Red, uv, ul, ur))); normalize();
                                                    }
                                                    have sized_flip_allowed(up) == 1 by assumption();
                                                    let { metadata: u_size, left: u_left, right: u_right } = unfold(uncle_tree);
                                                    have ug == g by {
                                                        if ug == g { assumption(); } else {
                                                            have sized_parent_is(uncle,g) == 0 by {
                                                                rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                                unfold(sized_parent_is(SizedTree::Node(u, ug, uc, uv, ul, ur),g));
                                                                normalize() using { not (ug == g); };
                                                            }
                                                            have not (sized_parent_is(uncle,g) == 1) by {
                                                                rewrite(sized_parent_is(uncle,g) == 0); normalize();
                                                            }
                                                            contradiction(sized_parent_is(uncle,g) == 1);
                                                        }
                                                    }
                                                    have separate(memory(p->__rb_parent_color), memory(u->__rb_parent_color)) by assumption();
                                                    have p != u by assumption();
                                                    mark before_recolor;
                                                    have p->rb_left != p by assumption();
                                                    have p->rb_right != p by assumption();
                                                    have g->rb_left != g by assumption();
                                                    have g->rb_right != g by assumption();
                                                    have u->rb_left != u by assumption();
                                                    have u->rb_right != u by assumption();
                                                    unfold(color_bit(Color::Red)); unfold(color_bit(Color::Black));
                                                    have (u->__rb_parent_color & 1) == 0 by {
                                                        rewrite((u->__rb_parent_color & 1) == color_bit(uc));
                                                        rewrite(uc == Color::Red);
                                                        unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have p->__rb_parent_color == address(g) by {
                                                        rewrite(p->__rb_parent_color == address(g) + (p->__rb_parent_color & 1));
                                                        rewrite((p->__rb_parent_color & 1) == color_bit(Color::Red));
                                                        rewrite(color_bit(Color::Red) == 0); normalize();
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have (tmp->__rb_parent_color & 1) == 0 by {
                                                        transport(at(before_recolor, (u->__rb_parent_color & 1) == 0), (tmp->__rb_parent_color & 1) == 0);
                                                    }
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    step();
                                                    have p->rb_left != p by { transport(at(before_recolor,p->rb_left != p), p->rb_left != p); }
                                                    have p->rb_right != p by { transport(at(before_recolor,p->rb_right != p), p->rb_right != p); }
                                                    have g->rb_left != g by { transport(at(before_recolor,g->rb_left != g), g->rb_left != g); }
                                                    have g->rb_right != g by { transport(at(before_recolor,g->rb_right != g), g->rb_right != g); }
                                                    have u->rb_left != u by { transport(at(before_recolor,u->rb_left != u), u->rb_left != u); }
                                                    have u->rb_right != u by { transport(at(before_recolor,u->rb_right != u), u->rb_right != u); }
                                                    let uncle_tree = fold(sized_at(u), { model: SizedTree::Node(u, g, Color::Black, uv, ul, ur) }, { metadata: u_size, left: u_left, right: u_right });
                                                    have sized_parent_is(at(iteration,state.model), p) == 1 by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi),p));
                                                        normalize() using { above == p; };
                                                    }
                                                    unfold(sized_value(at(iteration,state.model)));
                                                    have to_integer(pv) == 1 + to_integer(sized_value(other)) + to_integer(sized_value(at(iteration,state.model))) by {
                                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                        unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); assumption();
                                                    }
                                                    let parent_tree = fold(sized_at(p), { model: SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)) }, { metadata: p_size, left: other_tree, right: focus });
                                                    unfold(sized_parent_is(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)), g));
                                                    unfold(sized_value(SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))));
                                                    unfold(sized_parent_is(SizedTree::Node(u, g, Color::Black, uv, ul, ur), g));
                                                    unfold(sized_value(SizedTree::Node(u, g, Color::Black, uv, ul, ur)));
                                                    unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur)));
                                                    have sized_value(uncle) == uv by {
                                                        rewrite(uncle == SizedTree::Node(u, ug, uc, uv, ul, ur));
                                                        unfold(sized_value(SizedTree::Node(u, ug, uc, uv, ul, ur))); normalize();
                                                    }
                                                    let focus = fold(sized_at(g), { model: SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model))) }, { metadata: g_size, left: uncle_tree, right: parent_tree });
                                                    let state = fold(sized_flip_state(root), { chain: up, model: focus.model, context: sized_flip_context(up) }, { focus: focus, path: outer_path });
                                                    unfold(sized_flip_result(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up), at(iteration,state.model)));
                                                    unfold(sized_recolor(SizedTree::Node(u, ug, uc, uv, ul, ur),Color::Black));
                                                    have sized_flip_result(state.chain,state.model) == sized_flip_result(old(state.chain),old(state.model)) by assumption();
                                                    apply(sized_flip_depth_nonnegative(up));
                                                    unfold(sized_flip_depth(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up)));
                                                    have sized_flip_depth(state.chain) < sized_flip_depth(at(iteration,state.chain)) by {
                                                        rewrite(state.chain == up);
                                                        rewrite(at(iteration,state.chain) == SizedFlipChain::RR(p, g, pv, gv, other, uncle, up));
                                                        unfold(sized_flip_depth(SizedFlipChain::RR(p, g, pv, gv, other, uncle, up))); arithmetic();
                                                    }
                                                    unfold(sized_flip_node(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)))));
                                                    unfold(sized_flip_color(SizedTree::Node(g, sized_flip_parent(up), Color::Red, gv, SizedTree::Node(u, g, Color::Black, uv, ul, ur), SizedTree::Node(p, g, Color::Black, pv, other, at(iteration,state.model)))));
                                                    step();
                                                    close_invariants() by simp();
                                                },
                                            }
                                        },
                                    }
                                },
                                SizedFlipChain::Root => {
                                    have path.model == SizedContext::Top by {
                                        rewrite(path.model == at(iteration,state.context));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::Root);
                                        unfold(sized_flip_context(SizedFlipChain::Root)); normalize();
                                    }
                                    have parent == 0 by {
                                        rewrite(parent == above);
                                        rewrite(above == sized_context_parent(at(iteration,state.context), 0));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::Root);
                                        unfold(sized_flip_context(SizedFlipChain::Root));
                                        unfold(sized_context_parent(SizedContext::Top, 0)); normalize();
                                    }
                                    let { metadata: metadata, left: l, right: r } = unfold(focus);
                                    step(); step();
                                    unfold(color_bit(Color::Black));
                                    let focus = fold(sized_at(node), { model: SizedTree::Node(current, 0, Color::Black, count, lo, hi) }, { metadata: metadata, left: l, right: r });
                                    have sized_value(focus.model) == count by {
                                        rewrite(focus.model == SizedTree::Node(current, 0, Color::Black, count, lo, hi));
                                        unfold(sized_value(SizedTree::Node(current, 0, Color::Black, count, lo, hi))); normalize();
                                    }
                                    have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                        rewrite(focus.model == SizedTree::Node(current, 0, Color::Black, count, lo, hi));
                                        rewrite(path.model == SizedContext::Top);
                                        unfold(sized_context_parent(SizedContext::Top, 0));
                                        unfold(sized_parent_is(SizedTree::Node(current, 0, Color::Black, count, lo, hi), 0)); normalize();
                                    }
                                    have sized_plug(path.model, focus.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by {
                                        rewrite(path.model == SizedContext::Top);
                                        rewrite(focus.model == SizedTree::Node(current, 0, Color::Black, count, lo, hi));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::Root);
                                        rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                        unfold(sized_flip_result(SizedFlipChain::Root, SizedTree::Node(current, above, red, count, lo, hi)));
                                        unfold(sized_recolor(SizedTree::Node(current, above, red, count, lo, hi), Color::Black));
                                        unfold(sized_plug(SizedContext::Top, SizedTree::Node(current, 0, Color::Black, count, lo, hi)));
                                        have above == 0 by assumption();
                                        rewrite(above == 0); normalize();
                                    }
                                    let state = fold(sized_flip_state(root), { chain: at(iteration,state.chain), model: focus.model, context: SizedContext::Top }, { focus: focus, path: path });
                                    have sized_plug(state.context, state.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by assumption();
                                    have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by assumption();
                                    step();
                                },
                                SizedFlipChain::Stop(ctx) => {
                                    have path.model == ctx by {
                                        rewrite(path.model == at(iteration,state.context));
                                        rewrite(at(iteration,state.context) == sized_flip_context(at(iteration,state.chain)));
                                        rewrite(at(iteration,state.chain) == SizedFlipChain::Stop(ctx));
                                        unfold(sized_flip_context(SizedFlipChain::Stop(ctx))); normalize();
                                    }
                                    have sized_flip_black_boundary(ctx) == 1 by {
                                        unfold(sized_flip_allowed(SizedFlipChain::Stop(ctx)));
                                        rewrite(sized_flip_black_boundary(ctx) == sized_flip_allowed(SizedFlipChain::Stop(ctx)));
                                        rewrite(SizedFlipChain::Stop(ctx) == at(iteration,state.chain)); assumption();
                                    }
                                    match ctx {
                                        SizedContext::Top => {
                                            have not (sized_flip_black_boundary(ctx) == 1) by {
                                                rewrite(ctx == SizedContext::Top);
                                                unfold(sized_flip_black_boundary(SizedContext::Top)); normalize();
                                            }
                                            contradiction(sized_flip_black_boundary(ctx) == 1);
                                        },
                                        SizedContext::Left(a, gp, color, cached, sibling, up) => {
                                            have parent == a by {
                                                rewrite(parent == above);
                                                rewrite(above == sized_context_parent(at(iteration,state.context), 0));
                                                rewrite(at(iteration,state.context) == path.model);
                                                rewrite(path.model == ctx); rewrite(ctx == SizedContext::Left(a, gp, color, cached, sibling, up));
                                                unfold(sized_context_parent(SizedContext::Left(a, gp, color, cached, sibling, up), 0)); normalize();
                                            }
                                            have color_bit(color) == 1 by {
                                                unfold(sized_flip_black_boundary(SizedContext::Left(a, gp, color, cached, sibling, up)));
                                                rewrite(color_bit(color) == sized_flip_black_boundary(SizedContext::Left(a, gp, color, cached, sibling, up)));
                                                rewrite(SizedContext::Left(a, gp, color, cached, sibling, up) == ctx); assumption();
                                            }
                                            let { metadata: a_size, sibling: held_sibling, up: held_up } = unfold(path);
                                            have (a->__rb_parent_color & 1) == 1 by {
                                                rewrite((a->__rb_parent_color & 1) == color_bit(color));
                                                rewrite(color_bit(color) == 1); normalize();
                                            }
                                            step(); step(); step();
                                            let path = fold(sized_context_at(node, root->rb_node, 0, count), { model: SizedContext::Left(a, gp, color, cached, sibling, up) }, { metadata: a_size, sibling: held_sibling, up: held_up });
                                            have sized_value(focus.model) == count by {
                                                rewrite(focus.model == at(iteration,state.model));
                                                rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); normalize();
                                            }
                                            have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                                rewrite(focus.model == at(iteration,state.model));
                                                rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi), sized_context_parent(path.model, 0)));
                                                normalize() using { above == sized_context_parent(at(iteration,state.context), 0); at(iteration,state.context) == ctx; ctx == SizedContext::Left(a, gp, color, cached, sibling, up); path.model == SizedContext::Left(a, gp, color, cached, sibling, up); };
                                            }
                                            have sized_plug(path.model, focus.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by {
                                                rewrite(at(iteration,state.chain) == SizedFlipChain::Stop(ctx));
                                                unfold(sized_flip_result(SizedFlipChain::Stop(ctx), at(iteration,state.model)));
                                                rewrite(focus.model == at(iteration,state.model));
                                                rewrite(path.model == SizedContext::Left(a, gp, color, cached, sibling, up)); rewrite(SizedContext::Left(a, gp, color, cached, sibling, up) == ctx); normalize();
                                            }
                                            let state = fold(sized_flip_state(root), { chain: at(iteration,state.chain), model: focus.model, context: path.model }, { focus: focus, path: path });
                                            have sized_plug(state.context, state.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by assumption();
                                            have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by assumption();
                                            step();
                                        },
                                        SizedContext::Right(a, gp, color, cached, sibling, up) => {
                                            have parent == a by {
                                                rewrite(parent == above);
                                                rewrite(above == sized_context_parent(at(iteration,state.context), 0));
                                                rewrite(at(iteration,state.context) == path.model);
                                                rewrite(path.model == ctx); rewrite(ctx == SizedContext::Right(a, gp, color, cached, sibling, up));
                                                unfold(sized_context_parent(SizedContext::Right(a, gp, color, cached, sibling, up), 0)); normalize();
                                            }
                                            have color_bit(color) == 1 by {
                                                unfold(sized_flip_black_boundary(SizedContext::Right(a, gp, color, cached, sibling, up)));
                                                rewrite(color_bit(color) == sized_flip_black_boundary(SizedContext::Right(a, gp, color, cached, sibling, up)));
                                                rewrite(SizedContext::Right(a, gp, color, cached, sibling, up) == ctx); assumption();
                                            }
                                            let { metadata: a_size, sibling: held_sibling, up: held_up } = unfold(path);
                                            have (a->__rb_parent_color & 1) == 1 by {
                                                rewrite((a->__rb_parent_color & 1) == color_bit(color));
                                                rewrite(color_bit(color) == 1); normalize();
                                            }
                                            step(); step(); step();
                                            let path = fold(sized_context_at(node, root->rb_node, 0, count), { model: SizedContext::Right(a, gp, color, cached, sibling, up) }, { metadata: a_size, sibling: held_sibling, up: held_up });
                                            have sized_value(focus.model) == count by {
                                                rewrite(focus.model == at(iteration,state.model));
                                                rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_value(SizedTree::Node(current, above, red, count, lo, hi))); normalize();
                                            }
                                            have sized_parent_is(focus.model, sized_context_parent(path.model, 0)) == 1 by {
                                                rewrite(focus.model == at(iteration,state.model));
                                                rewrite(at(iteration,state.model) == SizedTree::Node(current, above, red, count, lo, hi));
                                                unfold(sized_parent_is(SizedTree::Node(current, above, red, count, lo, hi), sized_context_parent(path.model, 0)));
                                                normalize() using { above == sized_context_parent(at(iteration,state.context), 0); at(iteration,state.context) == ctx; ctx == SizedContext::Right(a, gp, color, cached, sibling, up); path.model == SizedContext::Right(a, gp, color, cached, sibling, up); };
                                            }
                                            have sized_plug(path.model, focus.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by {
                                                rewrite(at(iteration,state.chain) == SizedFlipChain::Stop(ctx));
                                                unfold(sized_flip_result(SizedFlipChain::Stop(ctx), at(iteration,state.model)));
                                                rewrite(focus.model == at(iteration,state.model));
                                                rewrite(path.model == SizedContext::Right(a, gp, color, cached, sibling, up)); rewrite(SizedContext::Right(a, gp, color, cached, sibling, up) == ctx); normalize();
                                            }
                                            let state = fold(sized_flip_state(root), { chain: at(iteration,state.chain), model: focus.model, context: path.model }, { focus: focus, path: path });
                                            have sized_plug(state.context, state.model) == sized_flip_result(at(iteration,state.chain), at(iteration,state.model)) by assumption();
                                            have sized_plug(state.context, state.model) == sized_flip_result(old(state.chain), old(state.model)) by assumption();
                                            step();
                                        },
                                    }
                                },
                            }
                        },
                    }
                }
            }
            let { whole: whole } = restore_sized_flip_state(root, { state: state });
            execute(); simp();
        },
    }
}

void __rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                 void (*augment_rotate)(struct rb_node*, struct rb_node*)) {
    consumes state: sized_flip_state(root);
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    let { whole: whole } = step(__rb_insert(node, root, augment_rotate), { state: state });
    execute(); simp();
}

void rb_insert_augmented(struct rb_node* node, struct rb_root* root,
                 const struct rb_augment_callbacks* augment) {
    views augment->rotate;
    consumes state: sized_flip_state(root);
    requires sized_flip_allowed(state.chain) == 1;
    requires state.context == sized_flip_context(state.chain);
    requires node == sized_flip_node(state.model);
    requires sized_flip_color(state.model) == 0;
    produces root->rb_node;
    produces whole: sized_at(root->rb_node);
    ensures whole.model == sized_flip_result(old(state.chain), old(state.model));
    ensures sized_parent_is(whole.model, 0) == 1;
} by {
    let { whole: whole } = step(__rb_insert_augmented(node, root, augment->rotate), { state: state });
    execute(); simp();
}
