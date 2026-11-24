// Arbitrary ancestor propagation over the unchanged Linux callback body.
verifying "rbtree_size_propagate.c";
verifying "rbtree_size_compute.c";
verifying "rbtree_size_copy.c";
import "rbtree_size_walk.click";

tactic sized_walk_done_at_stop(rb: struct rb_node*, stop: struct rb_node*) {
    owns walk: sized_walk_at(rb, stop);
    ensures walk.model == old(walk.model);
    ensures address(rb) != address(stop) or sized_walk_pending(walk.model) == 0;
} by {
    match walk.model {
        SizedWalk::Active(previous, sub_model, path_model) => {
            with(walk) {
                have address(rb) != address(stop) by { close(); }
            }
            have address(rb) != address(stop) or sized_walk_pending(walk.model) == 0 by { close(); }
        },
        SizedWalk::Done(result_model) => {
            have sized_walk_pending(walk.model) == 0 by {
                rewrite(walk.model, SizedWalk::Done(result_model));
                unfold(sized_walk_pending(SizedWalk::Done(result_model)));
                normalize();
            }
            have address(rb) != address(stop) or sized_walk_pending(walk.model) == 0 by { close(); }
        },
    }
}

void sized_propagate(struct rb_node* rb, struct rb_node* stop) {
    consumes walk: sized_walk_at(rb, stop);
    requires sized_walk_pending(walk.model) == 1 or rb == stop;
    requires rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
    produces whole: sized_result_at(stop);
    ensures sized_result_root(whole.model) == sized_walk_root(old(walk.model));
    ensures sized_shape(sized_result_tree(whole.model)) == sized_shape(sized_walk_tree(old(walk.model)));
    ensures sized_counts_valid(sized_result_tree(whole.model)) == 1;
} by {
    apply(compute_size_restores_subtree_size());
    sized_walk_done_at_stop(rb, stop, { walk: walk });
    have sized_walk_pending(walk.model) == 1 or rb == stop by {
        rewrite(walk.model, old(walk.model));
        close();
    }
    have rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647 by {
        rewrite(walk.model, old(walk.model));
        close();
    }
    loop {
        owns walk: sized_walk_at(rb, stop);
        decreases sized_walk_rank(walk.model);
        invariant sized_walk_pending(walk.model) == 1 or rb == stop;
        invariant address(rb) != address(stop) or sized_walk_pending(walk.model) == 0;
        invariant sized_walk_root(walk.model) == sized_walk_root(old(walk.model));
        invariant sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model)));
        invariant rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
        initialize by close();
        maintain by {
            mark iteration;
            match walk.model {
                SizedWalk::Done(result_model) => {
                    have sized_walk_pending(walk.model) == 0 by {
                        rewrite(walk.model, SizedWalk::Done(result_model));
                        unfold(sized_walk_pending(SizedWalk::Done(result_model))); normalize();
                    }
                    have not (sized_walk_pending(walk.model) == 1) by {
                        rewrite(sized_walk_pending(walk.model), 0); normalize();
                    }
                    have rb == stop by {
                        cases {
                            sized_walk_pending(walk.model) == 1 => { contradiction(sized_walk_pending(walk.model) == 1); }
                            rb == stop => { close(); }
                        }
                    }
                    have address(rb) == address(stop) by { rewrite(rb, stop); close(); }
                    contradiction(address(rb) == address(stop));
                },
                SizedWalk::Active(previous, sub_model, path_model) => {
                    have sized_walk_tree(walk.model) == sized_plug(sized_path_context(path_model), sub_model) by {
                        rewrite(walk.model, SizedWalk::Active(previous, sub_model, path_model));
                        unfold(sized_walk_tree(SizedWalk::Active(previous, sub_model, path_model))); normalize();
                    }
                    have sized_walk_root(walk.model) == sized_path_root(path_model) by {
                        rewrite(walk.model, SizedWalk::Active(previous, sub_model, path_model));
                        unfold(sized_walk_root(SizedWalk::Active(previous, sub_model, path_model))); normalize();
                    }
                    apply(sized_context_depth_nonnegative(sized_path_context(path_model)));
                    apply(sized_plug_contains_focus(sized_path_context(path_model), sub_model));
                    have rb_subtree_size(sized_shape(sized_plug(sized_path_context(path_model), sub_model))) <= 2147483647 by {
                        rewrite(sized_plug(sized_path_context(path_model), sub_model), sized_walk_tree(walk.model)); close();
                    }
                    have rb_subtree_size(sized_shape(sub_model)) <= 2147483647 by {
                        close() using {
                            rb_subtree_size(sized_shape(sub_model)) <= rb_subtree_size(sized_shape(sized_plug(sized_path_context(path_model), sub_model)));
                            rb_subtree_size(sized_shape(sized_plug(sized_path_context(path_model), sub_model))) <= 2147483647;
                        };
                    }
                    let { focus: dirty, path: path } = unfold(walk);
                    let { prepared: dirty } = prepare_sized_focus(rb, { tree: dirty });
                    step_until(loop(0).statement(1).entry);
                    mark before_recompute;
                    let { result: status, checked: repaired } = step(RecomputeTree, { tree: dirty });
                    apply(sized_parent_is_shape(sub_model, sized_context_parent(sized_path_context(path_model), stop)));
                    apply(sized_parent_is_shape(repaired.model, sized_context_parent(sized_path_context(path_model), stop)));
                    apply(sized_plug_same_shape(sized_path_context(path_model), sub_model, repaired.model));
                    if status != 0 {
                        have sized_value(repaired.model) == previous by {
                            cases {
                                status == 0 => { contradiction(status == 0); }
                                sized_value(repaired.model) == sized_value(at(before_recompute, dirty.model)) => {
                                    rewrite(sized_value(repaired.model), sized_value(at(before_recompute, dirty.model)));
                                    rewrite(at(before_recompute, dirty.model), sub_model); close();
                                }
                            }
                        }
                        let { done: walk } = stop_sized_path(rb, stop, previous, { sub: repaired, path: path });
                        have sized_walk_pending(walk.model) == 0 by { close(); }
                        have sized_walk_root(walk.model) == sized_walk_root(old(walk.model)) by { close(); }
                        have sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model))) by { close(); }
                        step(); step();
                    } else {
                        step();
                        match repaired.model {
                            SizedTree::Empty => { unfold(repaired); contradiction(&node->rb == 0); },
                            SizedTree::Node(identity, parent, color, value, left_model, right_model) => {
                                have sized_parent_is(SizedTree::Node(identity, parent, color, value, left_model, right_model), sized_context_parent(sized_path_context(path_model), stop)) == 1 by {
                                    rewrite(SizedTree::Node(identity, parent, color, value, left_model, right_model), repaired.model); close();
                                }
                                have parent == sized_context_parent(sized_path_context(path_model), stop);
                                let { metadata: metadata, left: left, right: right } = unfold(repaired);
                                have ((load<uint64>(&node->rb) & ~3) as (struct rb_node *)) == parent by { close(); }
                                step(); step(); step();
                                have rb == parent by { close(); }
                                let sub = fold(sized_at(identity), { model: SizedTree::Node(identity, parent, color, value, left_model, right_model), metadata: metadata, left: left, right: right });
                                have rb == sized_context_parent(sized_path_context(path.model), stop) by {
                                    rewrite(rb, parent);
                                    rewrite(path.model, path_model); close();
                                }
                                let { next: walk } = advance_sized_path(identity, rb, stop, previous, { sub: sub, path: path });
                                have address(rb) != address(stop) or sized_walk_pending(walk.model) == 0 by { close(); }
                                have sized_walk_pending(walk.model) == 1 or rb == stop by { close(); }
                                have sized_walk_root(walk.model) == sized_walk_root(old(walk.model)) by { close(); }
                                have sized_walk_tree(walk.model) == sized_plug(sized_path_context(path_model), SizedTree::Node(identity, parent, color, value, left_model, right_model)) by { close(); }
                                have sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model))) by { close(); }
                                have rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647 by {
                                    rewrite(sized_shape(sized_walk_tree(walk.model)), sized_shape(sized_walk_tree(old(walk.model))));
                                    rewrite(sized_shape(sized_walk_tree(old(walk.model))), sized_shape(sized_walk_tree(at(iteration, walk.model)))); close();
                                }
                                have sized_walk_root(walk.model) == sized_walk_root(at(loop(0).entry, walk.model))
                                    implies sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(at(loop(0).entry, walk.model)))
                                    implies rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647 by {
                                    intro();
                                    intro();
                                    close();
                                }
                                have 0 <= sized_walk_rank(walk.model) by { close(); }
                                have sized_walk_rank(walk.model) < sized_context_depth(sized_path_context(path_model)) + 1 by { close(); }
                                have sized_walk_rank(at(iteration, walk.model)) == sized_context_depth(sized_path_context(path_model)) + 1 by {
                                    rewrite(at(iteration, walk.model), SizedWalk::Active(previous, sub_model, path_model));
                                    unfold(sized_walk_rank(SizedWalk::Active(previous, sub_model, path_model))); normalize();
                                }
                                have sized_walk_rank(walk.model) < sized_walk_rank(at(iteration, walk.model)) by {
                                    rewrite(sized_walk_rank(at(iteration, walk.model)), sized_context_depth(sized_path_context(path_model)) + 1); close();
                                }
                            },
                        }
                    }
                },
            }
        }
        otherwise {
            have old(walk.model) == at(loop(0).entry, walk.model) by { close(); }
            have sized_walk_root(walk.model) == sized_walk_root(old(walk.model)) by {
                rewrite(old(walk.model), at(loop(0).entry, walk.model));
                close();
            }
            have sized_shape(sized_walk_tree(walk.model)) == sized_shape(sized_walk_tree(old(walk.model))) by {
                rewrite(old(walk.model), at(loop(0).entry, walk.model));
                close();
            }
            have sized_walk_pending(walk.model) == 0 by {
                cases {
                    address(rb) != address(stop) => { contradiction(address(rb) != address(stop)); }
                    sized_walk_pending(walk.model) == 0 => { close(); }
                }
            }
        }
    }
    mark completed_walk;
    let { whole: whole } = finish_sized_walk(rb, stop, { walk: walk });
    have sized_result_root(whole.model) == sized_walk_root(old(walk.model)) by {
        rewrite(sized_result_root(whole.model), sized_walk_root(at(completed_walk, walk.model)));
        close();
    }
    have sized_shape(sized_result_tree(whole.model)) == sized_shape(sized_walk_tree(old(walk.model))) by {
        rewrite(sized_result_tree(whole.model), sized_walk_tree(at(completed_walk, walk.model)));
        close();
    }
    step_until(function.exit);
}

contract void PropagateTree(struct rb_node* rb, struct rb_node* stop) {
    consumes walk: sized_walk_at(rb, stop);
    produces whole: sized_result_at(stop);
    requires sized_walk_pending(walk.model) == 1 or rb == stop;
    requires rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647;
    ensures sized_result_root(whole.model) == sized_walk_root(old(walk.model));
    ensures sized_shape(sized_result_tree(whole.model)) == sized_shape(sized_walk_tree(old(walk.model)));
    ensures sized_counts_valid(sized_result_tree(whole.model)) == 1;
}

theorem sized_propagate_has_tree_contract()
    executes sized_propagate(struct rb_node* rb, struct rb_node* stop) {
    ensures PropagateTree(&sized_propagate) as { walk: walk, whole: whole } by {
        let { whole: whole } = step(sized_propagate, { walk: walk }) {
            requires sized_walk_pending(walk.model) == 1 or rb == stop by { close(); };
            requires rb_subtree_size(sized_shape(sized_walk_tree(walk.model))) <= 2147483647 by { close(); };
        };
        close();
    }
}
