verifying "rb_erase.c";
import "rbtree_erase_callbacks.click";
import "rbtree_change_child.click";
import "../rbtree-model/rbtree_spine_resources.click";
import "../rbtree-model/rbtree_context_depth.click";

# The rotation helper changes tags and the outer link, retaining both
# already-updated child links of each local node.
resource rb_child_links(p: struct rb_node*, left: struct rb_node*, right: struct rb_node*) {
    owns p->rb_left;
    owns p->rb_right;
    fact p->rb_left == left;
    fact p->rb_right == right;
}

# Preserve the opaque far-subtree link before the parent changes its child.
spec enum RbSavedLink {
    Link(struct rb_node*),
}

resource rb_saved_link(slot: struct rb_node**) {
    field model: RbSavedLink;
    match model {
        RbSavedLink::Link(child) => {
            owns *slot;
            fact *slot == child;
        },
    }
}

resource rb_written_right_link(p: struct rb_node*, child: struct rb_node*) {
    owns p->rb_right;
    fact p->rb_right == child;
}

resource rb_written_left_link(p: struct rb_node*, child: struct rb_node*) {
    owns p->rb_left;
    fact p->rb_left == child;
}

resource rb_red_parent_tag(p: struct rb_node*, up: struct rb_node*) {
    owns p->__rb_parent_color;
    fact p->__rb_parent_color == address(up);
}

# Repeated color flips followed by black-sibling cases 3/4 or case 4,
# red-sibling cases 1/2, 1/4, and 1/3/4 in either direction,
# a red-parent exit, or the root exit. Focus and rotation subtrees may be nonempty.

function erase_flips_red_all(ctx: Context) -> int32
decreases ctx
{
    match ctx {
        Context::Top => 1,
        Context::Right(id, above, pc, sibling, up) => match sibling {
            RbTree::Empty => 0,
            RbTree::Node(sid, sp, sc, far, near) => if sc == Color::Black {
                if rb_root_black(far) == 1 {
                    if rb_root_black(near) == 1 {
                        match pc {
                            Color::Red => 1,
                            Color::Black => erase_flips_red_all(up),
                        }
                    } else {
                        1
                    }
                } else {
                    1
                }
            } else {
                match near {
                    RbTree::Empty => 0,
                    RbTree::Node(nid, np, nc, nl, nr) => if nc == Color::Black { 1 } else { 0 },
                }
            },
        },
        Context::Left(id, above, pc, sibling, up) => match sibling {
            RbTree::Empty => 0,
            RbTree::Node(sid, sp, sc, near, far) => if sc == Color::Black {
                if rb_root_black(far) == 1 {
                    if rb_root_black(near) == 1 {
                        match pc {
                            Color::Red => 1,
                            Color::Black => erase_flips_red_all(up),
                        }
                    } else {
                        1
                    }
                } else {
                    1
                }
            } else {
                match near {
                    RbTree::Empty => 0,
                    RbTree::Node(nid, np, nc, nl, nr) => if nc == Color::Black { 1 } else { 0 },
                }
            },
        },
    }
}
function erase_flips_red_all_result(ctx: Context, focus: RbTree) -> RbTree
decreases ctx
{
    match ctx {
        Context::Top => focus,
        Context::Right(id, above, pc, sibling, up) => match sibling {
            RbTree::Empty => match pc {
                Color::Red => plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
            },
            RbTree::Node(sid, sp, sc, far, near) => match sc {
                Color::Black => match far {
                    RbTree::Empty => match near {
                        RbTree::Empty => match pc {
                            Color::Red => plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                            Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                        },
                        RbTree::Node(nid, np, nc, nl, nr) => match nc {
                            Color::Black => match pc {
                                Color::Red => plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                                Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                            },
                            Color::Red => plug(up, RbTree::Node(nid, above, pc, RbTree::Node(sid, nid, Color::Black, far, rb_reparent(nl, sid)), RbTree::Node(id, nid, Color::Black, rb_reparent(nr, id), focus))),
                        },
                    },
                    RbTree::Node(rid, rp, rc, rl, rr) => match rc {
                        Color::Black => match near {
                            RbTree::Empty => match pc {
                                Color::Red => plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                                Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                            },
                            RbTree::Node(nid, np, nc, nl, nr) => match nc {
                                Color::Black => match pc {
                                    Color::Red => plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                                    Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(sibling, Color::Red), focus)),
                                },
                                Color::Red => plug(up, RbTree::Node(nid, above, pc, RbTree::Node(sid, nid, Color::Black, far, rb_reparent(nl, sid)), RbTree::Node(id, nid, Color::Black, rb_reparent(nr, id), focus))),
                            },
                        },
                        Color::Red => plug(up, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rl, rr), RbTree::Node(id, sid, Color::Black, rb_reparent(near, id), focus))),
                    },
                },
                Color::Red => match near {
                    RbTree::Empty => plug(up, RbTree::Node(sid, above, Color::Black, far, RbTree::Node(id, sid, Color::Black, rb_recolor(rb_reparent(near, id), Color::Red), focus))),
                    RbTree::Node(nid, np, nc, nl, nr) => match rb_color(nl) {
                        Color::Black => match rb_color(nr) { Color::Black => plug(up, RbTree::Node(sid, above, Color::Black, far, RbTree::Node(id, sid, Color::Black, rb_recolor(rb_reparent(near, id), Color::Red), focus))), Color::Red => match nr { RbTree::Empty => plug(up, RbTree::Node(sid, above, Color::Black, far, RbTree::Node(id, sid, Color::Black, rb_recolor(rb_reparent(near, id), Color::Red), focus))), RbTree::Node(iid, ip, ic, il, ir) => plug(Context::Right(sid, above, Color::Black, far, up), RbTree::Node(iid, sid, Color::Red, RbTree::Node(nid, iid, Color::Black, nl, rb_reparent(il, nid)), RbTree::Node(id, iid, Color::Black, rb_reparent(ir, id), focus))), }, },
                        Color::Red => match nl { RbTree::Empty => plug(up, RbTree::Node(sid, above, Color::Black, far, RbTree::Node(id, sid, Color::Black, rb_recolor(rb_reparent(near, id), Color::Red), focus))), RbTree::Node(rid, rp, rc, rl, rr) => plug(Context::Right(sid, above, Color::Black, far, up), RbTree::Node(nid, sid, Color::Red, RbTree::Node(rid, nid, Color::Black, rl, rr), RbTree::Node(id, nid, Color::Black, rb_reparent(nr, id), focus))), }, },
                },
            },
        },
        Context::Left(id, above, pc, sibling, up) => match sibling {
            RbTree::Empty => match pc {
                Color::Red => plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
            },
            RbTree::Node(sid, sp, sc, near, far) => match sc {
                Color::Black => match far {
                    RbTree::Empty => match near {
                        RbTree::Empty => match pc {
                            Color::Red => plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                            Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                        },
                        RbTree::Node(nid, np, nc, nr, nl) => match nc {
                            Color::Black => match pc {
                                Color::Red => plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                                Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                            },
                            Color::Red => plug(up, RbTree::Node(nid, above, pc, RbTree::Node(id, nid, Color::Black, focus, rb_reparent(nr, id)), RbTree::Node(sid, nid, Color::Black, rb_reparent(nl, sid), far))),
                        },
                    },
                    RbTree::Node(rid, rp, rc, rr, rl) => match rc {
                        Color::Black => match near {
                            RbTree::Empty => match pc {
                                Color::Red => plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                                Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                            },
                            RbTree::Node(nid, np, nc, nr, nl) => match nc {
                                Color::Black => match pc {
                                    Color::Red => plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                                    Color::Black => erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(sibling, Color::Red))),
                                },
                                Color::Red => plug(up, RbTree::Node(nid, above, pc, RbTree::Node(id, nid, Color::Black, focus, rb_reparent(nr, id)), RbTree::Node(sid, nid, Color::Black, rb_reparent(nl, sid), far))),
                            },
                        },
                        Color::Red => plug(up, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, focus, rb_reparent(near, id)), RbTree::Node(rid, sid, Color::Black, rr, rl))),
                    },
                },
                Color::Red => match near {
                    RbTree::Empty => plug(up, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, focus, rb_recolor(rb_reparent(near, id), Color::Red)), far)),
                    RbTree::Node(nid, np, nc, nr, nl) => match rb_color(nl) {
                        Color::Black => match rb_color(nr) { Color::Black => plug(up, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, focus, rb_recolor(rb_reparent(near, id), Color::Red)), far)), Color::Red => match nr { RbTree::Empty => plug(up, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, focus, rb_recolor(rb_reparent(near, id), Color::Red)), far)), RbTree::Node(iid, ip, ic, ir, il) => plug(Context::Left(sid, above, Color::Black, far, up), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, focus, rb_reparent(ir, id)), RbTree::Node(nid, iid, Color::Black, rb_reparent(il, nid), nl))), }, },
                        Color::Red => match nl { RbTree::Empty => plug(up, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, focus, rb_recolor(rb_reparent(near, id), Color::Red)), far)), RbTree::Node(rid, rp, rc, rr, rl) => plug(Context::Left(sid, above, Color::Black, far, up), RbTree::Node(nid, sid, Color::Red, RbTree::Node(id, nid, Color::Black, focus, rb_reparent(nr, id)), RbTree::Node(rid, nid, Color::Black, rr, rl))), }, },
                },
            },
        },
    }
}

theorem outer_nonblack_node_color(node: struct rb_node*, parent: struct rb_node*, color: Color, left: RbTree, right: RbTree) {
    requires not(rb_root_black(RbTree::Node(node, parent, color, left, right)) == 1);
    ensures color == Color::Red by {
        induct(color) as ih {
            Color::Red => { normalize(); }
            Color::Black => {
                have rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)) == 1 by { unfold(rb_root_black(RbTree::Node(node, parent, Color::Black, left, right))); normalize(); }
                contradiction(rb_root_black(RbTree::Node(node, parent, Color::Black, left, right)) == 1);
            }
        }
    }
}

theorem outer_black_node_color(node: struct rb_node*, parent: struct rb_node*, color: Color, left: RbTree, right: RbTree) {
    requires rb_root_black(RbTree::Node(node, parent, color, left, right)) == 1;
    ensures color == Color::Black by {
        induct(color) as ih {
            Color::Black => { normalize(); }
            Color::Red => {
                have rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) == 0 by { unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right))); normalize(); }
                have not(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) == 1) by { rewrite(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) == 0); normalize(); }
                contradiction(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) == 1);
            }
        }
    }
}

theorem erase_flips_red_all_right_red_step_empty(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Empty, near), up), focus) == plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, RbTree::Empty, near), Color::Red), focus)) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Node(nid, np, Color::Black, nl, nr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_right_red_step_black(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, rid: struct rb_node*, rp: struct rb_node*, rl: RbTree, rr: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), near), up), focus) == plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), near), Color::Red), focus)) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), RbTree::Node(nid, np, Color::Black, nl, nr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_right_red_step(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, far: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(far) == 1;
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, far, near), up), focus) == plug(up, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, far, near), Color::Red), focus)) by {
        induct(far) as ih {
            RbTree::Empty => { apply(erase_flips_red_all_right_red_step_empty(id, above, sid, near, up, focus)); assumption(); }
            RbTree::Node(rid, rp, rc, rl, rr) => {
                apply(outer_black_node_color(rid, rp, rc, rl, rr));
                rewrite(rc == Color::Black);
                apply(erase_flips_red_all_right_red_step_black(id, above, sid, near, rid, rp, rl, rr, up, focus)); assumption();
            }
        }
    }
}

theorem erase_flips_red_all_right_black_step_empty(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, near), up), focus) == erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, RbTree::Empty, near), Color::Red), focus)) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Node(nid, np, Color::Black, nl, nr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_right_black_step_black(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, rid: struct rb_node*, rp: struct rb_node*, rl: RbTree, rr: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), near), up), focus) == erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), near), Color::Red), focus)) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, rp, Color::Black, rl, rr), RbTree::Node(nid, np, Color::Black, nl, nr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_right_black_step(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, far: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(far) == 1;
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, far, near), up), focus) == erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, far, near), Color::Red), focus)) by {
        induct(far) as ih {
            RbTree::Empty => { apply(erase_flips_red_all_right_black_step_empty(id, above, sid, near, up, focus)); assumption(); }
            RbTree::Node(rid, rp, rc, rl, rr) => {
                apply(outer_black_node_color(rid, rp, rc, rl, rr));
                rewrite(rc == Color::Black);
                apply(erase_flips_red_all_right_black_step_black(id, above, sid, near, rid, rp, rl, rr, up, focus)); assumption();
            }
        }
    }
}

theorem erase_flips_red_all_left_red_step_empty(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, near, RbTree::Empty), up), focus) == plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(RbTree::Node(sid, id, Color::Black, near, RbTree::Empty), Color::Red))) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Node(nid, np, Color::Black, nl, nr), RbTree::Empty), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_left_red_step_black(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, rid: struct rb_node*, rp: struct rb_node*, rl: RbTree, rr: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, near, RbTree::Node(rid, rp, Color::Black, rl, rr)), up), focus) == plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(RbTree::Node(sid, id, Color::Black, near, RbTree::Node(rid, rp, Color::Black, rl, rr)), Color::Red))) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Node(rid, rp, Color::Black, rl, rr)), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, RbTree::Node(nid, np, Color::Black, nl, nr), RbTree::Node(rid, rp, Color::Black, rl, rr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_left_red_step(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, far: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(far) == 1;
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, near, far), up), focus) == plug(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(RbTree::Node(sid, id, Color::Black, near, far), Color::Red))) by {
        induct(far) as ih {
            RbTree::Empty => { apply(erase_flips_red_all_left_red_step_empty(id, above, sid, near, up, focus)); assumption(); }
            RbTree::Node(rid, rp, rc, rl, rr) => {
                apply(outer_black_node_color(rid, rp, rc, rl, rr));
                rewrite(rc == Color::Black);
                apply(erase_flips_red_all_left_red_step_black(id, above, sid, near, rid, rp, rl, rr, up, focus)); assumption();
            }
        }
    }
}

theorem erase_flips_red_all_left_black_step_empty(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, near, RbTree::Empty), up), focus) == erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(RbTree::Node(sid, id, Color::Black, near, RbTree::Empty), Color::Red))) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Node(nid, np, Color::Black, nl, nr), RbTree::Empty), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_left_black_step_black(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, rid: struct rb_node*, rp: struct rb_node*, rl: RbTree, rr: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, near, RbTree::Node(rid, rp, Color::Black, rl, rr)), up), focus) == erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(RbTree::Node(sid, id, Color::Black, near, RbTree::Node(rid, rp, Color::Black, rl, rr)), Color::Red))) by {
        induct(near) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Node(rid, rp, Color::Black, rl, rr)), up), focus)); normalize(); }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                rewrite(nc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, RbTree::Node(nid, np, Color::Black, nl, nr), RbTree::Node(rid, rp, Color::Black, rl, rr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_left_black_step(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, near: RbTree, far: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(far) == 1;
    requires rb_root_black(near) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, near, far), up), focus) == erase_flips_red_all_result(up, RbTree::Node(id, above, Color::Black, focus, rb_recolor(RbTree::Node(sid, id, Color::Black, near, far), Color::Red))) by {
        induct(far) as ih {
            RbTree::Empty => { apply(erase_flips_red_all_left_black_step_empty(id, above, sid, near, up, focus)); assumption(); }
            RbTree::Node(rid, rp, rc, rl, rr) => {
                apply(outer_black_node_color(rid, rp, rc, rl, rr));
                rewrite(rc == Color::Black);
                apply(erase_flips_red_all_left_black_step_black(id, above, sid, near, rid, rp, rl, rr, up, focus)); assumption();
            }
        }
    }
}

theorem erase_flips_red_all_left_inner_result(id: struct rb_node*, above: struct rb_node*, pc: Color, sid: struct rb_node*, rid: struct rb_node*, rl: RbTree, rr: RbTree, far: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(far) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rl, rr), far), up), focus) == plug(up, RbTree::Node(rid, above, pc, RbTree::Node(id, rid, Color::Black, focus, rb_reparent(rl, id)), RbTree::Node(sid, rid, Color::Black, rb_reparent(rr, sid), far))) by {
        induct(far) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rl, rr), RbTree::Empty), up), focus)); normalize(); }
            RbTree::Node(fid, fp, fc, fl, fr) => {
                apply(outer_black_node_color(fid, fp, fc, fl, fr));
                rewrite(fc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rl, rr), RbTree::Node(fid, fp, Color::Black, fl, fr)), up), focus)); normalize();
            }
        }
    }
}

theorem erase_flips_red_all_right_inner_result(id: struct rb_node*, above: struct rb_node*, pc: Color, sid: struct rb_node*, rid: struct rb_node*, rl: RbTree, rr: RbTree, far: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(far) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, far, RbTree::Node(rid, sid, Color::Red, rl, rr)), up), focus) == plug(up, RbTree::Node(rid, above, pc, RbTree::Node(sid, rid, Color::Black, far, rb_reparent(rl, sid)), RbTree::Node(id, rid, Color::Black, rb_reparent(rr, id), focus))) by {
        induct(far) as ih {
            RbTree::Empty => { unfold(erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Empty, RbTree::Node(rid, sid, Color::Red, rl, rr)), up), focus)); normalize(); }
            RbTree::Node(fid, fp, fc, fl, fr) => {
                apply(outer_black_node_color(fid, fp, fc, fl, fr));
                rewrite(fc == Color::Black);
                unfold(erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(fid, fp, Color::Black, fl, fr), RbTree::Node(rid, sid, Color::Red, rl, rr)), up), focus)); normalize();
            }
        }
    }
}

theorem black_root_has_black_color(tree: RbTree) {
    requires rb_root_black(tree) == 1;
    ensures rb_color(tree) == Color::Black by {
        induct(tree) as ih {
            RbTree::Empty => { unfold(rb_color(RbTree::Empty)); normalize(); }
            RbTree::Node(id, p, c, l, r) => {
                apply(outer_black_node_color(id, p, c, l, r));
                unfold(rb_color(RbTree::Node(id, p, c, l, r))); normalize();
            }
        }
    }
}
theorem erase_flips_red_all_right_red_result(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, nid: struct rb_node*, far: RbTree, nl: RbTree, nr: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(nl) == 1;
    requires rb_root_black(nr) == 1;
    ensures erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, far, RbTree::Node(nid, sid, Color::Black, nl, nr)), up), focus) == plug(up, RbTree::Node(sid, above, Color::Black, far, RbTree::Node(id, sid, Color::Black, RbTree::Node(nid, id, Color::Red, nl, nr), focus))) by {
        apply(black_root_has_black_color(nl));
        apply(black_root_has_black_color(nr));
        unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, far, RbTree::Node(nid, sid, Color::Black, nl, nr)), up), focus));
        unfold(rb_reparent(RbTree::Node(nid, sid, Color::Black, nl, nr), id));
        unfold(rb_recolor(RbTree::Node(nid, id, Color::Black, nl, nr), Color::Red));
        rewrite(rb_color(nl) == Color::Black); rewrite(rb_color(nr) == Color::Black); normalize();
    }
}

theorem erase_flips_red_all_left_red_result(id: struct rb_node*, above: struct rb_node*, sid: struct rb_node*, nid: struct rb_node*, far: RbTree, nl: RbTree, nr: RbTree, up: Context, focus: RbTree) {
    requires rb_root_black(nr) == 1;
    requires rb_root_black(nl) == 1;
    ensures erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(nid, sid, Color::Black, nl, nr), far), up), focus) == plug(up, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, focus, RbTree::Node(nid, id, Color::Red, nl, nr)), far)) by {
        apply(black_root_has_black_color(nr));
        apply(black_root_has_black_color(nl));
        unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(nid, sid, Color::Black, nl, nr), far), up), focus));
        unfold(rb_reparent(RbTree::Node(nid, sid, Color::Black, nl, nr), id));
        unfold(rb_recolor(RbTree::Node(nid, id, Color::Black, nl, nr), Color::Red));
        rewrite(rb_color(nr) == Color::Black); rewrite(rb_color(nl) == Color::Black); normalize();
    }
}

theorem ctx_node_is_left_identity(cid: struct rb_node*, grandparent: struct rb_node*,
ccolor: Color, sibling_model: RbTree, up_model: Context,
p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
    p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_node_is_right_identity(cid: struct rb_node*, grandparent: struct rb_node*,
ccolor: Color, sibling_model: RbTree, up_model: Context,
p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
    p) == 1;

    ensures p == cid by {
        if p == cid {
            assumption();
        } else {
            have ctx_node_is(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_top_fixed(p: struct rb_node*) {
    ensures Context::Top == ctx_reroot(Context::Top, p) by {
        unfold(ctx_reroot(Context::Top, p));
        normalize();
    }
}

theorem ctx_reroot_left_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
ccolor: Color, sibling_model: RbTree, up_model: Context,
p: struct rb_node*) {
    requires ctx_node_is(Context::Left(cid, grandparent, ccolor, sibling_model, up_model),
    p) == 1;

    ensures Context::Left(cid, grandparent, ccolor, sibling_model, up_model)
    == ctx_reroot(Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_right_fixed(cid: struct rb_node*, grandparent: struct rb_node*,
ccolor: Color, sibling_model: RbTree, up_model: Context,
p: struct rb_node*) {
    requires ctx_node_is(Context::Right(cid, grandparent, ccolor, sibling_model, up_model),
    p) == 1;

    ensures Context::Right(cid, grandparent, ccolor, sibling_model, up_model)
    == ctx_reroot(Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) by {
        if p == cid {
            unfold(ctx_reroot(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
            rewrite(p == cid);
            normalize();
        } else {
            have ctx_node_is(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) != 1 by {
                unfold(ctx_node_is(
                Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p));
                normalize() using { not(p == cid); }
            }
            contradiction(ctx_node_is(
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model), p) == 1);
        }
    }
}

theorem ctx_reroot_fixed(ctx: Context, p: struct rb_node*) {
    requires ctx_node_is(ctx, p) == 1;

    ensures ctx == ctx_reroot(ctx, p) by {
        induct(ctx) as ih {
            Context::Top => {
                apply(ctx_reroot_top_fixed(p));
                assumption();
            }
            Context::Left(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_left_fixed(cid, grandparent, ccolor, sibling_model,
                up_model, p));
                assumption();
            }
            Context::Right(cid, grandparent, ccolor, sibling_model, up_model) => {
                apply(ctx_reroot_right_fixed(cid, grandparent, ccolor, sibling_model,
                up_model, p));
                assumption();
            }
        }
    }
}

theorem rb_root_black_node_color_bit(node: struct rb_node*, parent: struct rb_node*,
color: Color, left: RbTree, right: RbTree) {
    requires rb_root_black(RbTree::Node(node, parent, color, left, right)) == 1;

    ensures color_bit(color) == 1 by {
        induct(color) as ih {
            Color::Red => {
                have rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)) != 1 by {
                    unfold(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right)));
                    normalize();
                }
                contradiction(rb_root_black(RbTree::Node(node, parent, Color::Red, left, right))
                == 1);
            }
            Color::Black => {
                unfold(color_bit(Color::Black));
                normalize();
            }
        }
    }
}

theorem ctx_node_is_top_null(p: struct rb_node*) {
    requires ctx_node_is(Context::Top, p) == 1;

    ensures p == 0 by {
        if p == 0 {
            assumption();
        } else {
            have ctx_node_is(Context::Top, p) != 1 by {
                unfold(ctx_node_is(Context::Top, p));
                normalize() using { not(p == 0); }
            }
            contradiction(ctx_node_is(Context::Top, p) == 1);
        }
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


function ctx_parent_word(ctx: Context, word: uint64) -> int32 {
    match ctx {
        Context::Top => if word == 0 { 1 } else { if word == 1 { 1 } else { 0 } },
        Context::Left(id, above, pc, sibling, up) => if word == address(id) { 1 } else { if word == address(id) + 1 { 1 } else { 0 } },
        Context::Right(id, above, pc, sibling, up) => if word == address(id) { 1 } else { if word == address(id) + 1 { 1 } else { 0 } },
    }
}

void __rb_rotate_set_parents(struct rb_node* old, struct rb_node* new,
struct rb_root* root, int32 color) {
    consumes c: ctx_at(old, root);
    owns old->__rb_parent_color;
    owns new->__rb_parent_color;
    requires old != 0;
    requires new != 0;
    requires aligned(new, 8);
    requires 0 <= color;
    requires color <= 1;
    requires ctx_parent_word(c.model, old->__rb_parent_color) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(c.model);
    ensures new->__rb_parent_color == old(old->__rb_parent_color);
    ensures old->__rb_parent_color == address(new) + color;
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Top });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == Context::Top); rewrite(Context::Top == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == 0 by {
                if old->__rb_parent_color == 0 {
                    rewrite(old->__rb_parent_color == 0); normalize();
                } else {
                    have old->__rb_parent_color == 1 by {
                        if old->__rb_parent_color == 1 { assumption(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == Context::Top); unfold(ctx_parent_word(Context::Top, old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == 0); not(old->__rb_parent_color == 1); }
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    rewrite(old->__rb_parent_color == 1); normalize();
                }
            }
            step(); step();
            have parent == 0;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Top); rewrite(parent == 0); unfold(ctx_node_is(Context::Top, 0)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
        Context::Left(id, above, pc, sibling, up) => {
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Left(id, above, pc, sibling, up) }, { sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == Context::Left(id, above, pc, sibling, up)); rewrite(Context::Left(id, above, pc, sibling, up) == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    arithmetic() using { old->__rb_parent_color == address(id); aligned(id, 8); }
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { assumption(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == Context::Left(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); }
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    arithmetic() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); }
                }
            }
            step(); step();
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Left(id, above, pc, sibling, up)); rewrite(parent == id); unfold(ctx_node_is(Context::Left(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
        Context::Right(id, above, pc, sibling, up) => {
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Right(id, above, pc, sibling, up) }, { sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model == Context::Right(id, above, pc, sibling, up)); rewrite(Context::Right(id, above, pc, sibling, up) == old(c.model)); assumption(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    arithmetic() using { old->__rb_parent_color == address(id); aligned(id, 8); }
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { assumption(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model == Context::Right(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); }
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color) == 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    arithmetic() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); }
                }
            }
            step(); step();
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model == Context::Right(id, above, pc, sibling, up)); rewrite(parent == id); unfold(ctx_node_is(Context::Right(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color == (address(new) | color));
                if color == 0 { rewrite(color == 0); normalize(); } else {
                    have color == 1 by { arithmetic() using { 0 <= color; color <= 1; not(color == 0); } }
                    rewrite(color == 1);
                    arithmetic() using { aligned(new, 8); }
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by assumption();
            let { after: after } = step(__rb_change_child(old, new, parent, root), { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color == at(words, old->__rb_parent_color)); assumption();
            }
            execute(); simp();
        },
    }
}

theorem color_bit_nonzero_is_one(color: Color) {
    requires not(color_bit(color) == 0);
    ensures color_bit(color) == 1 by {
        induct(color) as ih {
            Color::Red => {
                have color_bit(Color::Red) == 0 by { unfold(color_bit(Color::Red)); normalize(); }
                contradiction(color_bit(Color::Red) == 0);
            }
            Color::Black => { unfold(color_bit(Color::Black)); normalize(); }
        }
    }
}

theorem ctx_parent_word_from_color(ctx: Context, parent: struct rb_node*, word: uint64, color: Color) {
    requires ctx_node_is(ctx, parent) == 1;
    requires word == address(parent) + color_bit(color);
    ensures ctx_parent_word(ctx, word) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                have parent == 0 by { apply(ctx_node_is_top_null(parent)); assumption(); }
                if color_bit(color) == 0 {
                    have word == 0 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == 0); rewrite(color_bit(color) == 0); normalize(); }
                    have ctx_parent_word(Context::Top, 0) == 1 by { unfold(ctx_parent_word(Context::Top, 0)); normalize(); }
                    rewrite(word == 0); assumption();
                } else {
                    apply(color_bit_nonzero_is_one(color));
                    have word == 1 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == 0); rewrite(color_bit(color) == 1); normalize(); }
                    rewrite(word == 1); unfold(ctx_parent_word(Context::Top, 1)); normalize();
                }
            }
            Context::Left(id, above, pc, sibling, up) => {
                have parent == id by { apply(ctx_node_is_left_identity(id, above, pc, sibling, up, parent)); assumption(); }
                if color_bit(color) == 0 {
                    have word == address(id) by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 0); normalize(); }
                    rewrite(word == address(id)); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), address(id))); normalize();
                } else {
                    apply(color_bit_nonzero_is_one(color));
                    have word == address(id) + 1 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 1); normalize(); }
                    rewrite(word == address(id) + 1); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), address(id) + 1)); normalize();
                }
            }
            Context::Right(id, above, pc, sibling, up) => {
                have parent == id by { apply(ctx_node_is_right_identity(id, above, pc, sibling, up, parent)); assumption(); }
                if color_bit(color) == 0 {
                    have word == address(id) by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 0); normalize(); }
                    rewrite(word == address(id)); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), address(id))); normalize();
                } else {
                    apply(color_bit_nonzero_is_one(color));
                    have word == address(id) + 1 by { rewrite(word == address(parent) + color_bit(color)); rewrite(parent == id); rewrite(color_bit(color) == 1); normalize(); }
                    rewrite(word == address(id) + 1); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), address(id) + 1)); normalize();
                }
            }
        }
    }
}

void rb_set_parent(struct rb_node* rb, struct rb_node* p) {
    owns rb->__rb_parent_color;
    ensures rb->__rb_parent_color == ((old(rb->__rb_parent_color) & 1) | address(p));
} by { execute(); simp(); }

theorem erase_color_not_black(c: Color) {
    requires not(c == Color::Black);
    ensures c == Color::Red by {
        induct(c) as ih {
            Color::Red => {
                normalize();
            }
            Color::Black => {
                have Color::Black == Color::Black by normalize();
                contradiction(Color::Black == Color::Black);
            }
        }
    }
}

theorem erase_red_near_left(id: struct rb_node*, above: struct rb_node*, pc: Color, sid: struct rb_node*, sp: struct rb_node*, near: RbTree, far: RbTree, up: Context, height: Nat) {
    requires rb_root_black(near) == 1;
    requires black_height(near) == Nat::Succ(height);
    ensures erase_flips_red_all(Context::Left(id, above, pc, RbTree::Node(sid, sp, Color::Red, near, far), up)) == 1 by {
        induct(near) as ih {
            RbTree::Empty => {
                have Nat::Zero == Nat::Succ(height) by {
                    unfold(black_height(RbTree::Empty));
                    rewrite(Nat::Zero == black_height(RbTree::Empty));
                    assumption();
                }
                have not(Nat::Zero == Nat::Succ(height)) by normalize();
                contradiction(Nat::Zero == Nat::Succ(height));
            }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                unfold(erase_flips_red_all(Context::Left(id, above, pc, RbTree::Node(sid, sp, Color::Red, RbTree::Node(nid, np, nc, nl, nr), far), up)));
                normalize() using {
                    nc == Color::Black;
                }
            }
        }
    }
}

theorem erase_frame_left(id: struct rb_node*, above: struct rb_node*, pc: Color, sibling: RbTree, up: Context, height: Nat) {
    requires is_rb(sibling) == 1;
    requires black_height(sibling) == Nat::Succ(height);
    requires erase_flips_red_all(up) == 1;
    ensures erase_flips_red_all(Context::Left(id, above, pc, sibling, up)) == 1 by {
        induct(sibling) as ih {
            RbTree::Empty => {
                have Nat::Zero == Nat::Succ(height) by {
                    unfold(black_height(RbTree::Empty));
                    rewrite(Nat::Zero == black_height(RbTree::Empty));
                    assumption();
                }
                have not(Nat::Zero == Nat::Succ(height)) by normalize();
                contradiction(Nat::Zero == Nat::Succ(height));
            }
            RbTree::Node(sid, sp, sc, l, r) => {
                if sc == Color::Black {
                    if pc == Color::Black {
                        unfold(erase_flips_red_all(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, l, r), up)));
                        if rb_root_black(l) == 1 {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    rb_root_black(l) == 1;
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    rb_root_black(l) == 1;
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                        else {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    not(rb_root_black(l) == 1);
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    not(rb_root_black(l) == 1);
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                    }
                    else {
                        apply(erase_color_not_black(pc));
                        unfold(erase_flips_red_all(Context::Left(id, above, pc, RbTree::Node(sid, sp, sc, l, r), up)));
                        if rb_root_black(l) == 1 {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    rb_root_black(l) == 1;
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    rb_root_black(l) == 1;
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                        else {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    not(rb_root_black(l) == 1);
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    not(rb_root_black(l) == 1);
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                    }
                }
                else {
                    apply(erase_color_not_black(sc));
                    have is_rb(RbTree::Node(sid, sp, Color::Red, l, r)) == 1 by {
                        rewrite(Color::Red == sc);
                        assumption();
                    }
                    apply(is_rb_red_node_children_are_black(sid, sp, l, r));
                    apply(is_rb_red_node_right_child_is_black(sid, sp, l, r));
                    apply(is_rb_node_black_heights(sid, sp, Color::Red, l, r));
                    apply(black_height_red_node(sid, sp, l, r));
                    have black_height(l) == Nat::Succ(height) by {
                        rewrite(black_height(l) == black_height(RbTree::Node(sid, sp, Color::Red, l, r)));
                        rewrite(Color::Red == sc);
                        assumption();
                    }
                    apply(erase_red_near_left(id, above, pc, sid, sp, l, r, up, height));
                    rewrite(sc == Color::Red);
                    assumption();
                }
            }
        }
    }
}

theorem erase_red_near_right(id: struct rb_node*, above: struct rb_node*, pc: Color, sid: struct rb_node*, sp: struct rb_node*, near: RbTree, far: RbTree, up: Context, height: Nat) {
    requires rb_root_black(near) == 1;
    requires black_height(near) == Nat::Succ(height);
    ensures erase_flips_red_all(Context::Right(id, above, pc, RbTree::Node(sid, sp, Color::Red, far, near), up)) == 1 by {
        induct(near) as ih {
            RbTree::Empty => {
                have Nat::Zero == Nat::Succ(height) by {
                    unfold(black_height(RbTree::Empty));
                    rewrite(Nat::Zero == black_height(RbTree::Empty));
                    assumption();
                }
                have not(Nat::Zero == Nat::Succ(height)) by normalize();
                contradiction(Nat::Zero == Nat::Succ(height));
            }
            RbTree::Node(nid, np, nc, nl, nr) => {
                apply(outer_black_node_color(nid, np, nc, nl, nr));
                unfold(erase_flips_red_all(Context::Right(id, above, pc, RbTree::Node(sid, sp, Color::Red, far, RbTree::Node(nid, np, nc, nl, nr)), up)));
                normalize() using {
                    nc == Color::Black;
                }
            }
        }
    }
}

theorem erase_frame_right(id: struct rb_node*, above: struct rb_node*, pc: Color, sibling: RbTree, up: Context, height: Nat) {
    requires is_rb(sibling) == 1;
    requires black_height(sibling) == Nat::Succ(height);
    requires erase_flips_red_all(up) == 1;
    ensures erase_flips_red_all(Context::Right(id, above, pc, sibling, up)) == 1 by {
        induct(sibling) as ih {
            RbTree::Empty => {
                have Nat::Zero == Nat::Succ(height) by {
                    unfold(black_height(RbTree::Empty));
                    rewrite(Nat::Zero == black_height(RbTree::Empty));
                    assumption();
                }
                have not(Nat::Zero == Nat::Succ(height)) by normalize();
                contradiction(Nat::Zero == Nat::Succ(height));
            }
            RbTree::Node(sid, sp, sc, l, r) => {
                if sc == Color::Black {
                    if pc == Color::Black {
                        unfold(erase_flips_red_all(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, l, r), up)));
                        if rb_root_black(l) == 1 {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    rb_root_black(l) == 1;
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    rb_root_black(l) == 1;
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                        else {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    not(rb_root_black(l) == 1);
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Black);
                                rewrite(erase_flips_red_all(up) == 1);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Black;
                                    erase_flips_red_all(up) == 1;
                                    not(rb_root_black(l) == 1);
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                    }
                    else {
                        apply(erase_color_not_black(pc));
                        unfold(erase_flips_red_all(Context::Right(id, above, pc, RbTree::Node(sid, sp, sc, l, r), up)));
                        if rb_root_black(l) == 1 {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    rb_root_black(l) == 1;
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    rb_root_black(l) == 1;
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                        else {
                            if rb_root_black(r) == 1 {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    not(rb_root_black(l) == 1);
                                    rb_root_black(r) == 1;
                                }
                            }
                            else {
                                rewrite(sc == Color::Black);
                                rewrite(pc == Color::Red);
                                normalize() using {
                                    sc == Color::Black;
                                    pc == Color::Red;
                                    not(rb_root_black(l) == 1);
                                    not(rb_root_black(r) == 1);
                                }
                            }
                        }
                    }
                }
                else {
                    apply(erase_color_not_black(sc));
                    have is_rb(RbTree::Node(sid, sp, Color::Red, l, r)) == 1 by {
                        rewrite(Color::Red == sc);
                        assumption();
                    }
                    apply(is_rb_red_node_children_are_black(sid, sp, l, r));
                    apply(is_rb_red_node_right_child_is_black(sid, sp, l, r));
                    apply(is_rb_node_black_heights(sid, sp, Color::Red, l, r));
                    apply(black_height_red_node(sid, sp, l, r));
                    have black_height(r) == Nat::Succ(height) by {
                        rewrite(black_height(r) == black_height(l));
                        rewrite(black_height(l) == black_height(RbTree::Node(sid, sp, Color::Red, l, r)));
                        rewrite(Color::Red == sc);
                        assumption();
                    }
                    apply(erase_red_near_right(id, above, pc, sid, sp, r, l, up, height));
                    rewrite(sc == Color::Red);
                    assumption();
                }
            }
        }
    }
}

theorem erase_flips_red_all_covers_deficit(ctx: Context, height: Nat, focus_color: Color) {
    requires ctx_rb(ctx, Nat::Succ(height), focus_color) == 1;
    ensures erase_flips_red_all(ctx) == 1 by {
        induct(ctx) as ih {
            Context::Top => {
                unfold(erase_flips_red_all(Context::Top));
                normalize();
            }
            Context::Left(id, above, pc, sibling, up) => {
                apply(ctx_rb_left_sibling(id, above, pc, sibling, up, Nat::Succ(height), focus_color));
                apply(ctx_rb_left_height(id, above, pc, sibling, up, Nat::Succ(height), focus_color));
                have black_height(sibling) == Nat::Succ(height) by {
                    rewrite(Nat::Succ(height) == black_height(sibling));
                    normalize();
                }
                apply(ctx_rb_left_up(id, above, pc, sibling, up, Nat::Succ(height), focus_color));
                if pc == Color::Black {
                    apply(frame_black_height_black(Nat::Succ(height)));
                    have ctx_rb(up, Nat::Succ(Nat::Succ(height)), Color::Black) == 1 by {
                        rewrite(Nat::Succ(Nat::Succ(height)) == frame_black_height(Color::Black, Nat::Succ(height)));
                        rewrite(Color::Black == pc);
                        assumption();
                    }
                    apply(ih(up, Nat::Succ(height), Color::Black));
                    apply(erase_frame_left(id, above, pc, sibling, up, height));
                    assumption();
                }
                else {
                    apply(erase_color_not_black(pc));
                    apply(frame_black_height_red(Nat::Succ(height)));
                    have ctx_rb(up, Nat::Succ(height), Color::Red) == 1 by {
                        rewrite(Nat::Succ(height) == frame_black_height(Color::Red, Nat::Succ(height)));
                        rewrite(Color::Red == pc);
                        assumption();
                    }
                    apply(ih(up, height, Color::Red));
                    apply(erase_frame_left(id, above, pc, sibling, up, height));
                    assumption();
                }
            }
            Context::Right(id, above, pc, sibling, up) => {
                apply(ctx_rb_right_sibling(id, above, pc, sibling, up, Nat::Succ(height), focus_color));
                apply(ctx_rb_right_height(id, above, pc, sibling, up, Nat::Succ(height), focus_color));
                have black_height(sibling) == Nat::Succ(height) by {
                    rewrite(Nat::Succ(height) == black_height(sibling));
                    normalize();
                }
                apply(ctx_rb_right_up(id, above, pc, sibling, up, Nat::Succ(height), focus_color));
                if pc == Color::Black {
                    apply(frame_black_height_black(Nat::Succ(height)));
                    have ctx_rb(up, Nat::Succ(Nat::Succ(height)), Color::Black) == 1 by {
                        rewrite(Nat::Succ(Nat::Succ(height)) == frame_black_height(Color::Black, Nat::Succ(height)));
                        rewrite(Color::Black == pc);
                        assumption();
                    }
                    apply(ih(up, Nat::Succ(height), Color::Black));
                    apply(erase_frame_right(id, above, pc, sibling, up, height));
                    assumption();
                }
                else {
                    apply(erase_color_not_black(pc));
                    apply(frame_black_height_red(Nat::Succ(height)));
                    have ctx_rb(up, Nat::Succ(height), Color::Red) == 1 by {
                        rewrite(Nat::Succ(height) == frame_black_height(Color::Red, Nat::Succ(height)));
                        rewrite(Color::Red == pc);
                        assumption();
                    }
                    apply(ih(up, height, Color::Red));
                    apply(erase_frame_right(id, above, pc, sibling, up, height));
                    assumption();
                }
            }
        }
    }
}


void ____rb_erase_color(struct rb_node* parent, struct rb_root* root,
void (*augment_rotate)(struct rb_node* old, struct rb_node* new)) {
    consumes c: ctx_at(0, root);
    requires AugmentRotate(augment_rotate);
    requires c.model != Context::Top;
    requires ctx_node_is(c.model, parent) == 1;
    requires ctx_rb(c.model, Nat::Succ(black_height(RbTree::Empty)), Color::Black) == 1;
    requires rb_tree_parent_consistent(plug(c.model, RbTree::Empty)) == 1;
    produces whole: rb_root_at(root);
    ensures whole.model == erase_flips_red_all_result(old(c.model), RbTree::Empty);
    ensures is_rb_root(whole.model) == 1;
    ensures rb_tree_parent_consistent(whole.model) == 1;
    ensures rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty));
} by {
    unfold(black_height(RbTree::Empty));
    have ctx_rb(c.model, Nat::Succ(Nat::Zero), Color::Black) == 1 by {
        rewrite(Nat::Zero == black_height(RbTree::Empty)); assumption();
    }
    apply(erase_flips_red_all_covers_deficit(c.model, Nat::Zero, Color::Black));
    have c.model == ctx_reroot(c.model, parent) by {
        apply(ctx_reroot_fixed(c.model, parent)) using { ctx_node_is(c.model, parent) == 1; }
        assumption();
    }
    execute_until(loop(0));
    have node == 0;
    let t = fold(rb_at(node), { model: RbTree::Empty });
    have is_rb(t.model) == 1 by { rewrite(t.model == RbTree::Empty); unfold(is_rb(RbTree::Empty)); normalize(); }
    have rb_root_black(t.model) == 1 by { rewrite(t.model == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
    have rb_parent_is(t.model, parent) == 1 by { rewrite(t.model == RbTree::Empty); unfold(rb_parent_is(RbTree::Empty, parent)); normalize(); }
    loop {
        owns c: ctx_at(node, root);
        owns t: rb_at(node);
        decreases c;
        invariant c.model != Context::Top;
        invariant ctx_node_is(c.model, parent) == 1;
        invariant c.model == ctx_reroot(c.model, parent);
        invariant erase_flips_red_all(c.model) == 1;
        invariant is_rb(t.model) == 1;
        invariant rb_root_black(t.model) == 1;
        invariant rb_parent_is(t.model, parent) == 1;
        invariant ctx_rb(c.model, Nat::Succ(black_height(t.model)), Color::Black) == 1;
        invariant rb_tree_parent_consistent(plug(c.model, t.model)) == 1;
        invariant erase_flips_red_all_result(c.model, t.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty);
        invariant rb_inorder(plug(c.model, t.model)) == rb_inorder(plug(old(c.model), RbTree::Empty));
        initialize by simp;
        preserve by {
            mark iteration;
            match c.model {
                Context::Top => { contradiction(c.model == Context::Top); },
                Context::Right(id, above, pc, sm, um) => {
                    have ctx_node_is(Context::Right(id, above, pc, sm, um), parent) == 1 by {
                        rewrite(Context::Right(id, above, pc, sm, um) == c.model); assumption();
                    }
                    have parent == id by {
                        apply(ctx_node_is_right_identity(id, above, pc, sm, um, parent)) using {
                            ctx_node_is(Context::Right(id, above, pc, sm, um), parent) == 1;
                        }
                        assumption();
                    }
                    match sm {
                        RbTree::Empty => {
                            have erase_flips_red_all(c.model) == 0 by {
                                rewrite(c.model == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty);
                                unfold(erase_flips_red_all(Context::Right(id, above, pc, RbTree::Empty, um))); normalize();
                            }
                            have not(erase_flips_red_all(c.model) == 1) by { rewrite(erase_flips_red_all(c.model) == 0); normalize(); }
                            contradiction(erase_flips_red_all(c.model) == 1);
                        },
                        RbTree::Node(sid, sp, sc, srm, slm) => {
                            match sc {
                                Color::Black => {


                                    have at(iteration, c.model) == c.model by normalize();
                                    have at(iteration, c.model) == Context::Right(id, above, pc, sm, um) by { rewrite(at(iteration, c.model) == c.model); assumption(); }
                                    let { sibling: s, up: u } = unfold(c);
                                    have aligned(id, 8) by { rewrite(id == parent); assumption(); }
                                    have rb_parent_is(RbTree::Node(sid, sp, sc, srm, slm), id) == 1 by {
                                        rewrite(RbTree::Node(sid, sp, sc, srm, slm) == sm); rewrite(id == parent); assumption();
                                    }
                                    apply(rb_parent_is_node_parent(sid, sp, sc, srm, slm, id));
                                    have s.model == RbTree::Node(sid, id, Color::Black, srm, slm) by {
                                        rewrite(s.model == sm); rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm));
                                        rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                                    }
                                    have sm == RbTree::Node(sid, id, Color::Black, srm, slm) by {
                                        rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm)); rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                                    }
                                    have at(iteration, c.model) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) by {
                                        rewrite(at(iteration, c.model) == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, id, Color::Black, srm, slm)); normalize();
                                    }
                                    let { right: sl, left: sr } = unfold(s);
                                    step(); # Read the right child, which is the focus.
                                    mark focus_split;
                                    match t.model ensuring {
                                        owns nt: rb_at(node);
                                        fact nt.model == at(focus_split, t.model);
                                    } {
                                        RbTree::Empty => {
                                            have at(focus_split, t.model) == t.model by normalize();
                                            have at(focus_split, t.model) == RbTree::Empty by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            unfold(t);
                                            step(); # The right child equals the null focus.
                                            let nt = fold(rb_at(node), { model: RbTree::Empty });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Empty); rewrite(at(focus_split, t.model) == RbTree::Empty); normalize(); }
                                        },
                                        RbTree::Node(tid, tp, tc, trm, tlm) => {
                                            have at(focus_split, t.model) == t.model by normalize();
                                            have at(focus_split, t.model) == RbTree::Node(tid, tp, tc, trm, tlm) by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            let { right: tl, left: tr } = unfold(t);
                                            step(); # The right child equals the current focus.
                                            let nt = fold(rb_at(node), { model: RbTree::Node(tid, tp, tc, trm, tlm) }, { right: tl, left: tr });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Node(tid, tp, tc, trm, tlm)); rewrite(at(focus_split, t.model) == RbTree::Node(tid, tp, tc, trm, tlm)); normalize(); }
                                        },
                                    }
                                    step(); # Read the left sibling on the mirrored C arm.
                                    have is_rb(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_root_black(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_parent_is(nt.model, parent) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have (sid->__rb_parent_color & 1) == 1 by {
                                        rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                                    }
                                    step(); step(); # Skip the red-sibling rotation.
                                    step(); # Read the sibling's left child.
                                    if rb_root_black(srm) == 1 {
                                        if rb_root_black(slm) == 1 {


                                            match sr.model ensuring {
                                                owns rs: rb_at(tmp1);
                                                fact rs.model == srm;
                                            } {
                                                RbTree::Empty => {
                                                    have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                                    unfold(sr);
                                                    step(); # The null child satisfies the black-child guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Empty); normalize(); }
                                                },
                                                RbTree::Node(cid, cp, cc, crm, clm) => {
                                                    have srm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(srm == sr.model); assumption(); }
                                                    have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == srm); assumption(); }
                                                    apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                                    let { right: cl, left: cr } = unfold(sr);
                                                    step(); # The owned black child's tag satisfies the guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                                },
                                            }
                                            step(); # Read the sibling's right child.
                                            match sl.model ensuring {
                                                owns ls: rb_at(tmp2);
                                                fact ls.model == slm;
                                            } {
                                                RbTree::Empty => {
                                                    have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                                    unfold(sl);
                                                    step(); # The null child satisfies the black-child guard.
                                                    let ls = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                    have ls.model == slm by { rewrite(slm == RbTree::Empty); normalize(); }
                                                },
                                                RbTree::Node(cid, cp, cc, crm, clm) => {
                                                    have slm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(slm == sl.model); assumption(); }
                                                    have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == slm); assumption(); }
                                                    apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                                    let { right: cl, left: cr } = unfold(sl);
                                                    step(); # The owned black child's tag satisfies the guard.
                                                    let ls = fold(rb_at(tmp2), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                                    have ls.model == slm by { rewrite(slm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                                },
                                            }
                                            have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            have rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == 1 by {
                                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            have rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by {
                                                unfold(rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)));
                                                rewrite(rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model))); assumption();
                                            }
                                            have erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            have rb_inorder(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            step(); # Recolor the sibling red, preserving its parent.
                                            have sid->__rb_parent_color == address(id) by { rewrite(id == parent); simp(); }
                                            have (sid->__rb_parent_color & 1) == 0 by { rewrite(sid->__rb_parent_color == address(id)); arithmetic() using { aligned(id, 8); } }
                                            have (sid->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                                            have sid->__rb_parent_color == address(id) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == 0); rewrite(sid->__rb_parent_color == address(id)); normalize(); }
                                            let sn = fold(rb_at(sid), { model: RbTree::Node(sid, id, Color::Red, srm, slm) }, { right: ls, left: rs });
                                            have rb_parent_is(nt.model, id) == 1 by { rewrite(id == parent); assumption(); }
                                            have rb_parent_is(sn.model, id) == 1 by { rewrite(sn.model == RbTree::Node(sid, id, Color::Red, srm, slm)); unfold(rb_parent_is(RbTree::Node(sid, id, Color::Red, srm, slm), id)); normalize(); }
                                            match pc {
                                                Color::Red => {
                                                    have ctx_rb(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                                    have rb_parent_consistent(plug(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                                    apply(ctx_erase_case2_right_red_exit(above, id, sid, nt.model, srm, slm, um)) using {
                                                        is_rb(nt.model) == 1;
                                                        rb_root_black(nt.model) == 1;
                                                        ctx_rb(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                                        rb_root_black(slm) == 1;
                                                        rb_root_black(srm) == 1;
                                                        rb_parent_consistent(plug(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1;
                                                    }
                                                    have (parent->__rb_parent_color & 1) == 0 by {
                                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Red); unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have parent->__rb_parent_color == address(above) by {
                                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 0); normalize();
                                                    }
                                                    mark red_flip;
                                                    have at(red_flip, parent->__rb_parent_color) == address(above) by assumption();
                                                    step(); step(); # Select the red parent and blacken it.
                                                    have parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1;
                                                    have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1); rewrite(at(red_flip, parent->__rb_parent_color) == address(above)); normalize(); }
                                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                    let nc = fold(ctx_at(node, root), { model: Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) }, { sibling: sn, up: u });
                                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)) by { rewrite(nc.model == Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um)); unfold(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model)); normalize(); }
                                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(nc.model, nt.model)));
                                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))); assumption();
                                                    }
                                                    have erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)) by {
                                                        apply(erase_flips_red_all_right_red_step(id, above, sid, slm, srm, um, nt.model)); rewrite(erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == plug(um, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, srm, slm), Color::Red), nt.model))); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, srm, slm), Color::Red)); normalize();
                                                    }
                                                    have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))); rewrite(plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)) == erase_flips_red_all_result(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model));
                                                        rewrite(Color::Red == pc); assumption();
                                                    }
                                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model)));
                                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model))) == rb_inorder(plug(Context::Right(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)));
                                                        rewrite(Color::Red == pc); assumption();
                                                    }
                                                    step(); # Break with a balanced whole tree.
                                                },
                                                Color::Black => {
                                                    have Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) by { rewrite(pc == Color::Black); normalize(); }
                                                    have ctx_rb(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                                    have rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                                    apply(ctx_erase_case2_right_black_step(above, id, sid, nt.model, srm, slm, um)) using {
                                                        is_rb(nt.model) == 1;
                                                        rb_root_black(nt.model) == 1;
                                                        ctx_rb(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                                        rb_root_black(slm) == 1;
                                                        rb_root_black(srm) == 1;
                                                        rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1;
                                                    }
                                                    have (parent->__rb_parent_color & 1) == 1 by {
                                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Black); unfold(color_bit(Color::Black)); normalize();
                                                    }
                                                    have parent->__rb_parent_color == address(above) + 1 by {
                                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 1); normalize();
                                                    }
                                                    have id->__rb_parent_color == address(above) + 1 by assumption();
                                                    have (id->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                                    have erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); assumption(); }
                                                    step(); # The black parent cannot absorb the deficit.
                                                    step(); step(); # Move the deficit node and decode its parent.
                                                    have node == id;
                                                    have parent == above;
                                                    have id->__rb_parent_color == address(above) + (id->__rb_parent_color & 1) by {
                                                        rewrite((id->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); assumption();
                                                    }
                                                    mark parent_fold;
                                                    have at(parent_fold, nt.model) == nt.model by normalize();
                                                    let sub = fold(rb_at(id), { model: RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), nt.model) }, { right: nt, left: sn });
                                                    have sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)) by normalize();
                                                    have is_rb(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); assumption(); }
                                                    have rb_root_black(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); assumption(); }
                                                    have rb_parent_is(sub.model, parent) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); rewrite(parent == above); unfold(rb_parent_is(RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)), above)); normalize(); }
                                                    have ctx_rb(u.model, Nat::Succ(black_height(sub.model)), Color::Black) == 1 by { rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(u.model, sub.model))); assumption(); }
                                                    have rb_inorder(plug(u.model, sub.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)));
                                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)))) == rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model)))); assumption();
                                                    }
                                                    have erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model)) == erase_flips_red_all_result(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))) by {
                                                        apply(erase_flips_red_all_right_black_step(id, above, sid, slm, srm, um, at(parent_fold, nt.model))); rewrite(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model)) == erase_flips_red_all_result(um, RbTree::Node(id, above, Color::Black, rb_recolor(RbTree::Node(sid, id, Color::Black, srm, slm), Color::Red), at(parent_fold, nt.model)))); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, srm, slm), Color::Red)); normalize();
                                                    }
                                                    have erase_flips_red_all_result(u.model, sub.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model)));
                                                        rewrite(erase_flips_red_all_result(um, RbTree::Node(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), at(parent_fold, nt.model))) == erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um), at(parent_fold, nt.model))); assumption();
                                                    }

                                                    have ctx_node_is(u.model, parent) == 1 by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                                    have u.model == ctx_reroot(u.model, parent) by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                                    have erase_flips_red_all(u.model) == 1 by {
                                                        rewrite(u.model == um);
                                                        have erase_flips_red_all(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um)) == erase_flips_red_all(um) by {
                                                            unfold(erase_flips_red_all(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um))); normalize() using { rb_root_black(slm) == 1; rb_root_black(srm) == 1; }
                                                        }
                                                        rewrite(erase_flips_red_all(um) == erase_flips_red_all(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um)));
                                                        rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, srm, slm), um) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um)); rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); assumption();
                                                    }
                                                    if parent == 0 {
                                                        match u.model {
                                                            Context::Top => {
                                                                have is_rb_root(sub.model) == 1 by { apply(is_rb_root_from_parts(sub.model)) using { is_rb(sub.model) == 1; rb_root_black(sub.model) == 1; } assumption(); }
                                                                have plug(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(plug(Context::Top, sub.model)); normalize(); }
                                                                have erase_flips_red_all_result(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(erase_flips_red_all_result(Context::Top, sub.model)); normalize(); }
                                                                have is_rb_root(plug(u.model, sub.model)) == 1 by { rewrite(plug(u.model, sub.model) == sub.model); assumption(); }
                                                                have plug(u.model, sub.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                                    rewrite(plug(u.model, sub.model) == sub.model); rewrite(sub.model == erase_flips_red_all_result(u.model, sub.model)); assumption();
                                                                }
                                                                step(); step(); step(); # Null parent: skip continue and break.
                                                            },
                                                            Context::Right(uid, ugp, uc, usm, uum) => {
                                                                have ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Right(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                                have parent == uid by { apply(ctx_node_is_right_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                                let { sibling: us, up: uu } = unfold(u);
                                                                contradiction(parent == 0);
                                                            },
                                                            Context::Left(uid, ugp, uc, usm, uum) => {
                                                                have ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Left(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                                have parent == uid by { apply(ctx_node_is_left_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                                let { sibling: us, up: uu } = unfold(u);
                                                                contradiction(parent == 0);
                                                            },
                                                        }
                                                    } else {
                                                        have u.model != Context::Top by {
                                                            if u.model == Context::Top {
                                                                have ctx_node_is(Context::Top, parent) == 1 by { rewrite(Context::Top == u.model); assumption(); }
                                                                apply(ctx_node_is_top_null(parent)) using { ctx_node_is(Context::Top, parent) == 1; }
                                                                contradiction(parent == 0);
                                                            } else { assumption(); }
                                                        }
                                                        step(); step(); # A live parent continues with the strict child context.
                                                        close_invariants();
                                                    }
                                                },
                                            }

                                        } else {
                                            match sr.model ensuring {
                                                owns rs: rb_at(tmp1);
                                                fact rs.model == srm;
                                            } {
                                                RbTree::Empty => {
                                                    have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                                    unfold(sr);
                                                    step(); # The null child satisfies the black-child guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Empty); normalize(); }
                                                },
                                                RbTree::Node(cid, cp, cc, crm, clm) => {
                                                    have srm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(srm == sr.model); assumption(); }
                                                    have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == srm); assumption(); }
                                                    apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                                    let { right: cl, left: cr } = unfold(sr);
                                                    step(); # The owned black child's tag satisfies the guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                                },
                                            }
                                            step(); # Read the sibling's right child.
                                            match sl.model {
                                                RbTree::Empty => {
                                                    have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                                    have rb_root_black(slm) == 1 by { rewrite(slm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                    contradiction(rb_root_black(slm) == 1);
                                                },
                                                RbTree::Node(iid, ip, ic, ilm, irm) => {
                                                    have slm == RbTree::Node(iid, ip, ic, ilm, irm) by { rewrite(slm == sl.model); assumption(); }
                                                    have not(rb_root_black(RbTree::Node(iid, ip, ic, ilm, irm)) == 1) by { rewrite(RbTree::Node(iid, ip, ic, ilm, irm) == slm); assumption(); }
                                                    apply(outer_nonblack_node_color(iid, ip, ic, ilm, irm));
                                                    have rb_parent_is(RbTree::Node(iid, ip, ic, ilm, irm), sid) == 1 by { rewrite(RbTree::Node(iid, ip, ic, ilm, irm) == slm); rewrite(sid == parent->rb_left); assumption(); }
                                                    apply(rb_parent_is_node_parent(iid, ip, ic, ilm, irm, sid));
                                                    have slm == RbTree::Node(iid, sid, Color::Red, ilm, irm) by { rewrite(slm == RbTree::Node(iid, ip, ic, ilm, irm)); rewrite(ip == sid); rewrite(ic == Color::Red); normalize(); }
                                                    have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                                        rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }
                                                    have rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == 1 by {
                                                        rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }
                                                    have rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)));
                                                        rewrite(rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model))); assumption();
                                                    }
                                                    have erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                        rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }
                                                    have rb_inorder(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                        rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }

                                                    have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, RbTree::Node(iid, sid, Color::Red, ilm, irm)), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    have rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, RbTree::Node(iid, sid, Color::Red, ilm, irm)), um), nt.model), 0) == 1 by { rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    apply(ctx_erase_case3_right_exit(above, id, pc, sid, iid, nt.model, srm, ilm, irm, um));

                                                    apply(ctx_rb_right_sibling(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, RbTree::Node(iid, sid, Color::Red, ilm, irm)), um, Nat::Succ(black_height(nt.model)), Color::Black));
                                                    apply(is_rb_node_right(sid, id, Color::Black, srm, RbTree::Node(iid, sid, Color::Red, ilm, irm)));
                                                    apply(is_rb_red_node_children_are_black(iid, sid, ilm, irm));
                                                    let { left: il, right: ir } = unfold(sl);
                                                    have tmp2 == iid;
                                                    have sibling == sid;
                                                    have (iid->__rb_parent_color & 1) == 0 by { rewrite((iid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); normalize(); }
                                                    mark inner_inputs;
                                                    step(); # The red near child selects case 3.
                                                    step(); # Leave the untaken case-2 body.
                                                    step(); # Read its left child.
                                                    step(); # Move that child under the old sibling.
                                                    step(); # Put the old sibling under the red node.
                                                    step(); # Update the parent's child link.
                                                    have aligned(sid, 8);
                                                    have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                    have parent->rb_right == node;
                                                    have parent->rb_left == iid;
                                                    have iid->rb_left == sid;
                                                    have sid->rb_right == tmp1;
                                                    have sid->rb_left == at(inner_inputs, sid->rb_left);
                                                    have iid->rb_right == at(inner_inputs, iid->rb_right);
                                                    mark first_update;
                                                    match il.model ensuring {
                                                        owns first_near: rb_at(tmp1);
                                                        fact first_near.model == rb_reparent(ilm, sid);
                                                        fact parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                        fact parent->rb_right == node;
                                                        fact parent->rb_left == iid;
                                                        fact iid->rb_left == sid;
                                                        fact sid->rb_right == tmp1;
                                                        fact sid->rb_left == at(inner_inputs, sid->rb_left);
                                                        fact iid->rb_right == at(inner_inputs, iid->rb_right);
                                                    } {
                                                        RbTree::Empty => {
                                                            have ilm == RbTree::Empty by { rewrite(ilm == il.model); assumption(); }
                                                            unfold(il);
                                                            step(); step(); # Select and leave the null grandchild branch.
                                                            let first_near = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                            have first_near.model == rb_reparent(ilm, sid) by { rewrite(ilm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, sid)); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, clm, crm) => {
                                                            have ilm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(ilm == il.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == ilm); assumption(); }
                                                            apply(outer_black_node_color(cid, cp, cc, clm, crm));
                                                            let { left: cl, right: cr } = unfold(il);
                                                            have tmp1 == cid;
                                                            step(); # Enter the nonempty grandchild update.
                                                            step(); # Store its new black parent word.
                                                            have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                            have cid->__rb_parent_color == (address(sid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == cid; sibling == sid; } }
                                                            have cid->__rb_parent_color == address(sid) + 1 by { rewrite(cid->__rb_parent_color == (address(sid) | 1)); arithmetic() using { aligned(sid, 8); } }
                                                            have (cid->__rb_parent_color & 1) == 1 by normalize();
                                                            have cid->__rb_parent_color == address(sid) + (cid->__rb_parent_color & 1) by { normalize() using { cid->__rb_parent_color == address(sid) + 1; (cid->__rb_parent_color & 1) == 1; } }
                                                            have (cid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                            let first_near = fold(rb_at(tmp1), { model: RbTree::Node(cid, sid, Color::Black, clm, crm) }, { left: cl, right: cr });
                                                            have first_near.model == rb_reparent(ilm, sid) by { rewrite(ilm == RbTree::Node(cid, cp, cc, clm, crm)); rewrite(cc == Color::Black); unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, clm, crm), sid)); normalize(); }
                                                            have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color) by { normalize() using { at(first_update, parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color)); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have parent->rb_right == node by { normalize() using { at(first_update, parent->rb_right == node); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have parent->rb_left == iid by { normalize() using { at(first_update, parent->rb_left == iid); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have iid->rb_left == sid by { normalize() using { at(first_update, iid->rb_left == sid); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have sid->rb_right == tmp1 by { normalize() using { at(first_update, sid->rb_right == tmp1); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have sid->rb_left == at(inner_inputs, sid->rb_left) by { normalize() using { at(first_update, sid->rb_left == at(inner_inputs, sid->rb_left)); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have iid->rb_right == at(inner_inputs, iid->rb_right) by { normalize() using { at(first_update, iid->rb_right == at(inner_inputs, iid->rb_right)); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                        },
                                                    }
                                                    step(); # The augmentation callback preserves tree fields.
                                                    step(); step(); # Select the new sibling and far child for case 4.
                                                    have tmp1 == sid;
                                                    have sibling == iid;
                                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color)); assumption(); }
                                                    have parent->rb_right == node by assumption();
                                                    have iid->rb_left == sid by assumption();
                                                    mark outer_inputs;
                                                    step(); # Read the near child.
                                                    step(); # Attach the near child to the parent.
                                                    step(); # Attach the parent under the sibling.
                                                    step(); # Blacken the far child.
                                                    have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                    have sid->__rb_parent_color == (address(iid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == sid; sibling == iid; } }
                                                    have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { simp() using { tmp1 == sid; sibling == iid; } }
                                                    have parent->rb_right == node by { simp() using { at(outer_inputs, parent->rb_right) == node; tmp1 == sid; sibling == iid; } }
                                                    have parent->rb_left == tmp2 by { simp() using { tmp1 == sid; sibling == iid; } }
                                                    have sibling->rb_right == parent by assumption();
                                                    have iid->rb_right == parent by { rewrite(iid == sibling); normalize() using { sibling->rb_right == parent; } }
                                                    have sibling->rb_left == tmp1;
                                                    have iid->rb_left == sid by { rewrite(iid == sibling); rewrite(sid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                    have id->rb_right == node by { simp() using { parent->rb_right == node; parent == id; } }
                                                    mark near_update;
                                                    match ir.model ensuring {
                                                        owns near: rb_at(tmp2);
                                                        fact near.model == rb_reparent(irm, parent);
                                                        fact parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                        fact parent->rb_right == node;
                                                        fact parent->rb_left == tmp2;
                                                        fact iid->rb_right == parent;
                                                        fact iid->rb_left == sid;
                                                        fact sid->__rb_parent_color == (address(iid) | 1);
                                                    } {
                                                        RbTree::Empty => {
                                                            have irm == RbTree::Empty by { rewrite(irm == ir.model); assumption(); }
                                                            unfold(ir);
                                                            have tmp2 == 0;
                                                            step(); step(); # Select and complete the empty C arm.
                                                            let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                            have near.model == rb_reparent(irm, parent) by { rewrite(irm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                            have sid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, sid->__rb_parent_color == (address(iid) | 1)); sibling == iid; tmp1 == sid; } }
                                                        },
                                                        RbTree::Node(nid, np, nc, nlm, nrm) => {
                                                            have irm == RbTree::Node(nid, np, nc, nlm, nrm) by { rewrite(irm == ir.model); assumption(); }
                                                            let { left: nl, right: nr } = unfold(ir);
                                                            have tmp2 == nid;
                                                            have tmp2 != 0;
                                                            have separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color));
                                                            have separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color)) by { transport(separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)), separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color))) using { separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)); sibling == iid; }; }
                                                            have (tmp2->__rb_parent_color & 1) == color_bit(nc);
                                                            mark near_tag;
                                                            step(); # Select the nonempty near-child parent update.
                                                            step(rb_set_parent(tmp2, parent), {});
                                                            have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                            have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                                rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                                if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                            }
                                                            have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                                rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                                if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                            }
                                                            have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                            let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nlm, nrm) }, { left: nl, right: nr });
                                                            have near.model == rb_reparent(irm, parent) by { rewrite(irm == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nlm, nrm), parent)); simp(); }
                                                            have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { normalize() using { at(near_update, parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); tmp2 == nid; sibling == iid; tmp1 == sid; } }
                                                            have id->rb_right == node;
                                                            have parent->rb_right == node;
                                                            have parent->rb_left == tmp2 by { normalize() using { at(near_update, parent->rb_left == tmp2); tmp2 == nid; sibling == iid; tmp1 == sid; } }
                                                            have sibling->rb_right == parent by { transport(at(near_update, sibling->rb_right) == parent, sibling->rb_right == parent) using { at(near_update, sibling->rb_right) == parent; separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)); tmp2 == nid; sibling == iid; parent == id; }; }
                                                            have iid->rb_right == parent by { transport(at(near_update, iid->rb_right) == parent, iid->rb_right == parent) using { at(near_update, iid->rb_right) == parent; separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color)); tmp2 == nid; }; }
                                                            have sibling->rb_left == tmp1;
                                                            have iid->rb_left == sid by { rewrite(iid == sibling); rewrite(sid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                            have sid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, sid->__rb_parent_color == (address(iid) | 1)); tmp2 == nid; sibling == iid; tmp1 == sid; } }
                                                        },
                                                    }
                                                    have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by assumption();
                                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                    have u.model == um by assumption();
                                                    apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, pc));
                                                    have parent->rb_right == node by assumption();
                                                    have parent->rb_left == tmp2 by assumption();
                                                    have iid->rb_right == parent by assumption();
                                                    have iid->rb_left == sid by assumption();
                                                    have sid->__rb_parent_color == (address(iid) | 1) by assumption();
                                                    have aligned(iid, 8);
                                                    have sid->__rb_parent_color == address(iid) + 1 by { rewrite(sid->__rb_parent_color == (address(iid) | 1)); arithmetic() using { aligned(iid, 8); } }
                                                    have (sid->__rb_parent_color & 1) == 1 by normalize();
                                                    have sid->__rb_parent_color == address(iid) + (sid->__rb_parent_color & 1) by { normalize() using { sid->__rb_parent_color == address(iid) + 1; (sid->__rb_parent_color & 1) == 1; } }
                                                    have (sid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                    apply(rb_reparent_parent_is(ilm, sid));
                                                    let far_tree = fold(rb_at(sid), { model: RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)) }, { left: rs, right: first_near });
                                                    apply(rb_parent_is_node_of(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)));
                                                    fold(rb_child_links(iid, sid, parent));
                                                    fold(rb_child_links(parent, tmp2, node));
                                                    mark outer_rotation;
                                                    let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: u });
                                                    step(); # The augmentation callback preserves the tree resources.
                                                    unfold(rb_child_links(iid, sid, parent));
                                                    unfold(rb_child_links(parent, tmp2, node));
                                                    have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color);
                                                    have iid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == iid; parent == id; } }
                                                    have iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(iid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                    have iid->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                    have (iid->__rb_parent_color & 1) == color_bit(pc) by {
                                                        rewrite(iid->__rb_parent_color == address(above) + color_bit(pc));
                                                        if color_bit(pc) == 0 { rewrite(color_bit(pc) == 0); arithmetic() using { aligned(above, 8); } } else { apply(color_bit_nonzero_is_one(pc)); rewrite(color_bit(pc) == 1); arithmetic() using { aligned(above, 8); } }
                                                    }
                                                    have iid->__rb_parent_color == address(above) + (iid->__rb_parent_color & 1) by { rewrite((iid->__rb_parent_color & 1) == color_bit(pc)); assumption(); }
                                                    have parent->__rb_parent_color == address(iid) + 1;
                                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(iid) + 1); arithmetic() using { aligned(iid, 8); } }
                                                    have parent->__rb_parent_color == address(iid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have iid->rb_right == parent by assumption();
                                                    have iid->rb_left == sid by assumption();
                                                    let rotated_up = fold(ctx_at(parent, root), { model: Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um) }, { sibling: far_tree, up: u });
                                                    have ctx_node_is(Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um), iid) == 1 by { unfold(ctx_node_is(Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um), iid)); normalize(); }
                                                    apply(ctx_reroot_fixed(Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um), iid));
                                                    have near.model == rb_reparent(irm, id) by { rewrite(id == parent); assumption(); }
                                                    apply(rb_reparent_parent_is(irm, id));
                                                    have parent->rb_right == node by assumption();
                                                    have parent->rb_left == tmp2 by assumption();
                                                    let nc = fold(ctx_at(node, root), { model: Context::Right(id, iid, Color::Black, rb_reparent(irm, id), Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um)) }, { sibling: near, up: rotated_up });
                                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))) by { rewrite(nc.model == Context::Right(id, iid, Color::Black, rb_reparent(irm, id), Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um))); unfold(plug(Context::Right(id, iid, Color::Black, rb_reparent(irm, id), Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um)), nt.model)); unfold(plug(Context::Right(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), um), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))); normalize(); }
                                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))); assumption(); }
                                                    apply(erase_flips_red_all_right_inner_result(id, above, pc, sid, iid, ilm, irm, srm, um, nt.model));
                                                    have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))); rewrite(plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))) == erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, RbTree::Node(iid, sid, Color::Red, ilm, irm)), um), nt.model)); rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))); rewrite(rb_inorder(plug(um, RbTree::Node(iid, above, pc, RbTree::Node(sid, iid, Color::Black, srm, rb_reparent(ilm, sid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))) == rb_inorder(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, RbTree::Node(iid, sid, Color::Red, ilm, irm)), um), nt.model))); rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    step(); # Break after both rotations with a balanced whole tree.
                                                },
                                            }
                                        }
                                    } else {
                                        match sr.model {
                                            RbTree::Empty => {
                                                have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                                have rb_root_black(srm) == 1 by { rewrite(srm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                contradiction(rb_root_black(srm) == 1);
                                            },
                                            RbTree::Node(rid, rp, rc, rlm, rrm) => {
                                                have srm == RbTree::Node(rid, rp, rc, rlm, rrm) by auto;
                                                have not(rb_root_black(RbTree::Node(rid, rp, rc, rlm, rrm)) == 1) by auto;
                                                apply(outer_nonblack_node_color(rid, rp, rc, rlm, rrm));
                                                have rb_parent_is(RbTree::Node(rid, rp, rc, rlm, rrm), sid) == 1 by auto;
                                                apply(rb_parent_is_node_parent(rid, rp, rc, rlm, rrm, sid));
                                                have srm == RbTree::Node(rid, sid, Color::Red, rlm, rrm) by { rewrite(srm == RbTree::Node(rid, rp, rc, rlm, rrm)); rewrite(rp == sid); rewrite(rc == Color::Red); normalize(); }
                                                have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                                    rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }
                                                have rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == 1 by {
                                                    rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }
                                                have rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)));
                                                    rewrite(rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model))); assumption();
                                                }
                                                have erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                    rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }
                                                have rb_inorder(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                    rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }

                                                have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rlm, rrm), slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by auto;
                                                have rb_parent_consistent(plug(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rlm, rrm), slm), um), nt.model), 0) == 1 by auto;
                                                apply(ctx_erase_case4_right_exit(above, id, pc, sid, rid, nt.model, slm, rlm, rrm, um));
                                                let { left: rl, right: rr } = unfold(sr);
                                                have tmp1 == rid;
                                                have sibling == sid;
                                                have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                have parent->__rb_parent_color == address(above) + color_bit(pc) by auto;
                                                have parent->rb_right == node;
                                                have sibling->rb_left == tmp1;
                                                have sid->rb_left == rid by { rewrite(sid == sibling); rewrite(rid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                mark outer_inputs;
                                                step(); # Red far child skips cases 2 and 3.
                                                step(); # Read the near child.
                                                step(); # Attach the near child to the parent.
                                                step(); # Attach the parent under the sibling.
                                                step(); # Blacken the far child.
                                                step(); # Execute the far-child parent/color store.
                                                have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                have rid->__rb_parent_color == (address(sid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == rid; sibling == sid; } }
                                                have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { simp() using { tmp1 == rid; sibling == sid; } }
                                                have parent->rb_right == node by { simp() using { at(outer_inputs, parent->rb_right) == node; tmp1 == rid; sibling == sid; } }
                                                have parent->rb_left == tmp2 by { simp() using { tmp1 == rid; sibling == sid; } }
                                                have sibling->rb_right == parent by assumption();
                                                have sid->rb_right == parent by { rewrite(sid == sibling); normalize() using { sibling->rb_right == parent; } }
                                                have sibling->rb_left == tmp1;
                                                have sid->rb_left == rid by { rewrite(sid == sibling); rewrite(rid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                have id->rb_right == node by { simp() using { parent->rb_right == node; parent == id; } }
                                                mark near_update;
                                                match sl.model ensuring {
                                                    owns near: rb_at(tmp2);
                                                    fact near.model == rb_reparent(slm, parent);
                                                    fact parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                    fact parent->rb_right == node;
                                                    fact parent->rb_left == tmp2;
                                                    fact sid->rb_right == parent;
                                                    fact sid->rb_left == rid;
                                                    fact rid->__rb_parent_color == (address(sid) | 1);
                                                } {
                                                    RbTree::Empty => {
                                                        have slm == RbTree::Empty by auto;
                                                        unfold(sl);
                                                        have tmp2 == 0;
                                                        step(); step(); # Select and complete the empty C arm.
                                                        let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                        have near.model == rb_reparent(slm, parent) by auto;
                                                        have rid->__rb_parent_color == (address(sid) | 1) by { normalize() using { at(near_update, rid->__rb_parent_color == (address(sid) | 1)); sibling == sid; tmp1 == rid; } }
                                                    },
                                                    RbTree::Node(nid, np, nc, nlm, nrm) => {
                                                        have slm == RbTree::Node(nid, np, nc, nlm, nrm) by auto;
                                                        let { left: nl, right: nr } = unfold(sl);
                                                        have tmp2 == nid;
                                                        have tmp2 != 0;
                                                        have separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color));
                                                        have separate(memory(sid->rb_right), memory(tmp2->__rb_parent_color)) by { transport(separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)), separate(memory(sid->rb_right), memory(tmp2->__rb_parent_color))) using { separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)); sibling == sid; }; }
                                                        have (tmp2->__rb_parent_color & 1) == color_bit(nc);
                                                        mark near_tag;
                                                        step(); # Select the nonempty near-child parent update.
                                                        step(rb_set_parent(tmp2, parent), {});
                                                        have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by auto;
                                                        have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                            rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                            if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                        }
                                                        have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                            rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                            if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                        }
                                                        have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by auto;
                                                        let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nlm, nrm) }, { left: nl, right: nr });
                                                        have near.model == rb_reparent(slm, parent) by { rewrite(slm == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nlm, nrm), parent)); simp(); }
                                                        have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { normalize() using { at(near_update, parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                                        have id->rb_right == node;
                                                        have parent->rb_right == node;
                                                        have parent->rb_left == tmp2 by { normalize() using { at(near_update, parent->rb_left == tmp2); tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                                        have sibling->rb_right == parent by { transport(at(near_update, sibling->rb_right) == parent, sibling->rb_right == parent) using { at(near_update, sibling->rb_right) == parent; separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)); tmp2 == nid; sibling == sid; parent == id; }; }
                                                        have sid->rb_right == parent by { transport(at(near_update, sid->rb_right) == parent, sid->rb_right == parent) using { at(near_update, sid->rb_right) == parent; separate(memory(sid->rb_right), memory(tmp2->__rb_parent_color)); tmp2 == nid; }; }
                                                        have sibling->rb_left == tmp1;
                                                        have sid->rb_left == rid by { rewrite(sid == sibling); rewrite(rid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                        have rid->__rb_parent_color == (address(sid) | 1) by { normalize() using { at(near_update, rid->__rb_parent_color == (address(sid) | 1)); tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                                    },
                                                }
                                                have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by assumption();
                                                have parent->__rb_parent_color == address(above) + color_bit(pc) by auto;
                                                have u.model == um by assumption();
                                                apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, pc));
                                                have parent->rb_right == node by assumption();
                                                have parent->rb_left == tmp2 by assumption();
                                                have sid->rb_right == parent by assumption();
                                                have sid->rb_left == rid by assumption();
                                                have rid->__rb_parent_color == (address(sid) | 1) by assumption();
                                                have aligned(sid, 8);
                                                have rid->__rb_parent_color == address(sid) + 1 by { rewrite(rid->__rb_parent_color == (address(sid) | 1)); arithmetic() using { aligned(sid, 8); } }
                                                have (rid->__rb_parent_color & 1) == 1 by normalize();
                                                have rid->__rb_parent_color == address(sid) + (rid->__rb_parent_color & 1) by { normalize() using { rid->__rb_parent_color == address(sid) + 1; (rid->__rb_parent_color & 1) == 1; } }
                                                have (rid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                let far_tree = fold(rb_at(rid), { model: RbTree::Node(rid, sid, Color::Black, rlm, rrm) }, { left: rl, right: rr });
                                                apply(rb_parent_is_node_of(rid, sid, Color::Black, rlm, rrm));
                                                fold(rb_child_links(sid, rid, parent));
                                                fold(rb_child_links(parent, tmp2, node));
                                                mark outer_rotation;
                                                let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: u });
                                                step(); # The augmentation callback preserves the tree resources.
                                                unfold(rb_child_links(sid, rid, parent));
                                                unfold(rb_child_links(parent, tmp2, node));
                                                have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color);
                                                have sid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == sid; parent == id; } }
                                                have sid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by auto;
                                                have sid->__rb_parent_color == address(above) + color_bit(pc) by auto;
                                                have (sid->__rb_parent_color & 1) == color_bit(pc) by {
                                                    rewrite(sid->__rb_parent_color == address(above) + color_bit(pc));
                                                    if color_bit(pc) == 0 { rewrite(color_bit(pc) == 0); arithmetic() using { aligned(above, 8); } } else { apply(color_bit_nonzero_is_one(pc)); rewrite(color_bit(pc) == 1); arithmetic() using { aligned(above, 8); } }
                                                }
                                                have sid->__rb_parent_color == address(above) + (sid->__rb_parent_color & 1) by auto;
                                                have parent->__rb_parent_color == address(sid) + 1;
                                                have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(sid) + 1); arithmetic() using { aligned(sid, 8); } }
                                                have parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1) by auto;
                                                have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                have sid->rb_right == parent by assumption();
                                                have sid->rb_left == rid by assumption();
                                                let rotated_up = fold(ctx_at(parent, root), { model: Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um) }, { sibling: far_tree, up: u });
                                                have ctx_node_is(Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), sid) == 1 by { unfold(ctx_node_is(Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), sid)); normalize(); }
                                                apply(ctx_reroot_fixed(Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), sid));
                                                have near.model == rb_reparent(slm, id) by auto;
                                                apply(rb_reparent_parent_is(slm, id));
                                                have parent->rb_right == node by assumption();
                                                have parent->rb_left == tmp2 by assumption();
                                                let nc = fold(ctx_at(node, root), { model: Context::Right(id, sid, Color::Black, rb_reparent(slm, id), Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um)) }, { sibling: near, up: rotated_up });
                                                have plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model))) by { rewrite(nc.model == Context::Right(id, sid, Color::Black, rb_reparent(slm, id), Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um))); unfold(plug(Context::Right(id, sid, Color::Black, rb_reparent(slm, id), Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um)), nt.model)); unfold(plug(Context::Right(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model))); normalize(); }
                                                have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model)))); assumption(); }
                                                have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model)))); assumption(); }
                                                have erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rlm, rrm), slm), um), nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model))) by { unfold(erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rlm, rrm), slm), um), nt.model)); normalize(); }
                                                have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model)))); rewrite(plug(um, RbTree::Node(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), RbTree::Node(id, sid, Color::Black, rb_reparent(slm, id), nt.model))) == erase_flips_red_all_result(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(rid, sid, Color::Red, rlm, rrm), slm), um), nt.model)); rewrite(RbTree::Node(rid, sid, Color::Red, rlm, rrm) == srm); assumption(); }
                                                have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by auto;
                                                step(); # Break with a balanced context around the unchanged focus.

                                            },
                                        }
                                    }


                                },
                                Color::Red => {
                                    have at(iteration, c.model) == c.model by { normalize(); }
                                    have at(iteration, c.model) == Context::Right(id, above, pc, sm, um) by { rewrite(at(iteration, c.model) == c.model); assumption(); }
                                    let { sibling: s, up: u } = unfold(c);
                                    have aligned(id, 8) by { rewrite(id == parent); assumption(); }
                                    have rb_parent_is(RbTree::Node(sid, sp, sc, srm, slm), id) == 1 by {
                                        rewrite(RbTree::Node(sid, sp, sc, srm, slm) == sm); rewrite(id == parent); assumption();
                                    }
                                    apply(rb_parent_is_node_parent(sid, sp, sc, srm, slm, id));
                                    have s.model == RbTree::Node(sid, id, Color::Red, srm, slm) by {
                                        rewrite(s.model == sm); rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm));
                                        rewrite(sp == id); rewrite(sc == Color::Red); normalize();
                                    }
                                    have sm == RbTree::Node(sid, id, Color::Red, srm, slm) by {
                                        rewrite(sm == RbTree::Node(sid, sp, sc, srm, slm)); rewrite(sp == id); rewrite(sc == Color::Red); normalize();
                                    }
                                    have at(iteration, c.model) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Red, srm, slm), um) by {
                                        rewrite(at(iteration, c.model) == Context::Right(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, id, Color::Red, srm, slm)); normalize();
                                    }
                                    let { right: sl, left: sr } = unfold(s);
                                    step(); # Read the right child, which is the focus.
                                    mark focus_split;
                                    match t.model ensuring {
                                        owns nt: rb_at(node);
                                        fact nt.model == at(focus_split, t.model);
                                    } {
                                        RbTree::Empty => {
                                            have at(focus_split, t.model) == t.model by { normalize(); }
                                            have at(focus_split, t.model) == RbTree::Empty by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            unfold(t);
                                            step(); # The right child equals the null focus.
                                            let nt = fold(rb_at(node), { model: RbTree::Empty });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Empty); rewrite(at(focus_split, t.model) == RbTree::Empty); normalize(); }
                                        },
                                        RbTree::Node(tid, tp, tc, trm, tlm) => {
                                            have at(focus_split, t.model) == t.model by { normalize(); }
                                            have at(focus_split, t.model) == RbTree::Node(tid, tp, tc, trm, tlm) by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            let { right: tl, left: tr } = unfold(t);
                                            step(); # The right child equals the current focus.
                                            let nt = fold(rb_at(node), { model: RbTree::Node(tid, tp, tc, trm, tlm) }, { right: tl, left: tr });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Node(tid, tp, tc, trm, tlm)); rewrite(at(focus_split, t.model) == RbTree::Node(tid, tp, tc, trm, tlm)); normalize(); }
                                        },
                                    }
                                    step(); # Read the left sibling on the mirrored C arm.
                                    have is_rb(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_root_black(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_parent_is(nt.model, parent) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }

                                    have ctx_rb(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Red, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Red, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    apply(ctx_erase_case1_right_parent_black(above, id, pc, sid, srm, slm, um, Nat::Succ(black_height(nt.model))));
                                    have Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) == at(iteration, c.model) by { rewrite(at(iteration, c.model) == Context::Right(id, above, pc, RbTree::Node(sid, id, Color::Red, srm, slm), um)); rewrite(pc == Color::Black); normalize(); }
                                    have ctx_rb(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                        rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    have rb_tree_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model)) == 1 by {
                                        rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    have rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model), 0) == 1 by {
                                        unfold(rb_tree_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model)));
                                        rewrite(rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model))); assumption();
                                    }
                                    have erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                        rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    have rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                        rewrite(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    match sl.model {
                                        RbTree::Empty => {
                                            have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                            have erase_flips_red_all(at(iteration, c.model)) == 0 by { rewrite(at(iteration, c.model) == Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um)); rewrite(slm == RbTree::Empty); unfold(erase_flips_red_all(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Empty), um))); normalize(); }
                                            have not(erase_flips_red_all(at(iteration, c.model)) == 1) by { rewrite(erase_flips_red_all(at(iteration, c.model)) == 0); normalize(); }
                                            contradiction(erase_flips_red_all(at(iteration, c.model)) == 1);
                                        },
                                        RbTree::Node(zid, zp, zc, zlm, zrm) => {
                                            have slm == RbTree::Node(zid, zp, zc, zlm, zrm) by { rewrite(slm == sl.model); assumption(); }
                                            have zc == Color::Black by {
                                                if zc == Color::Black { assumption(); } else {
                                                    have erase_flips_red_all(at(iteration, c.model)) == 0 by { rewrite(at(iteration, c.model) == Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, slm), um)); rewrite(slm == RbTree::Node(zid, zp, zc, zlm, zrm)); unfold(erase_flips_red_all(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, zp, zc, zlm, zrm)), um))); normalize() using { not(zc == Color::Black); } }
                                                    have not(erase_flips_red_all(at(iteration, c.model)) == 1) by { rewrite(erase_flips_red_all(at(iteration, c.model)) == 0); normalize(); }
                                                    contradiction(erase_flips_red_all(at(iteration, c.model)) == 1);
                                                }
                                            }
                                            have rb_parent_is(RbTree::Node(zid, zp, zc, zlm, zrm), sid) == 1 by { rewrite(RbTree::Node(zid, zp, zc, zlm, zrm) == slm); rewrite(sid == parent->rb_left); assumption(); }
                                            apply(rb_parent_is_node_parent(zid, zp, zc, zlm, zrm, sid));
                                            have slm == RbTree::Node(zid, sid, Color::Black, zlm, zrm) by { rewrite(slm == RbTree::Node(zid, zp, zc, zlm, zrm)); rewrite(zp == sid); rewrite(zc == Color::Black); normalize(); }
                                            have ctx_rb(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                            have rb_parent_consistent(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), nt.model), 0) == 1 by { rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                            apply(ctx_erase_case1_right_step(above, id, sid, nt.model, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm), um));
                                            have rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id) == RbTree::Node(zid, id, Color::Black, zlm, zrm) by { unfold(rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); normalize(); }
                                            have ctx_rb(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(zid, id, Color::Black, zlm, zrm) == rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); assumption(); }
                                            have rb_parent_consistent(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model), 0) == 1 by { rewrite(RbTree::Node(zid, id, Color::Black, zlm, zrm) == rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); assumption(); }
                                            have rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), nt.model)) by { rewrite(RbTree::Node(zid, id, Color::Black, zlm, zrm) == rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); assumption(); }
                                            let { left: zl, right: zr } = unfold(sl);
                                            have sibling == sid by { simp(); }
                                            have parent->rb_left == sid by { simp(); }
                                            have parent->rb_left->rb_right == zid by { simp(); }
                                            have sid->rb_right == zid by { rewrite(sid == parent->rb_left); normalize() using { parent->rb_left->rb_right == zid; } }
                                            have aligned(sid, 8) by { simp(); }
                                            have aligned(zid, 8) by { simp(); }
                                            have (sid->__rb_parent_color & 1) == 0 by { rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                            have (parent->__rb_parent_color & 1) == 1 by { rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                                            have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 1); normalize(); }
                                            have parent->__rb_parent_color == address(above) + color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                            have u.model == um by { assumption(); }
                                            apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, Color::Black));
                                            have sid->rb_left == parent->rb_left->rb_left by { rewrite(sid == parent->rb_left); normalize(); }
                                            let far_link = fold(rb_saved_link(&sid->rb_left), { model: RbSavedLink::Link(parent->rb_left->rb_left) });
                                            mark red_inputs;
                                            step(); # Enter case 1 for the red sibling.
                                            step(); # Read its near child.
                                            step(); # Attach the near child under the parent.
                                            step(); # Attach the parent under the old sibling.
                                            step(); # Set the near child's black parent word.
                                            have tmp1 == zid by { simp(); }
                                            have tmp1->__rb_parent_color == (address(parent) | 1) by { assumption(); }
                                            have zid->__rb_parent_color == (address(id) | 1) by { simp() using { tmp1->__rb_parent_color == (address(parent) | 1); tmp1 == zid; parent == id; } }
                                            have zid->__rb_parent_color == address(id) + 1 by { rewrite(zid->__rb_parent_color == (address(id) | 1)); arithmetic() using { aligned(id, 8); } }
                                            have (zid->__rb_parent_color & 1) == 1 by { normalize(); }
                                            have (zid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                            have zid->__rb_parent_color == address(id) + (zid->__rb_parent_color & 1) by { normalize() using { zid->__rb_parent_color == address(id) + 1; (zid->__rb_parent_color & 1) == 1; } }
                                            let ns = fold(rb_at(zid), { model: RbTree::Node(zid, id, Color::Black, zlm, zrm) }, { left: zl, right: zr });
                                            have parent->rb_left == zid by { simp(); }
                                            have parent->rb_right == node by { simp(); }
                                            have sid->rb_right == parent by { simp(); }
                                            fold(rb_written_right_link(sid, parent));
                                            fold(rb_child_links(parent, zid, node));
                                            mark red_rotation;
                                            let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 0), { c: u });
                                            step(); # The callback preserves all tree resources.
                                            unfold(far_link);
                                            unfold(rb_written_right_link(sid, parent));
                                            unfold(rb_child_links(parent, zid, node));
                                            have sibling->__rb_parent_color == at(red_rotation, parent->__rb_parent_color) by { simp(); }
                                            have sid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == sid; parent == id; } }
                                            have sid->__rb_parent_color == at(red_rotation, parent->__rb_parent_color) by { rewrite(sid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                            have sid->__rb_parent_color == address(above) + 1 by { rewrite(sid->__rb_parent_color == at(red_rotation, parent->__rb_parent_color)); assumption(); }
                                            have (sid->__rb_parent_color & 1) == 1 by { rewrite(sid->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                            have (sid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                            have sid->__rb_parent_color == address(above) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == 1); assumption(); }
                                            have parent->__rb_parent_color == address(sibling) by { simp(); }
                                            have parent->__rb_parent_color == address(sid) by { rewrite(sid == sibling); normalize() using { parent->__rb_parent_color == address(sibling); } }
                                            have (parent->__rb_parent_color & 1) == 0 by { rewrite(parent->__rb_parent_color == address(sid)); arithmetic() using { aligned(sid, 8); } }
                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                                            have parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 0); assumption(); }
                                            have sid->rb_right == parent by { assumption(); }
                                            let red_up = fold(ctx_at(parent, root), { model: Context::Right(sid, above, Color::Black, srm, um) }, { sibling: sr, up: u });
                                            have ctx_node_is(Context::Right(sid, above, Color::Black, srm, um), sid) == 1 by { unfold(ctx_node_is(Context::Right(sid, above, Color::Black, srm, um), sid)); normalize(); }
                                            apply(ctx_reroot_fixed(Context::Right(sid, above, Color::Black, srm, um), sid));
                                            step(); # The near node becomes the new sibling.
                                            have sibling == zid by { simp(); }
                                            mark near_children;
                                            let { left: nleft, right: nright } = unfold(ns);
                                            step(); # Read the new sibling's far child.
                                            if rb_root_black(zlm) == 1 {
                                                if rb_root_black(zrm) == 1 {
                                                    apply(ctx_erase_case2_right_red_exit(sid, id, zid, nt.model, zlm, zrm, Context::Right(sid, above, Color::Black, srm, um)));
                                                    fold(rb_red_parent_tag(parent, sid));
                                                    match nleft.model ensuring {
                                                        owns rs: rb_at(tmp1);
                                                        fact rs.model == zlm;
                                                    } {
                                                        RbTree::Empty => {
                                                            have zlm == RbTree::Empty by { rewrite(zlm == nleft.model); assumption(); }
                                                            unfold(nleft);
                                                            step(); # The null child satisfies the black-child guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                            have rs.model == zlm by { rewrite(zlm == RbTree::Empty); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, crm, clm) => {
                                                            have zlm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(zlm == nleft.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == zlm); assumption(); }
                                                            apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                                            let { right: cl, left: cr } = unfold(nleft);
                                                            step(); # The owned black child's tag satisfies the guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                                            have rs.model == zlm by { rewrite(zlm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                                        },
                                                    }
                                                    step(); # Read the sibling's right child.
                                                    match nright.model ensuring {
                                                        owns ls: rb_at(tmp2);
                                                        fact ls.model == zrm;
                                                    } {
                                                        RbTree::Empty => {
                                                            have zrm == RbTree::Empty by { rewrite(zrm == nright.model); assumption(); }
                                                            unfold(nright);
                                                            step(); # The null child satisfies the black-child guard.
                                                            let ls = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                            have ls.model == zrm by { rewrite(zrm == RbTree::Empty); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, crm, clm) => {
                                                            have zrm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(zrm == nright.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == zrm); assumption(); }
                                                            apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                                            let { right: cl, left: cr } = unfold(nright);
                                                            step(); # The owned black child's tag satisfies the guard.
                                                            let ls = fold(rb_at(tmp2), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                                            have ls.model == zrm by { rewrite(zrm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                                        },
                                                    }
                                                    step(); # Recolor the sibling red, preserving its parent.
                                                    have zid->__rb_parent_color == address(id) by { rewrite(id == parent); simp(); }
                                                    have (zid->__rb_parent_color & 1) == 0 by { rewrite(zid->__rb_parent_color == address(id)); arithmetic() using { aligned(id, 8); } }
                                                    have (zid->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                                                    have zid->__rb_parent_color == address(id) + (zid->__rb_parent_color & 1) by { rewrite((zid->__rb_parent_color & 1) == 0); rewrite(zid->__rb_parent_color == address(id)); normalize(); }
                                                    let sn = fold(rb_at(zid), { model: RbTree::Node(zid, id, Color::Red, zlm, zrm) }, { right: ls, left: rs });
                                                    have rb_parent_is(nt.model, id) == 1 by { rewrite(id == parent); assumption(); }
                                                    have rb_parent_is(sn.model, id) == 1 by { rewrite(sn.model == RbTree::Node(zid, id, Color::Red, zlm, zrm)); unfold(rb_parent_is(RbTree::Node(zid, id, Color::Red, zlm, zrm), id)); normalize(); }
                                                    unfold(rb_red_parent_tag(parent, sid));
                                                    have parent->__rb_parent_color == address(sid) by { assumption(); }
                                                    have (parent->__rb_parent_color & 1) == 0 by { rewrite(parent->__rb_parent_color == address(sid)); arithmetic() using { aligned(sid, 8); } }
                                                    mark red_flip;
                                                    have at(red_flip, parent->__rb_parent_color) == address(sid) by { assumption(); }
                                                    step(); step(); # Select the red parent and blacken it.
                                                    have parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1 by { simp(); }
                                                    have parent->__rb_parent_color == address(sid) + 1 by { rewrite(parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1); rewrite(at(red_flip, parent->__rb_parent_color) == address(sid)); normalize(); }
                                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(sid) + 1); arithmetic() using { aligned(sid, 8); } }
                                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                    let nc = fold(ctx_at(node, root), { model: Context::Right(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)) }, { sibling: sn, up: red_up });
                                                    have plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model)) by { rewrite(nc.model == Context::Right(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um))); unfold(plug(Context::Right(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model)); normalize(); }
                                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(nc.model, nt.model)));
                                                        rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))); assumption();
                                                    }
                                                    have plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model)) == plug(um, RbTree::Node(sid, above, Color::Black, srm, RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))) by { unfold(plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))); normalize(); }
                                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, Color::Black, srm, RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))) by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))); assumption(); }
                                                    apply(erase_flips_red_all_right_red_result(id, above, sid, zid, srm, zlm, zrm, um, nt.model));
                                                    have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, Color::Black, srm, RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model)))); rewrite(plug(um, RbTree::Node(sid, above, Color::Black, srm, RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))) == erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), nt.model)); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))); rewrite(rb_inorder(plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), nt.model))) == rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model))); rewrite(rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), nt.model))); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                    step(); # The red-parent color flip completes the repair.

                                                } else {

                                                    match nleft.model ensuring {
                                                        owns rs: rb_at(tmp1);
                                                        fact rs.model == zlm;
                                                    } {
                                                        RbTree::Empty => {
                                                            have zlm == RbTree::Empty by { rewrite(zlm == nleft.model); assumption(); }
                                                            unfold(nleft);
                                                            step(); # The null child satisfies the black-child guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                            have rs.model == zlm by { rewrite(zlm == RbTree::Empty); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, crm, clm) => {
                                                            have zlm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(zlm == nleft.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == zlm); assumption(); }
                                                            apply(rb_root_black_node_color_bit(cid, cp, cc, crm, clm));
                                                            let { right: cl, left: cr } = unfold(nleft);
                                                            step(); # The owned black child's tag satisfies the guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, crm, clm) }, { right: cl, left: cr });
                                                            have rs.model == zlm by { rewrite(zlm == RbTree::Node(cid, cp, cc, crm, clm)); normalize(); }
                                                        },
                                                    }
                                                    step(); # Read the sibling's right child.
                                                    match nright.model {
                                                        RbTree::Empty => {
                                                            have zrm == RbTree::Empty by { rewrite(zrm == nright.model); assumption(); }
                                                            have rb_root_black(zrm) == 1 by { rewrite(zrm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                            contradiction(rb_root_black(zrm) == 1);
                                                        },
                                                        RbTree::Node(iid, ip, ic, ilm, irm) => {
                                                            have zrm == RbTree::Node(iid, ip, ic, ilm, irm) by { rewrite(zrm == nright.model); assumption(); }
                                                            have not(rb_root_black(RbTree::Node(iid, ip, ic, ilm, irm)) == 1) by { rewrite(RbTree::Node(iid, ip, ic, ilm, irm) == zrm); assumption(); }
                                                            apply(outer_nonblack_node_color(iid, ip, ic, ilm, irm));
                                                            have rb_parent_is(RbTree::Node(iid, ip, ic, ilm, irm), zid) == 1 by { rewrite(RbTree::Node(iid, ip, ic, ilm, irm) == zrm); rewrite(zid == parent->rb_left); assumption(); }
                                                            apply(rb_parent_is_node_parent(iid, ip, ic, ilm, irm, zid));
                                                            have zrm == RbTree::Node(iid, zid, Color::Red, ilm, irm) by { rewrite(zrm == RbTree::Node(iid, ip, ic, ilm, irm)); rewrite(ip == zid); rewrite(ic == Color::Red); normalize(); }
                                                            have ctx_rb(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm)), Context::Right(sid, above, Color::Black, srm, um)), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(iid, zid, Color::Red, ilm, irm) == zrm); assumption(); }
                                                            have rb_parent_consistent(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm)), Context::Right(sid, above, Color::Black, srm, um)), nt.model), 0) == 1 by { rewrite(RbTree::Node(iid, zid, Color::Red, ilm, irm) == zrm); assumption(); }
                                                            apply(ctx_erase_case3_right_exit(sid, id, Color::Red, zid, iid, nt.model, zlm, ilm, irm, Context::Right(sid, above, Color::Black, srm, um)));

                                                            apply(ctx_rb_right_sibling(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm)), Context::Right(sid, above, Color::Black, srm, um), Nat::Succ(black_height(nt.model)), Color::Black));
                                                            apply(is_rb_node_right(zid, id, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm)));
                                                            apply(is_rb_red_node_children_are_black(iid, zid, ilm, irm));
                                                            let { left: il, right: ir } = unfold(nright);
                                                            have tmp2 == iid;
                                                            have sibling == zid;
                                                            have (iid->__rb_parent_color & 1) == 0 by { rewrite((iid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Red)); normalize(); }
                                                            mark inner_inputs;
                                                            step(); # The red near child selects case 3.
                                                            step(); # Leave the untaken case-2 body.
                                                            step(); # Read its left child.
                                                            step(); # Move that child under the old sibling.
                                                            have zid->rb_right == tmp1;
                                                            mark sibling_link_written;
                                                            step(); # Put the old sibling under the red node.
                                                            step(); # Update the parent's child link.
                                                            have aligned(zid, 8);
                                                            have separate(memory(parent->__rb_parent_color), memory(tmp2->rb_left));
                                                            have separate(memory(parent->__rb_parent_color), memory(sibling->rb_right));
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { transport(at(inner_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red), parent->__rb_parent_color == address(sid) + color_bit(Color::Red)) using { at(inner_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red); separate(memory(parent->__rb_parent_color), memory(tmp2->rb_left)); separate(memory(parent->__rb_parent_color), memory(sibling->rb_right)); tmp2 == iid; sibling == zid; parent == id; }; }
                                                            have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                            have parent->rb_right == node;
                                                            have parent->rb_left == iid;
                                                            have iid->rb_left == zid;
                                                            have zid->rb_right == tmp1;
                                                            have zid->rb_left == at(inner_inputs, zid->rb_left);
                                                            have iid->rb_right == at(inner_inputs, iid->rb_right);
                                                            mark first_update;
                                                            match il.model ensuring {
                                                                owns first_near: rb_at(tmp1);
                                                                fact first_near.model == rb_reparent(ilm, zid);
                                                                fact parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                                fact parent->rb_right == node;
                                                                fact parent->rb_left == iid;
                                                                fact iid->rb_left == zid;
                                                                fact zid->rb_right == tmp1;
                                                                fact zid->rb_left == at(inner_inputs, zid->rb_left);
                                                                fact iid->rb_right == at(inner_inputs, iid->rb_right);
                                                            } {
                                                                RbTree::Empty => {
                                                                    have ilm == RbTree::Empty by { rewrite(ilm == il.model); assumption(); }
                                                                    unfold(il);
                                                                    step(); step(); # Select and leave the null grandchild branch.
                                                                    let first_near = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                                    have first_near.model == rb_reparent(ilm, zid) by { rewrite(ilm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, zid)); normalize(); }
                                                                },
                                                                RbTree::Node(cid, cp, cc, clm, crm) => {
                                                                    have ilm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(ilm == il.model); assumption(); }
                                                                    have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == ilm); assumption(); }
                                                                    apply(outer_black_node_color(cid, cp, cc, clm, crm));
                                                                    let { left: cl, right: cr } = unfold(il);
                                                                    have tmp1 == cid;
                                                                    have separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)) by assumption();
                                                                    step(); # Enter the nonempty grandchild update.
                                                                    step(); # Store its new black parent word.
                                                                    have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                                    have cid->__rb_parent_color == (address(zid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == cid; sibling == zid; } }
                                                                    have cid->__rb_parent_color == address(zid) + 1 by { rewrite(cid->__rb_parent_color == (address(zid) | 1)); arithmetic() using { aligned(zid, 8); } }
                                                                    have (cid->__rb_parent_color & 1) == 1 by normalize();
                                                                    have cid->__rb_parent_color == address(zid) + (cid->__rb_parent_color & 1) by { normalize() using { cid->__rb_parent_color == address(zid) + 1; (cid->__rb_parent_color & 1) == 1; } }
                                                                    have (cid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                                    let first_near = fold(rb_at(tmp1), { model: RbTree::Node(cid, zid, Color::Black, clm, crm) }, { left: cl, right: cr });
                                                                    have first_near.model == rb_reparent(ilm, zid) by { rewrite(ilm == RbTree::Node(cid, cp, cc, clm, crm)); rewrite(cc == Color::Black); unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, clm, crm), zid)); normalize(); }
                                                                    have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { transport(at(first_update, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red), parent->__rb_parent_color == address(sid) + color_bit(Color::Red)) using { at(first_update, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red); separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)); tmp1 == cid; }; }
                                                                    have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                                    have parent->rb_right == node by { normalize() using { at(first_update, parent->rb_right == node); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have parent->rb_left == iid by { normalize() using { at(first_update, parent->rb_left == iid); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have iid->rb_left == zid by { normalize() using { at(first_update, iid->rb_left == zid); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have zid->rb_right == tmp1 by { normalize() using { at(first_update, zid->rb_right == tmp1); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have zid->rb_left == at(inner_inputs, zid->rb_left) by { normalize() using { at(first_update, zid->rb_left == at(inner_inputs, zid->rb_left)); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have iid->rb_right == at(inner_inputs, iid->rb_right) by { normalize() using { at(first_update, iid->rb_right == at(inner_inputs, iid->rb_right)); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                },
                                                            }
                                                            step(); # The augmentation callback preserves tree fields.
                                                            step(); step(); # Select the new sibling and far child for case 4.
                                                            have tmp1 == zid;
                                                            have sibling == iid;
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color)); assumption(); }
                                                            have parent->rb_right == node by assumption();
                                                            have iid->rb_left == zid by assumption();
                                                            mark outer_inputs;
                                                            have separate(memory(parent->__rb_parent_color), memory(sibling->rb_right)) by assumption();
                                                            have separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)) by assumption();
                                                            step(); # Read the near child.
                                                            step(); # Attach the near child to the parent.
                                                            step(); # Attach the parent under the sibling.
                                                            step(); # Blacken the far child.
                                                            have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                            have zid->__rb_parent_color == (address(iid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == zid; sibling == iid; } }
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { transport(at(outer_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red), parent->__rb_parent_color == address(sid) + color_bit(Color::Red)) using { at(outer_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red); separate(memory(parent->__rb_parent_color), memory(sibling->rb_right)); separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)); tmp1 == zid; sibling == iid; }; }
                                                            have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                            have parent->rb_right == node by { simp() using { at(outer_inputs, parent->rb_right) == node; tmp1 == zid; sibling == iid; } }
                                                            have parent->rb_left == tmp2 by { simp() using { tmp1 == zid; sibling == iid; } }
                                                            have sibling->rb_right == parent by assumption();
                                                            have iid->rb_right == parent by { rewrite(iid == sibling); normalize() using { sibling->rb_right == parent; } }
                                                            have sibling->rb_left == tmp1;
                                                            have iid->rb_left == zid by { rewrite(iid == sibling); rewrite(zid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                            have id->rb_right == node by { simp() using { parent->rb_right == node; parent == id; } }
                                                            mark near_update;
                                                            match ir.model ensuring {
                                                                owns near: rb_at(tmp2);
                                                                fact near.model == rb_reparent(irm, parent);
                                                                fact parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                                fact parent->rb_right == node;
                                                                fact parent->rb_left == tmp2;
                                                                fact iid->rb_right == parent;
                                                                fact iid->rb_left == zid;
                                                                fact zid->__rb_parent_color == (address(iid) | 1);
                                                            } {
                                                                RbTree::Empty => {
                                                                    have irm == RbTree::Empty by { rewrite(irm == ir.model); assumption(); }
                                                                    unfold(ir);
                                                                    have tmp2 == 0;
                                                                    step(); step(); # Select and complete the empty C arm.
                                                                    let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                                    have near.model == rb_reparent(irm, parent) by { rewrite(irm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                                    have zid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, zid->__rb_parent_color == (address(iid) | 1)); sibling == iid; tmp1 == zid; } }
                                                                },
                                                                RbTree::Node(nid, np, nc, nlm, nrm) => {
                                                                    have irm == RbTree::Node(nid, np, nc, nlm, nrm) by { rewrite(irm == ir.model); assumption(); }
                                                                    let { left: nl, right: nr } = unfold(ir);
                                                                    have tmp2 == nid;
                                                                    have tmp2 != 0;
                                                                    have separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color));
                                                                    have separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color)) by { transport(separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)), separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color))) using { separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)); sibling == iid; }; }
                                                                    have (tmp2->__rb_parent_color & 1) == color_bit(nc);
                                                                    mark near_tag;
                                                                    step(); # Select the nonempty near-child parent update.
                                                                    step(rb_set_parent(tmp2, parent), {});
                                                                    have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                                    have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                                        rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                                        if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                    }
                                                                    have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                                        rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                                        if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                    }
                                                                    have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                                    let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nlm, nrm) }, { left: nl, right: nr });
                                                                    have near.model == rb_reparent(irm, parent) by { rewrite(irm == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nlm, nrm), parent)); simp(); }
                                                                    have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { normalize() using { at(near_update, parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); tmp2 == nid; sibling == iid; tmp1 == zid; } }
                                                                    have id->rb_right == node;
                                                                    have parent->rb_right == node;
                                                                    have parent->rb_left == tmp2 by { normalize() using { at(near_update, parent->rb_left == tmp2); tmp2 == nid; sibling == iid; tmp1 == zid; } }
                                                                    have sibling->rb_right == parent by { transport(at(near_update, sibling->rb_right) == parent, sibling->rb_right == parent) using { at(near_update, sibling->rb_right) == parent; separate(memory(sibling->rb_right), memory(tmp2->__rb_parent_color)); tmp2 == nid; sibling == iid; parent == id; }; }
                                                                    have iid->rb_right == parent by { transport(at(near_update, iid->rb_right) == parent, iid->rb_right == parent) using { at(near_update, iid->rb_right) == parent; separate(memory(iid->rb_right), memory(tmp2->__rb_parent_color)); tmp2 == nid; }; }
                                                                    have sibling->rb_left == tmp1;
                                                                    have iid->rb_left == zid by { rewrite(iid == sibling); rewrite(zid == tmp1); normalize() using { sibling->rb_left == tmp1; } }
                                                                    have zid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, zid->__rb_parent_color == (address(iid) | 1)); tmp2 == nid; sibling == iid; tmp1 == zid; } }
                                                                },
                                                            }
                                                            have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by assumption();
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                            have red_up.model == Context::Right(sid, above, Color::Black, srm, um) by assumption();
                                                            apply(ctx_parent_word_from_color(red_up.model, sid, parent->__rb_parent_color, Color::Red));
                                                            have parent->rb_right == node by assumption();
                                                            have parent->rb_left == tmp2 by assumption();
                                                            have iid->rb_right == parent by assumption();
                                                            have iid->rb_left == zid by assumption();
                                                            have zid->__rb_parent_color == (address(iid) | 1) by assumption();
                                                            have aligned(iid, 8);
                                                            have zid->__rb_parent_color == address(iid) + 1 by { rewrite(zid->__rb_parent_color == (address(iid) | 1)); arithmetic() using { aligned(iid, 8); } }
                                                            have (zid->__rb_parent_color & 1) == 1 by normalize();
                                                            have zid->__rb_parent_color == address(iid) + (zid->__rb_parent_color & 1) by { normalize() using { zid->__rb_parent_color == address(iid) + 1; (zid->__rb_parent_color & 1) == 1; } }
                                                            have (zid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                            apply(rb_reparent_parent_is(ilm, zid));
                                                            have zid->rb_right == at(first_update, tmp1) by { normalize() using { at(first_update, zid->rb_right == tmp1); sibling == iid; tmp1 == zid; }; }
                                                            let far_tree = fold(rb_at(zid), { model: RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)) }, { left: rs, right: first_near });
                                                            apply(rb_parent_is_node_of(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)));
                                                            fold(rb_child_links(iid, zid, parent));
                                                            fold(rb_child_links(parent, tmp2, node));
                                                            mark outer_rotation;
                                                            let { after: red_up } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: red_up });
                                                            step(); # The augmentation callback preserves the tree resources.
                                                            unfold(rb_child_links(iid, zid, parent));
                                                            unfold(rb_child_links(parent, tmp2, node));
                                                            have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color);
                                                            have iid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == iid; parent == id; } }
                                                            have iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(iid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                            have iid->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                            have (iid->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                                rewrite(iid->__rb_parent_color == address(sid) + color_bit(Color::Red));
                                                                if color_bit(Color::Red) == 0 { rewrite(color_bit(Color::Red) == 0); arithmetic() using { aligned(sid, 8); } } else { apply(color_bit_nonzero_is_one(Color::Red)); rewrite(color_bit(Color::Red) == 1); arithmetic() using { aligned(sid, 8); } }
                                                            }
                                                            have iid->__rb_parent_color == address(sid) + (iid->__rb_parent_color & 1) by { rewrite((iid->__rb_parent_color & 1) == color_bit(Color::Red)); assumption(); }
                                                            have parent->__rb_parent_color == address(iid) + 1;
                                                            have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(iid) + 1); arithmetic() using { aligned(iid, 8); } }
                                                            have parent->__rb_parent_color == address(iid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                            have iid->rb_right == parent by assumption();
                                                            have iid->rb_left == zid by assumption();
                                                            let rotated_up = fold(ctx_at(parent, root), { model: Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um)) }, { sibling: far_tree, up: red_up });
                                                            have ctx_node_is(Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um)), iid) == 1 by { unfold(ctx_node_is(Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um)), iid)); normalize(); }
                                                            apply(ctx_reroot_fixed(Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um)), iid));
                                                            have near.model == rb_reparent(irm, id) by { rewrite(id == parent); assumption(); }
                                                            apply(rb_reparent_parent_is(irm, id));
                                                            have parent->rb_right == node by assumption();
                                                            have parent->rb_left == tmp2 by assumption();
                                                            let nc = fold(ctx_at(node, root), { model: Context::Right(id, iid, Color::Black, rb_reparent(irm, id), Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um))) }, { sibling: near, up: rotated_up });
                                                            have plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))) by { rewrite(nc.model == Context::Right(id, iid, Color::Black, rb_reparent(irm, id), Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um)))); unfold(plug(Context::Right(id, iid, Color::Black, rb_reparent(irm, id), Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um))), nt.model)); unfold(plug(Context::Right(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), Context::Right(sid, above, Color::Black, srm, um)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))); normalize(); }
                                                            have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))); assumption(); }
                                                            have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))); assumption(); }
                                                            have plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))) == erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm))), um), nt.model) by {
                                                                unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm))), um), nt.model));
                                                                apply(black_root_has_black_color(zlm)); rewrite(rb_color(zlm) == Color::Black); unfold(rb_color(RbTree::Node(iid, zid, Color::Red, ilm, irm))); normalize();
                                                            }
                                                            have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                                rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))));
                                                                rewrite(plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))) == erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm))), um), nt.model));
                                                                rewrite(RbTree::Node(iid, zid, Color::Red, ilm, irm) == zrm);
                                                                rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption();
                                                            }
                                                            have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                                rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model))));
                                                                rewrite(rb_inorder(plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, zlm, rb_reparent(ilm, zid)), RbTree::Node(id, iid, Color::Black, rb_reparent(irm, id), nt.model)))) == rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(iid, zid, Color::Red, ilm, irm)), Context::Right(sid, above, Color::Black, srm, um)), nt.model)));
                                                                rewrite(RbTree::Node(iid, zid, Color::Red, ilm, irm) == zrm);
                                                                rewrite(rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), nt.model)));
                                                                rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption();
                                                            }
                                                            step(); # Break after both rotations with a balanced whole tree.
                                                        },
                                                    }

                                                }
                                            } else {
                                                match nleft.model {
                                                    RbTree::Empty => {
                                                        have zlm == RbTree::Empty by { rewrite(zlm == nleft.model); assumption(); }
                                                        have rb_root_black(zlm) == 1 by { rewrite(zlm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                        contradiction(rb_root_black(zlm) == 1);
                                                    },
                                                    RbTree::Node(rid, rp, rc, rlm, rrm) => {
                                                        have zlm == RbTree::Node(rid, rp, rc, rlm, rrm) by { rewrite(zlm == nleft.model); assumption(); }
                                                        have not(rb_root_black(RbTree::Node(rid, rp, rc, rlm, rrm)) == 1) by { rewrite(RbTree::Node(rid, rp, rc, rlm, rrm) == zlm); assumption(); }
                                                        apply(outer_nonblack_node_color(rid, rp, rc, rlm, rrm));
                                                        have rb_parent_is(RbTree::Node(rid, rp, rc, rlm, rrm), zid) == 1 by { rewrite(RbTree::Node(rid, rp, rc, rlm, rrm) == zlm); assumption(); }
                                                        apply(rb_parent_is_node_parent(rid, rp, rc, rlm, rrm, zid));
                                                        have zlm == RbTree::Node(rid, zid, Color::Red, rlm, rrm) by { rewrite(zlm == RbTree::Node(rid, rp, rc, rlm, rrm)); rewrite(rp == zid); rewrite(rc == Color::Red); normalize(); }
                                                        have ctx_rb(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(rid, zid, Color::Red, rlm, rrm), zrm), Context::Right(sid, above, Color::Black, srm, um)), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(rid, zid, Color::Red, rlm, rrm) == zlm); assumption(); }
                                                        have rb_parent_consistent(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(rid, zid, Color::Red, rlm, rrm), zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model), 0) == 1 by { rewrite(RbTree::Node(rid, zid, Color::Red, rlm, rrm) == zlm); assumption(); }
                                                        apply(ctx_erase_case4_right_exit(sid, id, Color::Red, zid, rid, nt.model, zrm, rlm, rrm, Context::Right(sid, above, Color::Black, srm, um)));
                                                        let { left: rl, right: rr } = unfold(nleft);
                                                        have tmp1 == rid by { simp(); }
                                                        have sibling == zid by { simp(); }
                                                        have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                        have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Red)); normalize(); }
                                                        have parent->rb_right == node by { simp(); }
                                                        have sibling->rb_left == tmp1 by { simp(); }
                                                        have zid->rb_left == sibling->rb_left by { normalize() using { sibling == zid; } }
                                                        have zid->rb_left == rid by { rewrite(zid->rb_left == sibling->rb_left); rewrite(sibling->rb_left == tmp1); assumption(); }
                                                        mark outer_inputs;
                                                        have at(outer_inputs, parent->__rb_parent_color) == address(sid) by { assumption(); }
                                                        fold(rb_red_parent_tag(parent, sid));
                                                        step(); # Red far child skips cases 2 and 3.
                                                        step(); # Read the near child.
                                                        step(); # Attach the near child to the parent.
                                                        step(); # Attach the parent under the sibling.
                                                        step(); # Blacken the far child.
                                                        step(); # Execute the far-child parent/color store.
                                                        have tmp1->__rb_parent_color == (address(sibling) | 1) by { assumption(); }
                                                        have rid->__rb_parent_color == (address(zid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == rid; sibling == zid; } }
                                                        unfold(rb_red_parent_tag(parent, sid));
                                                        have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { rewrite(parent->__rb_parent_color == address(sid)); rewrite(at(outer_inputs, parent->__rb_parent_color) == address(sid)); normalize(); }
                                                        have parent->rb_right == node by { simp() using { at(outer_inputs, parent->rb_right) == node; tmp1 == rid; sibling == zid; } }
                                                        have parent->rb_left == tmp2 by { simp() using { tmp1 == rid; sibling == zid; } }
                                                        have sibling->rb_right == parent by { assumption(); }
                                                        have zid->rb_right == parent by { rewrite(zid == sibling); normalize() using { sibling->rb_right == parent; } }
                                                        have sibling->rb_left == tmp1 by { simp(); }
                                                        have zid->rb_left == sibling->rb_left by { normalize() using { sibling == zid; } }
                                                        have zid->rb_left == rid by { rewrite(zid->rb_left == sibling->rb_left); rewrite(sibling->rb_left == tmp1); assumption(); }
                                                        have id->rb_right == node by { simp() using { parent->rb_right == node; parent == id; } }
                                                        have rid->__rb_parent_color == (address(zid) | 1) by { assumption(); }
                                                        have aligned(zid, 8) by { simp(); }
                                                        have rid->__rb_parent_color == address(zid) + 1 by { rewrite(rid->__rb_parent_color == (address(zid) | 1)); arithmetic() using { aligned(zid, 8); } }
                                                        have (rid->__rb_parent_color & 1) == 1 by { normalize(); }
                                                        have rid->__rb_parent_color == address(zid) + (rid->__rb_parent_color & 1) by { normalize() using { rid->__rb_parent_color == address(zid) + 1; (rid->__rb_parent_color & 1) == 1; } }
                                                        have (rid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                        let far_tree = fold(rb_at(rid), { model: RbTree::Node(rid, zid, Color::Black, rlm, rrm) }, { left: rl, right: rr });
                                                        apply(rb_parent_is_node_of(rid, zid, Color::Black, rlm, rrm));
                                                        fold(rb_child_links(zid, rid, parent));
                                                        fold(rb_child_links(parent, tmp2, node));
                                                        fold(rb_red_parent_tag(parent, sid));
                                                        match nright.model ensuring {
                                                            owns near: rb_at(tmp2);
                                                            fact near.model == rb_reparent(zrm, parent);
                                                        } {
                                                            RbTree::Empty => {
                                                                have zrm == RbTree::Empty by { rewrite(zrm == nright.model); assumption(); }
                                                                unfold(nright);
                                                                have tmp2 == 0 by { simp(); }
                                                                step(); step();
                                                                let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                                have near.model == rb_reparent(zrm, parent) by { rewrite(zrm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                            },
                                                            RbTree::Node(nid, np, nc, nlm, nrm) => {
                                                                have zrm == RbTree::Node(nid, np, nc, nlm, nrm) by { rewrite(zrm == nright.model); assumption(); }
                                                                let { left: nl, right: nr } = unfold(nright);
                                                                have tmp2 == nid by { simp(); }
                                                                have tmp2 != 0 by { simp(); }
                                                                have (tmp2->__rb_parent_color & 1) == color_bit(nc) by { simp(); }
                                                                mark near_tag;
                                                                step();
                                                                step(rb_set_parent(tmp2, parent), {});
                                                                have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                                have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                                    rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                                    if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                }
                                                                have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                                    rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                                    if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                }
                                                                have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                                let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nlm, nrm) }, { left: nl, right: nr });
                                                                have near.model == rb_reparent(zrm, parent) by { rewrite(zrm == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nlm, nrm), parent)); simp(); }
                                                            },
                                                        }
                                                        unfold(rb_red_parent_tag(parent, sid));
                                                        unfold(rb_child_links(zid, rid, parent));
                                                        unfold(rb_child_links(parent, tmp2, node));
                                                        have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { rewrite(parent->__rb_parent_color == address(sid)); rewrite(at(outer_inputs, parent->__rb_parent_color) == address(sid)); normalize(); }
                                                        have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                        have red_up.model == Context::Right(sid, above, Color::Black, srm, um) by { assumption(); }
                                                        apply(ctx_parent_word_from_color(red_up.model, sid, parent->__rb_parent_color, Color::Red));
                                                        have parent->rb_right == node by { assumption(); }
                                                        have parent->rb_left == tmp2 by { assumption(); }
                                                        have zid->rb_right == parent by { assumption(); }
                                                        have zid->rb_left == rid by { assumption(); }
                                                        fold(rb_child_links(zid, rid, parent));
                                                        fold(rb_child_links(parent, tmp2, node));
                                                        mark outer_rotation;
                                                        let { after: red_up } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: red_up });
                                                        step(); # The augmentation callback preserves the tree resources.
                                                        unfold(rb_child_links(zid, rid, parent));
                                                        unfold(rb_child_links(parent, tmp2, node));
                                                        have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { simp(); }
                                                        have zid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == zid; parent == id; } }
                                                        have zid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(zid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                        have zid->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(zid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                        have (zid->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(zid->__rb_parent_color == address(sid) + color_bit(Color::Red));
                                                            if color_bit(Color::Red) == 0 { rewrite(color_bit(Color::Red) == 0); arithmetic() using { aligned(sid, 8); } } else { apply(color_bit_nonzero_is_one(Color::Red)); rewrite(color_bit(Color::Red) == 1); arithmetic() using { aligned(sid, 8); } }
                                                        }
                                                        have zid->__rb_parent_color == address(sid) + (zid->__rb_parent_color & 1) by { rewrite((zid->__rb_parent_color & 1) == color_bit(Color::Red)); assumption(); }
                                                        have parent->__rb_parent_color == address(zid) + 1 by { simp(); }
                                                        have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(zid) + 1); arithmetic() using { aligned(zid, 8); } }
                                                        have parent->__rb_parent_color == address(zid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                        have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                        have zid->rb_right == parent by { assumption(); }
                                                        have zid->rb_left == rid by { assumption(); }
                                                        have zid->__rb_parent_color == address(sid) by { rewrite(zid->__rb_parent_color == address(sid) + color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                        let rotated_up = fold(ctx_at(parent, root), { model: Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um)) }, { sibling: far_tree, up: red_up });
                                                        have ctx_node_is(Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um)), zid) == 1 by { unfold(ctx_node_is(Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um)), zid)); normalize(); }
                                                        apply(ctx_reroot_fixed(Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um)), zid));
                                                        have near.model == rb_reparent(zrm, id) by { rewrite(id == parent); assumption(); }
                                                        apply(rb_reparent_parent_is(zrm, id));
                                                        have parent->rb_right == node by { assumption(); }
                                                        have parent->rb_left == tmp2 by { assumption(); }
                                                        let nc = fold(ctx_at(node, root), { model: Context::Right(id, zid, Color::Black, rb_reparent(zrm, id), Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um))) }, { sibling: near, up: rotated_up });
                                                        have plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model))) by { rewrite(nc.model == Context::Right(id, zid, Color::Black, rb_reparent(zrm, id), Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um)))); unfold(plug(Context::Right(id, zid, Color::Black, rb_reparent(zrm, id), Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um))), nt.model)); unfold(plug(Context::Right(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), Context::Right(sid, above, Color::Black, srm, um)), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model))); normalize(); }
                                                        have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model)))); assumption(); }
                                                        have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model)))); assumption(); }
                                                        have rb_root_black(RbTree::Node(rid, zid, Color::Red, rlm, rrm)) == 0 by { unfold(rb_root_black(RbTree::Node(rid, zid, Color::Red, rlm, rrm))); normalize(); }
                                                        have erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, RbTree::Node(rid, zid, Color::Red, rlm, rrm), zrm)), um), nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model))) by { unfold(erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, RbTree::Node(rid, zid, Color::Red, rlm, rrm), zrm)), um), nt.model)); unfold(rb_color(RbTree::Node(rid, zid, Color::Red, rlm, rrm))); normalize(); }
                                                        have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model)))); rewrite(plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model))) == erase_flips_red_all_result(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, RbTree::Node(rid, zid, Color::Red, rlm, rrm), zrm)), um), nt.model)); rewrite(RbTree::Node(rid, zid, Color::Red, rlm, rrm) == zlm); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                        have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model)))); rewrite(rb_inorder(plug(Context::Right(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rlm, rrm), RbTree::Node(id, zid, Color::Black, rb_reparent(zrm, id), nt.model)))) == rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(rid, zid, Color::Red, rlm, rrm), zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model))); rewrite(RbTree::Node(rid, zid, Color::Red, rlm, rrm) == zlm); rewrite(rb_inorder(plug(Context::Right(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Right(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Right(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, srm, RbTree::Node(zid, sid, Color::Black, zlm, zrm)), um), nt.model))); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                        step(); # Break with a balanced context around the unchanged focus.

                                                    },
                                                }
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
                Context::Left(id, above, pc, sm, um) => {
                    have ctx_node_is(Context::Left(id, above, pc, sm, um), parent) == 1 by {
                        rewrite(Context::Left(id, above, pc, sm, um) == c.model); assumption();
                    }
                    have parent == id by {
                        apply(ctx_node_is_left_identity(id, above, pc, sm, um, parent)) using {
                            ctx_node_is(Context::Left(id, above, pc, sm, um), parent) == 1;
                        }
                        assumption();
                    }
                    match sm {
                        RbTree::Empty => {
                            have erase_flips_red_all(c.model) == 0 by {
                                rewrite(c.model == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Empty);
                                unfold(erase_flips_red_all(Context::Left(id, above, pc, RbTree::Empty, um))); normalize();
                            }
                            have not(erase_flips_red_all(c.model) == 1) by { rewrite(erase_flips_red_all(c.model) == 0); normalize(); }
                            contradiction(erase_flips_red_all(c.model) == 1);
                        },
                        RbTree::Node(sid, sp, sc, slm, srm) => {
                            match sc {
                                Color::Black => {


                                    have at(iteration, c.model) == c.model by normalize();
                                    have at(iteration, c.model) == Context::Left(id, above, pc, sm, um) by { rewrite(at(iteration, c.model) == c.model); assumption(); }
                                    let { sibling: s, up: u } = unfold(c);
                                    have aligned(id, 8) by { rewrite(id == parent); assumption(); }
                                    have rb_parent_is(RbTree::Node(sid, sp, sc, slm, srm), id) == 1 by {
                                        rewrite(RbTree::Node(sid, sp, sc, slm, srm) == sm); rewrite(id == parent); assumption();
                                    }
                                    apply(rb_parent_is_node_parent(sid, sp, sc, slm, srm, id));
                                    have s.model == RbTree::Node(sid, id, Color::Black, slm, srm) by {
                                        rewrite(s.model == sm); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                        rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                                    }
                                    have sm == RbTree::Node(sid, id, Color::Black, slm, srm) by {
                                        rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm)); rewrite(sp == id); rewrite(sc == Color::Black); normalize();
                                    }
                                    have at(iteration, c.model) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) by {
                                        rewrite(at(iteration, c.model) == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, id, Color::Black, slm, srm)); normalize();
                                    }
                                    let { left: sl, right: sr } = unfold(s);
                                    step(); # Read the sibling.
                                    mark focus_split;
                                    match t.model ensuring {
                                        owns nt: rb_at(node);
                                        fact nt.model == at(focus_split, t.model);
                                    } {
                                        RbTree::Empty => {
                                            have at(focus_split, t.model) == t.model by normalize();
                                            have at(focus_split, t.model) == RbTree::Empty by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            unfold(t);
                                            step(); # The null focus differs from the sibling.
                                            let nt = fold(rb_at(node), { model: RbTree::Empty });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Empty); rewrite(at(focus_split, t.model) == RbTree::Empty); normalize(); }
                                        },
                                        RbTree::Node(tid, tp, tc, tlm, trm) => {
                                            have at(focus_split, t.model) == t.model by normalize();
                                            have at(focus_split, t.model) == RbTree::Node(tid, tp, tc, tlm, trm) by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            let { left: tl, right: tr } = unfold(t);
                                            step(); # Separate owned roots distinguish the two pointers.
                                            let nt = fold(rb_at(node), { model: RbTree::Node(tid, tp, tc, tlm, trm) }, { left: tl, right: tr });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Node(tid, tp, tc, tlm, trm)); rewrite(at(focus_split, t.model) == RbTree::Node(tid, tp, tc, tlm, trm)); normalize(); }
                                        },
                                    }
                                    have is_rb(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_root_black(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_parent_is(nt.model, parent) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have (sid->__rb_parent_color & 1) == 1 by {
                                        rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); normalize();
                                    }
                                    step(); step(); # Skip the red-sibling rotation.
                                    step(); # Read the sibling's right child.
                                    if rb_root_black(srm) == 1 {
                                        if rb_root_black(slm) == 1 {


                                            match sr.model ensuring {
                                                owns rs: rb_at(tmp1);
                                                fact rs.model == srm;
                                            } {
                                                RbTree::Empty => {
                                                    have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                                    unfold(sr);
                                                    step(); # The null child satisfies the black-child guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Empty); normalize(); }
                                                },
                                                RbTree::Node(cid, cp, cc, clm, crm) => {
                                                    have srm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(srm == sr.model); assumption(); }
                                                    have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == srm); assumption(); }
                                                    apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                                    let { left: cl, right: cr } = unfold(sr);
                                                    step(); # The owned black child's tag satisfies the guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                                },
                                            }
                                            step(); # Read the sibling's left child.
                                            match sl.model ensuring {
                                                owns ls: rb_at(tmp2);
                                                fact ls.model == slm;
                                            } {
                                                RbTree::Empty => {
                                                    have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                                    unfold(sl);
                                                    step(); # The null child satisfies the black-child guard.
                                                    let ls = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                    have ls.model == slm by { rewrite(slm == RbTree::Empty); normalize(); }
                                                },
                                                RbTree::Node(cid, cp, cc, clm, crm) => {
                                                    have slm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(slm == sl.model); assumption(); }
                                                    have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == slm); assumption(); }
                                                    apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                                    let { left: cl, right: cr } = unfold(sl);
                                                    step(); # The owned black child's tag satisfies the guard.
                                                    let ls = fold(rb_at(tmp2), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                                    have ls.model == slm by { rewrite(slm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                                },
                                            }
                                            have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            have rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == 1 by {
                                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            have rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by {
                                                unfold(rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)));
                                                rewrite(rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model))); assumption();
                                            }
                                            have erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            have rb_inorder(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                            }
                                            step(); # Recolor the sibling red, preserving its parent.
                                            have sid->__rb_parent_color == address(id) by { rewrite(id == parent); simp(); }
                                            have (sid->__rb_parent_color & 1) == 0 by { rewrite(sid->__rb_parent_color == address(id)); arithmetic() using { aligned(id, 8); } }
                                            have (sid->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                                            have sid->__rb_parent_color == address(id) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == 0); rewrite(sid->__rb_parent_color == address(id)); normalize(); }
                                            let sn = fold(rb_at(sid), { model: RbTree::Node(sid, id, Color::Red, slm, srm) }, { left: ls, right: rs });
                                            have rb_parent_is(nt.model, id) == 1 by { rewrite(id == parent); assumption(); }
                                            have rb_parent_is(sn.model, id) == 1 by { rewrite(sn.model == RbTree::Node(sid, id, Color::Red, slm, srm)); unfold(rb_parent_is(RbTree::Node(sid, id, Color::Red, slm, srm), id)); normalize(); }
                                            match pc {
                                                Color::Red => {
                                                    have ctx_rb(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                                    have rb_parent_consistent(plug(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by { rewrite(Color::Red == pc); assumption(); }
                                                    apply(ctx_erase_case2_left_red_exit(above, id, sid, nt.model, slm, srm, um)) using {
                                                        is_rb(nt.model) == 1;
                                                        rb_root_black(nt.model) == 1;
                                                        ctx_rb(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                                        rb_root_black(slm) == 1;
                                                        rb_root_black(srm) == 1;
                                                        rb_parent_consistent(plug(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1;
                                                    }
                                                    have (parent->__rb_parent_color & 1) == 0 by {
                                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Red); unfold(color_bit(Color::Red)); normalize();
                                                    }
                                                    have parent->__rb_parent_color == address(above) by {
                                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 0); normalize();
                                                    }
                                                    mark red_flip;
                                                    have at(red_flip, parent->__rb_parent_color) == address(above) by assumption();
                                                    step(); step(); # Select the red parent and blacken it.
                                                    have parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1;
                                                    have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1); rewrite(at(red_flip, parent->__rb_parent_color) == address(above)); normalize(); }
                                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                    let nc = fold(ctx_at(node, root), { model: Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) }, { sibling: sn, up: u });
                                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))) by { rewrite(nc.model == Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um)); unfold(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model)); normalize(); }
                                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(nc.model, nt.model)));
                                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))); assumption();
                                                    }
                                                    have erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))) by {
                                                        apply(erase_flips_red_all_left_red_step(id, above, sid, slm, srm, um, nt.model)); rewrite(erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, rb_recolor(RbTree::Node(sid, id, Color::Black, slm, srm), Color::Red)))); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, slm, srm), Color::Red)); normalize();
                                                    }
                                                    have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))); rewrite(plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))) == erase_flips_red_all_result(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model));
                                                        rewrite(Color::Red == pc); assumption();
                                                    }
                                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                        rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm))));
                                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)))) == rb_inorder(plug(Context::Left(id, above, Color::Red, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)));
                                                        rewrite(Color::Red == pc); assumption();
                                                    }
                                                    step(); # Break with a balanced whole tree.
                                                },
                                                Color::Black => {
                                                    have Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) by { rewrite(pc == Color::Black); normalize(); }
                                                    have ctx_rb(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                                    have rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                                    apply(ctx_erase_case2_left_black_step(above, id, sid, nt.model, slm, srm, um)) using {
                                                        is_rb(nt.model) == 1;
                                                        rb_root_black(nt.model) == 1;
                                                        ctx_rb(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1;
                                                        rb_root_black(slm) == 1;
                                                        rb_root_black(srm) == 1;
                                                        rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1;
                                                    }
                                                    have (parent->__rb_parent_color & 1) == 1 by {
                                                        rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Black); unfold(color_bit(Color::Black)); normalize();
                                                    }
                                                    have parent->__rb_parent_color == address(above) + 1 by {
                                                        rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 1); normalize();
                                                    }
                                                    have id->__rb_parent_color == address(above) + 1 by assumption();
                                                    have (id->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                                    have erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); assumption(); }
                                                    step(); # The black parent cannot absorb the deficit.
                                                    step(); step(); # Move the deficit node and decode its parent.
                                                    have node == id;
                                                    have parent == above;
                                                    have id->__rb_parent_color == address(above) + (id->__rb_parent_color & 1) by {
                                                        rewrite((id->__rb_parent_color & 1) == color_bit(Color::Black)); unfold(color_bit(Color::Black)); assumption();
                                                    }
                                                    mark parent_fold;
                                                    have at(parent_fold, nt.model) == nt.model by normalize();
                                                    let sub = fold(rb_at(id), { model: RbTree::Node(id, above, Color::Black, nt.model, RbTree::Node(sid, id, Color::Red, slm, srm)) }, { left: nt, right: sn });
                                                    have sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)) by normalize();
                                                    have is_rb(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); assumption(); }
                                                    have rb_root_black(sub.model) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); assumption(); }
                                                    have rb_parent_is(sub.model, parent) == 1 by { rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); rewrite(parent == above); unfold(rb_parent_is(RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)), above)); normalize(); }
                                                    have ctx_rb(u.model, Nat::Succ(black_height(sub.model)), Color::Black) == 1 by { rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(u.model, sub.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(u.model, sub.model))); assumption(); }
                                                    have rb_inorder(plug(u.model, sub.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)));
                                                        rewrite(rb_inorder(plug(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)))) == rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model)))); assumption();
                                                    }
                                                    have erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model)) == erase_flips_red_all_result(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))) by {
                                                        apply(erase_flips_red_all_left_black_step(id, above, sid, slm, srm, um, at(parent_fold, nt.model))); rewrite(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model)) == erase_flips_red_all_result(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), rb_recolor(RbTree::Node(sid, id, Color::Black, slm, srm), Color::Red)))); unfold(rb_recolor(RbTree::Node(sid, id, Color::Black, slm, srm), Color::Red)); normalize();
                                                    }
                                                    have erase_flips_red_all_result(u.model, sub.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                        rewrite(u.model == um); rewrite(sub.model == RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm)));
                                                        rewrite(erase_flips_red_all_result(um, RbTree::Node(id, above, Color::Black, at(parent_fold, nt.model), RbTree::Node(sid, id, Color::Red, slm, srm))) == erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um), at(parent_fold, nt.model))); assumption();
                                                    }

                                                    have ctx_node_is(u.model, parent) == 1 by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                                    have u.model == ctx_reroot(u.model, parent) by { rewrite(u.model == um); rewrite(parent == above); assumption(); }
                                                    have erase_flips_red_all(u.model) == 1 by {
                                                        rewrite(u.model == um);
                                                        have erase_flips_red_all(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um)) == erase_flips_red_all(um) by {
                                                            unfold(erase_flips_red_all(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um))); normalize() using { rb_root_black(slm) == 1; rb_root_black(srm) == 1; }
                                                        }
                                                        rewrite(erase_flips_red_all(um) == erase_flips_red_all(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um)));
                                                        rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Black, slm, srm), um) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um)); rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); assumption();
                                                    }
                                                    if parent == 0 {
                                                        match u.model {
                                                            Context::Top => {
                                                                have is_rb_root(sub.model) == 1 by { apply(is_rb_root_from_parts(sub.model)) using { is_rb(sub.model) == 1; rb_root_black(sub.model) == 1; } assumption(); }
                                                                have plug(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(plug(Context::Top, sub.model)); normalize(); }
                                                                have erase_flips_red_all_result(u.model, sub.model) == sub.model by { rewrite(u.model == Context::Top); unfold(erase_flips_red_all_result(Context::Top, sub.model)); normalize(); }
                                                                have is_rb_root(plug(u.model, sub.model)) == 1 by { rewrite(plug(u.model, sub.model) == sub.model); assumption(); }
                                                                have plug(u.model, sub.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                                    rewrite(plug(u.model, sub.model) == sub.model); rewrite(sub.model == erase_flips_red_all_result(u.model, sub.model)); assumption();
                                                                }
                                                                step(); step(); step(); # Null parent: skip continue and break.
                                                            },
                                                            Context::Left(uid, ugp, uc, usm, uum) => {
                                                                have ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Left(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                                have parent == uid by { apply(ctx_node_is_left_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Left(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                                let { sibling: us, up: uu } = unfold(u);
                                                                contradiction(parent == 0);
                                                            },
                                                            Context::Right(uid, ugp, uc, usm, uum) => {
                                                                have ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1 by { rewrite(Context::Right(uid, ugp, uc, usm, uum) == u.model); assumption(); }
                                                                have parent == uid by { apply(ctx_node_is_right_identity(uid, ugp, uc, usm, uum, parent)) using { ctx_node_is(Context::Right(uid, ugp, uc, usm, uum), parent) == 1; } assumption(); }
                                                                let { sibling: us, up: uu } = unfold(u);
                                                                contradiction(parent == 0);
                                                            },
                                                        }
                                                    } else {
                                                        have u.model != Context::Top by {
                                                            if u.model == Context::Top {
                                                                have ctx_node_is(Context::Top, parent) == 1 by { rewrite(Context::Top == u.model); assumption(); }
                                                                apply(ctx_node_is_top_null(parent)) using { ctx_node_is(Context::Top, parent) == 1; }
                                                                contradiction(parent == 0);
                                                            } else { assumption(); }
                                                        }
                                                        step(); step(); # A live parent continues with the strict child context.
                                                        close_invariants();
                                                    }
                                                },
                                            }

                                        } else {

                                            match sr.model ensuring {
                                                owns rs: rb_at(tmp1);
                                                fact rs.model == srm;
                                            } {
                                                RbTree::Empty => {
                                                    have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                                    unfold(sr);
                                                    step(); # The null child satisfies the black-child guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Empty); normalize(); }
                                                },
                                                RbTree::Node(cid, cp, cc, clm, crm) => {
                                                    have srm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(srm == sr.model); assumption(); }
                                                    have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == srm); assumption(); }
                                                    apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                                    let { left: cl, right: cr } = unfold(sr);
                                                    step(); # The owned black child's tag satisfies the guard.
                                                    let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                                    have rs.model == srm by { rewrite(srm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                                },
                                            }
                                            step(); # Read the sibling's left child.
                                            match sl.model {
                                                RbTree::Empty => {
                                                    have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                                    have rb_root_black(slm) == 1 by { rewrite(slm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                    contradiction(rb_root_black(slm) == 1);
                                                },
                                                RbTree::Node(iid, ip, ic, ilm, irm) => {
                                                    have slm == RbTree::Node(iid, ip, ic, ilm, irm) by { rewrite(slm == sl.model); assumption(); }
                                                    have not(rb_root_black(RbTree::Node(iid, ip, ic, ilm, irm)) == 1) by { rewrite(RbTree::Node(iid, ip, ic, ilm, irm) == slm); assumption(); }
                                                    apply(outer_nonblack_node_color(iid, ip, ic, ilm, irm));
                                                    have rb_parent_is(RbTree::Node(iid, ip, ic, ilm, irm), sid) == 1 by { rewrite(RbTree::Node(iid, ip, ic, ilm, irm) == slm); rewrite(sid == parent->rb_right); assumption(); }
                                                    apply(rb_parent_is_node_parent(iid, ip, ic, ilm, irm, sid));
                                                    have slm == RbTree::Node(iid, sid, Color::Red, ilm, irm) by { rewrite(slm == RbTree::Node(iid, ip, ic, ilm, irm)); rewrite(ip == sid); rewrite(ic == Color::Red); normalize(); }
                                                    have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                                        rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }
                                                    have rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == 1 by {
                                                        rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }
                                                    have rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)));
                                                        rewrite(rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model))); assumption();
                                                    }
                                                    have erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                        rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }
                                                    have rb_inorder(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                        rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                    }

                                                    have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(iid, sid, Color::Red, ilm, irm), srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    have rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(iid, sid, Color::Red, ilm, irm), srm), um), nt.model), 0) == 1 by { rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    apply(ctx_erase_case3_left_exit(above, id, pc, sid, iid, nt.model, srm, ilm, irm, um));

                                                    apply(ctx_rb_left_sibling(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(iid, sid, Color::Red, ilm, irm), srm), um, Nat::Succ(black_height(nt.model)), Color::Black));
                                                    apply(is_rb_node_left(sid, id, Color::Black, RbTree::Node(iid, sid, Color::Red, ilm, irm), srm));
                                                    apply(is_rb_red_node_right_child_is_black(iid, sid, ilm, irm));
                                                    let { right: ir, left: il } = unfold(sl);
                                                    have tmp2 == iid;
                                                    have sibling == sid;
                                                    have (iid->__rb_parent_color & 1) == 0 by { rewrite((iid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); normalize(); }
                                                    mark inner_inputs;
                                                    step(); # The red near child selects case 3.
                                                    step(); # Leave the untaken case-2 body.
                                                    step(); # Read its right child.
                                                    step(); # Move that child under the old sibling.
                                                    step(); # Put the old sibling under the red node.
                                                    step(); # Update the parent's child link.
                                                    have aligned(sid, 8);
                                                    have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                    have parent->rb_left == node;
                                                    have parent->rb_right == iid;
                                                    have iid->rb_right == sid;
                                                    have sid->rb_left == tmp1;
                                                    have sid->rb_right == at(inner_inputs, sid->rb_right);
                                                    have iid->rb_left == at(inner_inputs, iid->rb_left);
                                                    mark first_update;
                                                    match ir.model ensuring {
                                                        owns first_near: rb_at(tmp1);
                                                        fact first_near.model == rb_reparent(irm, sid);
                                                        fact parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                        fact parent->rb_left == node;
                                                        fact parent->rb_right == iid;
                                                        fact iid->rb_right == sid;
                                                        fact sid->rb_left == tmp1;
                                                        fact sid->rb_right == at(inner_inputs, sid->rb_right);
                                                        fact iid->rb_left == at(inner_inputs, iid->rb_left);
                                                    } {
                                                        RbTree::Empty => {
                                                            have irm == RbTree::Empty by { rewrite(irm == ir.model); assumption(); }
                                                            unfold(ir);
                                                            step(); step(); # Select and leave the null grandchild branch.
                                                            let first_near = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                            have first_near.model == rb_reparent(irm, sid) by { rewrite(irm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, sid)); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, crm, clm) => {
                                                            have irm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(irm == ir.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == irm); assumption(); }
                                                            apply(outer_black_node_color(cid, cp, cc, crm, clm));
                                                            let { right: cl, left: cr } = unfold(ir);
                                                            have tmp1 == cid;
                                                            step(); # Enter the nonempty grandchild update.
                                                            step(); # Store its new black parent word.
                                                            have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                            have cid->__rb_parent_color == (address(sid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == cid; sibling == sid; } }
                                                            have cid->__rb_parent_color == address(sid) + 1 by { rewrite(cid->__rb_parent_color == (address(sid) | 1)); arithmetic() using { aligned(sid, 8); } }
                                                            have (cid->__rb_parent_color & 1) == 1 by normalize();
                                                            have cid->__rb_parent_color == address(sid) + (cid->__rb_parent_color & 1) by { normalize() using { cid->__rb_parent_color == address(sid) + 1; (cid->__rb_parent_color & 1) == 1; } }
                                                            have (cid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                            let first_near = fold(rb_at(tmp1), { model: RbTree::Node(cid, sid, Color::Black, crm, clm) }, { right: cl, left: cr });
                                                            have first_near.model == rb_reparent(irm, sid) by { rewrite(irm == RbTree::Node(cid, cp, cc, crm, clm)); rewrite(cc == Color::Black); unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, crm, clm), sid)); normalize(); }
                                                            have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color) by { normalize() using { at(first_update, parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color)); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have parent->rb_left == node by { normalize() using { at(first_update, parent->rb_left == node); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have parent->rb_right == iid by { normalize() using { at(first_update, parent->rb_right == iid); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have iid->rb_right == sid by { normalize() using { at(first_update, iid->rb_right == sid); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have sid->rb_left == tmp1 by { normalize() using { at(first_update, sid->rb_left == tmp1); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have sid->rb_right == at(inner_inputs, sid->rb_right) by { normalize() using { at(first_update, sid->rb_right == at(inner_inputs, sid->rb_right)); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                            have iid->rb_left == at(inner_inputs, iid->rb_left) by { normalize() using { at(first_update, iid->rb_left == at(inner_inputs, iid->rb_left)); tmp1 == cid; sibling == sid; tmp2 == iid; } }
                                                        },
                                                    }
                                                    step(); # The augmentation callback preserves tree fields.
                                                    step(); step(); # Select the new sibling and far child for case 4.
                                                    have tmp1 == sid;
                                                    have sibling == iid;
                                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color)); assumption(); }
                                                    have parent->rb_left == node by assumption();
                                                    have iid->rb_right == sid by assumption();
                                                    mark outer_inputs;
                                                    step(); # Read the near child.
                                                    step(); # Attach the near child to the parent.
                                                    step(); # Attach the parent under the sibling.
                                                    step(); # Blacken the far child.
                                                    have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                    have sid->__rb_parent_color == (address(iid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == sid; sibling == iid; } }
                                                    have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { simp() using { tmp1 == sid; sibling == iid; } }
                                                    have parent->rb_left == node by { simp() using { at(outer_inputs, parent->rb_left) == node; tmp1 == sid; sibling == iid; } }
                                                    have parent->rb_right == tmp2 by { simp() using { tmp1 == sid; sibling == iid; } }
                                                    have sibling->rb_left == parent by assumption();
                                                    have iid->rb_left == parent by { rewrite(iid == sibling); normalize() using { sibling->rb_left == parent; } }
                                                    have sibling->rb_right == tmp1;
                                                    have iid->rb_right == sid by { rewrite(iid == sibling); rewrite(sid == tmp1); normalize() using { sibling->rb_right == tmp1; } }
                                                    have id->rb_left == node by { simp() using { parent->rb_left == node; parent == id; } }
                                                    mark near_update;
                                                    match il.model ensuring {
                                                        owns near: rb_at(tmp2);
                                                        fact near.model == rb_reparent(ilm, parent);
                                                        fact parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                        fact parent->rb_left == node;
                                                        fact parent->rb_right == tmp2;
                                                        fact iid->rb_left == parent;
                                                        fact iid->rb_right == sid;
                                                        fact sid->__rb_parent_color == (address(iid) | 1);
                                                    } {
                                                        RbTree::Empty => {
                                                            have ilm == RbTree::Empty by { rewrite(ilm == il.model); assumption(); }
                                                            unfold(il);
                                                            have tmp2 == 0;
                                                            step(); step(); # Select and complete the empty C arm.
                                                            let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                            have near.model == rb_reparent(ilm, parent) by { rewrite(ilm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                            have sid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, sid->__rb_parent_color == (address(iid) | 1)); sibling == iid; tmp1 == sid; } }
                                                        },
                                                        RbTree::Node(nid, np, nc, nrm, nlm) => {
                                                            have ilm == RbTree::Node(nid, np, nc, nrm, nlm) by { rewrite(ilm == il.model); assumption(); }
                                                            let { right: nl, left: nr } = unfold(il);
                                                            have tmp2 == nid;
                                                            have tmp2 != 0;
                                                            have separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color));
                                                            have separate(memory(iid->rb_left), memory(tmp2->__rb_parent_color)) by { transport(separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)), separate(memory(iid->rb_left), memory(tmp2->__rb_parent_color))) using { separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)); sibling == iid; }; }
                                                            have (tmp2->__rb_parent_color & 1) == color_bit(nc);
                                                            mark near_tag;
                                                            step(); # Select the nonempty near-child parent update.
                                                            step(rb_set_parent(tmp2, parent), {});
                                                            have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                            have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                                rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                                if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                            }
                                                            have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                                rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                                if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                            }
                                                            have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                            let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nrm, nlm) }, { right: nl, left: nr });
                                                            have near.model == rb_reparent(ilm, parent) by { rewrite(ilm == RbTree::Node(nid, np, nc, nrm, nlm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nrm, nlm), parent)); simp(); }
                                                            have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { normalize() using { at(near_update, parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); tmp2 == nid; sibling == iid; tmp1 == sid; } }
                                                            have id->rb_left == node;
                                                            have parent->rb_left == node;
                                                            have parent->rb_right == tmp2 by { normalize() using { at(near_update, parent->rb_right == tmp2); tmp2 == nid; sibling == iid; tmp1 == sid; } }
                                                            have sibling->rb_left == parent by { transport(at(near_update, sibling->rb_left) == parent, sibling->rb_left == parent) using { at(near_update, sibling->rb_left) == parent; separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)); tmp2 == nid; sibling == iid; parent == id; }; }
                                                            have iid->rb_left == parent by { transport(at(near_update, iid->rb_left) == parent, iid->rb_left == parent) using { at(near_update, iid->rb_left) == parent; separate(memory(iid->rb_left), memory(tmp2->__rb_parent_color)); tmp2 == nid; }; }
                                                            have sibling->rb_right == tmp1;
                                                            have iid->rb_right == sid by { rewrite(iid == sibling); rewrite(sid == tmp1); normalize() using { sibling->rb_right == tmp1; } }
                                                            have sid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, sid->__rb_parent_color == (address(iid) | 1)); tmp2 == nid; sibling == iid; tmp1 == sid; } }
                                                        },
                                                    }
                                                    have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by assumption();
                                                    have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                    have u.model == um by assumption();
                                                    apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, pc));
                                                    have parent->rb_left == node by assumption();
                                                    have parent->rb_right == tmp2 by assumption();
                                                    have iid->rb_left == parent by assumption();
                                                    have iid->rb_right == sid by assumption();
                                                    have sid->__rb_parent_color == (address(iid) | 1) by assumption();
                                                    have aligned(iid, 8);
                                                    have sid->__rb_parent_color == address(iid) + 1 by { rewrite(sid->__rb_parent_color == (address(iid) | 1)); arithmetic() using { aligned(iid, 8); } }
                                                    have (sid->__rb_parent_color & 1) == 1 by normalize();
                                                    have sid->__rb_parent_color == address(iid) + (sid->__rb_parent_color & 1) by { normalize() using { sid->__rb_parent_color == address(iid) + 1; (sid->__rb_parent_color & 1) == 1; } }
                                                    have (sid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                    apply(rb_reparent_parent_is(irm, sid));
                                                    let far_tree = fold(rb_at(sid), { model: RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm) }, { right: rs, left: first_near });
                                                    apply(rb_parent_is_node_of(sid, iid, Color::Black, rb_reparent(irm, sid), srm));
                                                    fold(rb_child_links(iid, parent, sid));
                                                    fold(rb_child_links(parent, node, tmp2));
                                                    mark outer_rotation;
                                                    let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: u });
                                                    step(); # The augmentation callback preserves the tree resources.
                                                    unfold(rb_child_links(iid, parent, sid));
                                                    unfold(rb_child_links(parent, node, tmp2));
                                                    have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color);
                                                    have iid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == iid; parent == id; } }
                                                    have iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(iid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                    have iid->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                    have (iid->__rb_parent_color & 1) == color_bit(pc) by {
                                                        rewrite(iid->__rb_parent_color == address(above) + color_bit(pc));
                                                        if color_bit(pc) == 0 { rewrite(color_bit(pc) == 0); arithmetic() using { aligned(above, 8); } } else { apply(color_bit_nonzero_is_one(pc)); rewrite(color_bit(pc) == 1); arithmetic() using { aligned(above, 8); } }
                                                    }
                                                    have iid->__rb_parent_color == address(above) + (iid->__rb_parent_color & 1) by { rewrite((iid->__rb_parent_color & 1) == color_bit(pc)); assumption(); }
                                                    have parent->__rb_parent_color == address(iid) + 1;
                                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(iid) + 1); arithmetic() using { aligned(iid, 8); } }
                                                    have parent->__rb_parent_color == address(iid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have iid->rb_left == parent by assumption();
                                                    have iid->rb_right == sid by assumption();
                                                    let rotated_up = fold(ctx_at(parent, root), { model: Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um) }, { sibling: far_tree, up: u });
                                                    have ctx_node_is(Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um), iid) == 1 by { unfold(ctx_node_is(Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um), iid)); normalize(); }
                                                    apply(ctx_reroot_fixed(Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um), iid));
                                                    have near.model == rb_reparent(ilm, id) by { rewrite(id == parent); assumption(); }
                                                    apply(rb_reparent_parent_is(ilm, id));
                                                    have parent->rb_left == node by assumption();
                                                    have parent->rb_right == tmp2 by assumption();
                                                    let nc = fold(ctx_at(node, root), { model: Context::Left(id, iid, Color::Black, rb_reparent(ilm, id), Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um)) }, { sibling: near, up: rotated_up });
                                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm))) by { rewrite(nc.model == Context::Left(id, iid, Color::Black, rb_reparent(ilm, id), Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um))); unfold(plug(Context::Left(id, iid, Color::Black, rb_reparent(ilm, id), Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um)), nt.model)); unfold(plug(Context::Left(iid, above, pc, RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm), um), RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)))); normalize(); }
                                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm)))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm)))); assumption(); }
                                                    apply(erase_flips_red_all_left_inner_result(id, above, pc, sid, iid, ilm, irm, srm, um, nt.model));
                                                    have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm)))); rewrite(plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm))) == erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(iid, sid, Color::Red, ilm, irm), srm), um), nt.model)); rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm)))); rewrite(rb_inorder(plug(um, RbTree::Node(iid, above, pc, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(ilm, id)), RbTree::Node(sid, iid, Color::Black, rb_reparent(irm, sid), srm)))) == rb_inorder(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, RbTree::Node(iid, sid, Color::Red, ilm, irm), srm), um), nt.model))); rewrite(RbTree::Node(iid, sid, Color::Red, ilm, irm) == slm); assumption(); }
                                                    step(); # Break after both rotations with a balanced whole tree.
                                                },
                                            }
                                        }
                                    } else {
                                        match sr.model {
                                            RbTree::Empty => {
                                                have srm == RbTree::Empty by { rewrite(srm == sr.model); assumption(); }
                                                have rb_root_black(srm) == 1 by { rewrite(srm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                contradiction(rb_root_black(srm) == 1);
                                            },
                                            RbTree::Node(rid, rp, rc, rlm, rrm) => {
                                                have srm == RbTree::Node(rid, rp, rc, rlm, rrm) by { rewrite(srm == sr.model); assumption(); }
                                                have not(rb_root_black(RbTree::Node(rid, rp, rc, rlm, rrm)) == 1) by { rewrite(RbTree::Node(rid, rp, rc, rlm, rrm) == srm); assumption(); }
                                                apply(outer_nonblack_node_color(rid, rp, rc, rlm, rrm));
                                                have rb_parent_is(RbTree::Node(rid, rp, rc, rlm, rrm), sid) == 1 by { rewrite(RbTree::Node(rid, rp, rc, rlm, rrm) == srm); rewrite(sid == parent->rb_right); assumption(); }
                                                apply(rb_parent_is_node_parent(rid, rp, rc, rlm, rrm, sid));
                                                have srm == RbTree::Node(rid, sid, Color::Red, rlm, rrm) by { rewrite(srm == RbTree::Node(rid, rp, rc, rlm, rrm)); rewrite(rp == sid); rewrite(rc == Color::Red); normalize(); }
                                                have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                                    rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }
                                                have rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == 1 by {
                                                    rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }
                                                have rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == 1 by {
                                                    unfold(rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)));
                                                    rewrite(rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model))); assumption();
                                                }
                                                have erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                    rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }
                                                have rb_inorder(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                    rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                                }

                                                have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, RbTree::Node(rid, sid, Color::Red, rlm, rrm)), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(rid, sid, Color::Red, rlm, rrm) == srm); assumption(); }
                                                have rb_parent_consistent(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, RbTree::Node(rid, sid, Color::Red, rlm, rrm)), um), nt.model), 0) == 1 by { rewrite(RbTree::Node(rid, sid, Color::Red, rlm, rrm) == srm); assumption(); }
                                                apply(ctx_erase_case4_left_exit(above, id, pc, sid, rid, nt.model, slm, rlm, rrm, um));
                                                let { left: rl, right: rr } = unfold(sr);
                                                have tmp1 == rid;
                                                have sibling == sid;
                                                have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); normalize(); }
                                                have parent->rb_left == node;
                                                have sibling->rb_right == tmp1;
                                                have sid->rb_right == sibling->rb_right by { normalize() using { sibling == sid; } }
                                                have sid->rb_right == rid by { rewrite(sid->rb_right == sibling->rb_right); rewrite(sibling->rb_right == tmp1); assumption(); }
                                                mark outer_inputs;
                                                step(); # Red far child skips cases 2 and 3.
                                                step(); # Read the near child.
                                                step(); # Attach the near child to the parent.
                                                step(); # Attach the parent under the sibling.
                                                step(); # Blacken the far child.
                                                step(); # Execute the far-child parent/color store.
                                                have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                have rid->__rb_parent_color == (address(sid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == rid; sibling == sid; } }
                                                have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { simp() using { tmp1 == rid; sibling == sid; } }
                                                have parent->rb_left == node by { simp() using { at(outer_inputs, parent->rb_left) == node; tmp1 == rid; sibling == sid; } }
                                                have parent->rb_right == tmp2 by { simp() using { tmp1 == rid; sibling == sid; } }
                                                have sibling->rb_left == parent by assumption();
                                                have sid->rb_left == parent by { rewrite(sid == sibling); normalize() using { sibling->rb_left == parent; } }
                                                have sibling->rb_right == tmp1;
                                                have sid->rb_right == sibling->rb_right by { normalize() using { sibling == sid; } }
                                                have sid->rb_right == rid by { rewrite(sid->rb_right == sibling->rb_right); rewrite(sibling->rb_right == tmp1); assumption(); }
                                                have id->rb_left == node by { simp() using { parent->rb_left == node; parent == id; } }
                                                mark near_update;
                                                match sl.model ensuring {
                                                    owns near: rb_at(tmp2);
                                                    fact near.model == rb_reparent(slm, parent);
                                                    fact parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                    fact parent->rb_left == node;
                                                    fact parent->rb_right == tmp2;
                                                    fact sid->rb_left == parent;
                                                    fact sid->rb_right == rid;
                                                    fact rid->__rb_parent_color == (address(sid) | 1);
                                                } {
                                                    RbTree::Empty => {
                                                        have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                                        unfold(sl);
                                                        have tmp2 == 0;
                                                        step(); step(); # Select and complete the empty C arm.
                                                        let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                        have near.model == rb_reparent(slm, parent) by { rewrite(slm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                        have rid->__rb_parent_color == (address(sid) | 1) by { normalize() using { at(near_update, rid->__rb_parent_color == (address(sid) | 1)); sibling == sid; tmp1 == rid; } }
                                                    },
                                                    RbTree::Node(nid, np, nc, nlm, nrm) => {
                                                        have slm == RbTree::Node(nid, np, nc, nlm, nrm) by { rewrite(slm == sl.model); assumption(); }
                                                        let { left: nl, right: nr } = unfold(sl);
                                                        have tmp2 == nid;
                                                        have tmp2 != 0;
                                                        have separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color));
                                                        have separate(memory(sid->rb_left), memory(tmp2->__rb_parent_color)) by { transport(separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)), separate(memory(sid->rb_left), memory(tmp2->__rb_parent_color))) using { separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)); sibling == sid; }; }
                                                        have (tmp2->__rb_parent_color & 1) == color_bit(nc);
                                                        mark near_tag;
                                                        step(); # Select the nonempty near-child parent update.
                                                        step(rb_set_parent(tmp2, parent), {});
                                                        have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                        have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                            rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                            if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                        }
                                                        have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                            rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                            if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                        }
                                                        have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                        let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nlm, nrm) }, { left: nl, right: nr });
                                                        have near.model == rb_reparent(slm, parent) by { rewrite(slm == RbTree::Node(nid, np, nc, nlm, nrm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nlm, nrm), parent)); simp(); }
                                                        have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { normalize() using { at(near_update, parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                                        have id->rb_left == node;
                                                        have parent->rb_left == node;
                                                        have parent->rb_right == tmp2 by { normalize() using { at(near_update, parent->rb_right == tmp2); tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                                        have sibling->rb_left == parent by { transport(at(near_update, sibling->rb_left) == parent, sibling->rb_left == parent) using { at(near_update, sibling->rb_left) == parent; separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)); tmp2 == nid; sibling == sid; parent == id; }; }
                                                        have sid->rb_left == parent by { transport(at(near_update, sid->rb_left) == parent, sid->rb_left == parent) using { at(near_update, sid->rb_left) == parent; separate(memory(sid->rb_left), memory(tmp2->__rb_parent_color)); tmp2 == nid; }; }
                                                        have sibling->rb_right == tmp1;
                                                        have sid->rb_right == sibling->rb_right by { normalize() using { sibling == sid; } }
                                                        have sid->rb_right == rid by { rewrite(sid->rb_right == sibling->rb_right); rewrite(sibling->rb_right == tmp1); assumption(); }
                                                        have rid->__rb_parent_color == (address(sid) | 1) by { normalize() using { at(near_update, rid->__rb_parent_color == (address(sid) | 1)); tmp2 == nid; sibling == sid; tmp1 == rid; } }
                                                    },
                                                }
                                                have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by assumption();
                                                have parent->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                have u.model == um by assumption();
                                                apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, pc));
                                                have parent->rb_left == node by assumption();
                                                have parent->rb_right == tmp2 by assumption();
                                                have sid->rb_left == parent by assumption();
                                                have sid->rb_right == rid by assumption();
                                                have rid->__rb_parent_color == (address(sid) | 1) by assumption();
                                                have aligned(sid, 8);
                                                have rid->__rb_parent_color == address(sid) + 1 by { rewrite(rid->__rb_parent_color == (address(sid) | 1)); arithmetic() using { aligned(sid, 8); } }
                                                have (rid->__rb_parent_color & 1) == 1 by normalize();
                                                have rid->__rb_parent_color == address(sid) + (rid->__rb_parent_color & 1) by { normalize() using { rid->__rb_parent_color == address(sid) + 1; (rid->__rb_parent_color & 1) == 1; } }
                                                have (rid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                let far_tree = fold(rb_at(rid), { model: RbTree::Node(rid, sid, Color::Black, rlm, rrm) }, { left: rl, right: rr });
                                                apply(rb_parent_is_node_of(rid, sid, Color::Black, rlm, rrm));
                                                fold(rb_child_links(sid, parent, rid));
                                                fold(rb_child_links(parent, node, tmp2));
                                                mark outer_rotation;
                                                let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: u });
                                                step(); # The augmentation callback preserves the tree resources.
                                                unfold(rb_child_links(sid, parent, rid));
                                                unfold(rb_child_links(parent, node, tmp2));
                                                have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color);
                                                have sid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == sid; parent == id; } }
                                                have sid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(sid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                have sid->__rb_parent_color == address(above) + color_bit(pc) by { rewrite(sid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                have (sid->__rb_parent_color & 1) == color_bit(pc) by {
                                                    rewrite(sid->__rb_parent_color == address(above) + color_bit(pc));
                                                    if color_bit(pc) == 0 { rewrite(color_bit(pc) == 0); arithmetic() using { aligned(above, 8); } } else { apply(color_bit_nonzero_is_one(pc)); rewrite(color_bit(pc) == 1); arithmetic() using { aligned(above, 8); } }
                                                }
                                                have sid->__rb_parent_color == address(above) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == color_bit(pc)); assumption(); }
                                                have parent->__rb_parent_color == address(sid) + 1;
                                                have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(sid) + 1); arithmetic() using { aligned(sid, 8); } }
                                                have parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                have sid->rb_left == parent by assumption();
                                                have sid->rb_right == rid by assumption();
                                                let rotated_up = fold(ctx_at(parent, root), { model: Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um) }, { sibling: far_tree, up: u });
                                                have ctx_node_is(Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), sid) == 1 by { unfold(ctx_node_is(Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), sid)); normalize(); }
                                                apply(ctx_reroot_fixed(Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), sid));
                                                have near.model == rb_reparent(slm, id) by { rewrite(id == parent); assumption(); }
                                                apply(rb_reparent_parent_is(slm, id));
                                                have parent->rb_left == node by assumption();
                                                have parent->rb_right == tmp2 by assumption();
                                                let nc = fold(ctx_at(node, root), { model: Context::Left(id, sid, Color::Black, rb_reparent(slm, id), Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um)) }, { sibling: near, up: rotated_up });
                                                have plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm))) by { rewrite(nc.model == Context::Left(id, sid, Color::Black, rb_reparent(slm, id), Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um))); unfold(plug(Context::Left(id, sid, Color::Black, rb_reparent(slm, id), Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um)), nt.model)); unfold(plug(Context::Left(sid, above, pc, RbTree::Node(rid, sid, Color::Black, rlm, rrm), um), RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)))); normalize(); }
                                                have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm)))); assumption(); }
                                                have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm)))); assumption(); }
                                                have erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, RbTree::Node(rid, sid, Color::Red, rlm, rrm)), um), nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm))) by { unfold(erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, RbTree::Node(rid, sid, Color::Red, rlm, rrm)), um), nt.model)); normalize(); }
                                                have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm)))); rewrite(plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm))) == erase_flips_red_all_result(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, RbTree::Node(rid, sid, Color::Red, rlm, rrm)), um), nt.model)); rewrite(RbTree::Node(rid, sid, Color::Red, rlm, rrm) == srm); assumption(); }
                                                have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm)))); rewrite(rb_inorder(plug(um, RbTree::Node(sid, above, pc, RbTree::Node(id, sid, Color::Black, nt.model, rb_reparent(slm, id)), RbTree::Node(rid, sid, Color::Black, rlm, rrm)))) == rb_inorder(plug(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Black, slm, RbTree::Node(rid, sid, Color::Red, rlm, rrm)), um), nt.model))); rewrite(RbTree::Node(rid, sid, Color::Red, rlm, rrm) == srm); assumption(); }
                                                step(); # Break with a balanced context around the unchanged focus.

                                            },
                                        }
                                    }



                                },
                                Color::Red => {

                                    have at(iteration, c.model) == c.model by normalize();
                                    have at(iteration, c.model) == Context::Left(id, above, pc, sm, um) by { rewrite(at(iteration, c.model) == c.model); assumption(); }
                                    let { sibling: s, up: u } = unfold(c);
                                    have aligned(id, 8) by { rewrite(id == parent); assumption(); }
                                    have rb_parent_is(RbTree::Node(sid, sp, sc, slm, srm), id) == 1 by {
                                        rewrite(RbTree::Node(sid, sp, sc, slm, srm) == sm); rewrite(id == parent); assumption();
                                    }
                                    apply(rb_parent_is_node_parent(sid, sp, sc, slm, srm, id));
                                    have s.model == RbTree::Node(sid, id, Color::Red, slm, srm) by {
                                        rewrite(s.model == sm); rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm));
                                        rewrite(sp == id); rewrite(sc == Color::Red); normalize();
                                    }
                                    have sm == RbTree::Node(sid, id, Color::Red, slm, srm) by {
                                        rewrite(sm == RbTree::Node(sid, sp, sc, slm, srm)); rewrite(sp == id); rewrite(sc == Color::Red); normalize();
                                    }
                                    have at(iteration, c.model) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Red, slm, srm), um) by {
                                        rewrite(at(iteration, c.model) == Context::Left(id, above, pc, sm, um)); rewrite(sm == RbTree::Node(sid, id, Color::Red, slm, srm)); normalize();
                                    }
                                    let { left: sl, right: sr } = unfold(s);
                                    step(); # Read the right sibling.
                                    mark focus_split;
                                    match t.model ensuring {
                                        owns nt: rb_at(node);
                                        fact nt.model == at(focus_split, t.model);
                                    } {
                                        RbTree::Empty => {
                                            have at(focus_split, t.model) == t.model by normalize();
                                            have at(focus_split, t.model) == RbTree::Empty by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            unfold(t);
                                            step(); # The right sibling differs from the null focus.
                                            let nt = fold(rb_at(node), { model: RbTree::Empty });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Empty); rewrite(at(focus_split, t.model) == RbTree::Empty); normalize(); }
                                        },
                                        RbTree::Node(tid, tp, tc, tlm, trm) => {
                                            have at(focus_split, t.model) == t.model by normalize();
                                            have at(focus_split, t.model) == RbTree::Node(tid, tp, tc, tlm, trm) by { rewrite(at(focus_split, t.model) == t.model); assumption(); }
                                            let { left: tl, right: tr } = unfold(t);
                                            step(); # Separate owned roots distinguish the sibling and focus.
                                            let nt = fold(rb_at(node), { model: RbTree::Node(tid, tp, tc, tlm, trm) }, { left: tl, right: tr });
                                            have nt.model == at(focus_split, t.model) by { rewrite(nt.model == RbTree::Node(tid, tp, tc, tlm, trm)); rewrite(at(focus_split, t.model) == RbTree::Node(tid, tp, tc, tlm, trm)); normalize(); }
                                        },
                                    }
                                    have is_rb(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_root_black(nt.model) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    have rb_parent_is(nt.model, parent) == 1 by { rewrite(nt.model == at(focus_split, t.model)); assumption(); }

                                    have ctx_rb(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Red, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Red, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption(); }
                                    apply(ctx_erase_case1_left_parent_black(above, id, pc, sid, slm, srm, um, Nat::Succ(black_height(nt.model))));
                                    have Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) == at(iteration, c.model) by { rewrite(at(iteration, c.model) == Context::Left(id, above, pc, RbTree::Node(sid, id, Color::Red, slm, srm), um)); rewrite(pc == Color::Black); normalize(); }
                                    have ctx_rb(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by {
                                        rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    have rb_tree_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model)) == 1 by {
                                        rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    have rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model), 0) == 1 by {
                                        unfold(rb_tree_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model)));
                                        rewrite(rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model), 0) == rb_tree_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model))); assumption();
                                    }
                                    have erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                        rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    have rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um), nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                        rewrite(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um) == at(iteration, c.model)); rewrite(nt.model == at(focus_split, t.model)); assumption();
                                    }
                                    match sl.model {
                                        RbTree::Empty => {
                                            have slm == RbTree::Empty by { rewrite(slm == sl.model); assumption(); }
                                            have erase_flips_red_all(at(iteration, c.model)) == 0 by { rewrite(at(iteration, c.model) == Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um)); rewrite(slm == RbTree::Empty); unfold(erase_flips_red_all(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Empty, srm), um))); normalize(); }
                                            have not(erase_flips_red_all(at(iteration, c.model)) == 1) by { rewrite(erase_flips_red_all(at(iteration, c.model)) == 0); normalize(); }
                                            contradiction(erase_flips_red_all(at(iteration, c.model)) == 1);
                                        },
                                        RbTree::Node(zid, zp, zc, zlm, zrm) => {
                                            have slm == RbTree::Node(zid, zp, zc, zlm, zrm) by { rewrite(slm == sl.model); assumption(); }
                                            have zc == Color::Black by {
                                                if zc == Color::Black { assumption(); } else {
                                                    have erase_flips_red_all(at(iteration, c.model)) == 0 by { rewrite(at(iteration, c.model) == Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, slm, srm), um)); rewrite(slm == RbTree::Node(zid, zp, zc, zlm, zrm)); unfold(erase_flips_red_all(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, zp, zc, zlm, zrm), srm), um))); normalize() using { not(zc == Color::Black); } }
                                                    have not(erase_flips_red_all(at(iteration, c.model)) == 1) by { rewrite(erase_flips_red_all(at(iteration, c.model)) == 0); normalize(); }
                                                    contradiction(erase_flips_red_all(at(iteration, c.model)) == 1);
                                                }
                                            }

                                            have rb_parent_is(RbTree::Node(zid, zp, zc, zlm, zrm), sid) == 1 by { rewrite(RbTree::Node(zid, zp, zc, zlm, zrm) == slm); rewrite(sid == parent->rb_right); assumption(); }
                                            apply(rb_parent_is_node_parent(zid, zp, zc, zlm, zrm, sid));
                                            have slm == RbTree::Node(zid, sid, Color::Black, zlm, zrm) by { rewrite(slm == RbTree::Node(zid, zp, zc, zlm, zrm)); rewrite(zp == sid); rewrite(zc == Color::Black); normalize(); }
                                            have ctx_rb(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                            have rb_parent_consistent(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), nt.model), 0) == 1 by { rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                            apply(ctx_erase_case1_left_step(above, id, sid, nt.model, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm, um));
                                            have rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id) == RbTree::Node(zid, id, Color::Black, zlm, zrm) by { unfold(rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); normalize(); }
                                            have ctx_rb(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(zid, id, Color::Black, zlm, zrm) == rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); assumption(); }
                                            have rb_parent_consistent(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model), 0) == 1 by { rewrite(RbTree::Node(zid, id, Color::Black, zlm, zrm) == rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); assumption(); }
                                            have rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), nt.model)) by { rewrite(RbTree::Node(zid, id, Color::Black, zlm, zrm) == rb_reparent(RbTree::Node(zid, sid, Color::Black, zlm, zrm), id)); assumption(); }
                                            # Case 2 is justified below, after selecting black near-node children.
                                            let { right: zr, left: zl } = unfold(sl);
                                            have sibling == sid;
                                            have parent->rb_right == sid;
                                            have parent->rb_right->rb_left == zid;
                                            have sid->rb_left == parent->rb_right->rb_left by { normalize() using { parent->rb_right == sid; } }
                                            have sid->rb_left == zid by { rewrite(sid->rb_left == parent->rb_right->rb_left); assumption(); }
                                            have aligned(sid, 8);
                                            have aligned(zid, 8);
                                            have (sid->__rb_parent_color & 1) == 0 by { rewrite((sid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                            have (parent->__rb_parent_color & 1) == 1 by { rewrite((parent->__rb_parent_color & 1) == color_bit(pc)); rewrite(pc == Color::Black); unfold(color_bit(Color::Black)); normalize(); }
                                            have parent->__rb_parent_color == address(above) + 1 by { rewrite(parent->__rb_parent_color == address(above) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == 1); normalize(); }
                                            have parent->__rb_parent_color == address(above) + color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                            have u.model == um by assumption();
                                            apply(ctx_parent_word_from_color(u.model, above, parent->__rb_parent_color, Color::Black));
                                            have sid->rb_right == parent->rb_right->rb_right by { normalize() using { parent->rb_right == sid; } }
                                            let far_link = fold(rb_saved_link(&sid->rb_right), { model: RbSavedLink::Link(parent->rb_right->rb_right) });
                                            mark red_inputs;
                                            step(); # Enter case 1 for the red sibling.
                                            step(); # Read its near child.
                                            step(); # Attach the near child under the parent.
                                            step(); # Attach the parent under the old sibling.
                                            step(); # Set the near child's black parent word.
                                            have tmp1 == zid;
                                            have tmp1->__rb_parent_color == (address(parent) | 1) by assumption();
                                            have zid->__rb_parent_color == (address(id) | 1) by { simp() using { tmp1->__rb_parent_color == (address(parent) | 1); tmp1 == zid; parent == id; } }
                                            have zid->__rb_parent_color == address(id) + 1 by { rewrite(zid->__rb_parent_color == (address(id) | 1)); arithmetic() using { aligned(id, 8); } }
                                            have (zid->__rb_parent_color & 1) == 1 by normalize();
                                            have (zid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                            have zid->__rb_parent_color == address(id) + (zid->__rb_parent_color & 1) by { normalize() using { zid->__rb_parent_color == address(id) + 1; (zid->__rb_parent_color & 1) == 1; } }
                                            let ns = fold(rb_at(zid), { model: RbTree::Node(zid, id, Color::Black, zlm, zrm) }, { right: zr, left: zl });
                                            have parent->rb_right == zid;
                                            have parent->rb_left == node;
                                            have sid->rb_left == parent;
                                            fold(rb_written_left_link(sid, parent));
                                            fold(rb_child_links(parent, node, zid));
                                            mark red_rotation;
                                            let { after: u } = step(__rb_rotate_set_parents(parent, sibling, root, 0), { c: u });
                                            step(); # The callback preserves all tree resources.
                                            unfold(far_link);
                                            unfold(rb_written_left_link(sid, parent));
                                            unfold(rb_child_links(parent, node, zid));
                                            have sibling->__rb_parent_color == at(red_rotation, parent->__rb_parent_color);
                                            have sid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == sid; parent == id; } }
                                            have sid->__rb_parent_color == at(red_rotation, parent->__rb_parent_color) by { rewrite(sid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                            have sid->__rb_parent_color == address(above) + 1 by { rewrite(sid->__rb_parent_color == at(red_rotation, parent->__rb_parent_color)); assumption(); }
                                            have (sid->__rb_parent_color & 1) == 1 by { rewrite(sid->__rb_parent_color == address(above) + 1); arithmetic() using { aligned(above, 8); } }
                                            have (sid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                            have sid->__rb_parent_color == address(above) + (sid->__rb_parent_color & 1) by { rewrite((sid->__rb_parent_color & 1) == 1); assumption(); }
                                            have parent->__rb_parent_color == address(sibling);
                                            have parent->__rb_parent_color == address(sid) by { rewrite(sid == sibling); normalize() using { parent->__rb_parent_color == address(sibling); } }
                                            have (parent->__rb_parent_color & 1) == 0 by { rewrite(parent->__rb_parent_color == address(sid)); arithmetic() using { aligned(sid, 8); } }
                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                                            have parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 0); assumption(); }
                                            have sid->rb_left == parent by assumption();
                                            let red_up = fold(ctx_at(parent, root), { model: Context::Left(sid, above, Color::Black, srm, um) }, { sibling: sr, up: u });
                                            have ctx_node_is(Context::Left(sid, above, Color::Black, srm, um), sid) == 1 by { unfold(ctx_node_is(Context::Left(sid, above, Color::Black, srm, um), sid)); normalize(); }
                                            apply(ctx_reroot_fixed(Context::Left(sid, above, Color::Black, srm, um), sid));
                                            step(); # The near node becomes the new sibling.
                                            have sibling == zid by { simp(); }
                                            mark near_children;
                                            let { right: nright, left: nleft } = unfold(ns);
                                            step(); # Read the new sibling's far child.
                                            if rb_root_black(zrm) == 1 {
                                                if rb_root_black(zlm) == 1 {
                                                    apply(ctx_erase_case2_left_red_exit(sid, id, zid, nt.model, zlm, zrm, Context::Left(sid, above, Color::Black, srm, um)));
                                                    fold(rb_red_parent_tag(parent, sid));
                                                    match nright.model ensuring {
                                                        owns rs: rb_at(tmp1);
                                                        fact rs.model == zrm;
                                                    } {
                                                        RbTree::Empty => {
                                                            have zrm == RbTree::Empty by { rewrite(zrm == nright.model); assumption(); }
                                                            unfold(nright);
                                                            step(); # The null child satisfies the black-child guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                            have rs.model == zrm by { rewrite(zrm == RbTree::Empty); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, clm, crm) => {
                                                            have zrm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(zrm == nright.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == zrm); assumption(); }
                                                            apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                                            let { left: cl, right: cr } = unfold(nright);
                                                            step(); # The owned black child's tag satisfies the guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                                            have rs.model == zrm by { rewrite(zrm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                                        },
                                                    }
                                                    step(); # Read the sibling's left child.
                                                    match nleft.model ensuring {
                                                        owns ls: rb_at(tmp2);
                                                        fact ls.model == zlm;
                                                    } {
                                                        RbTree::Empty => {
                                                            have zlm == RbTree::Empty by { rewrite(zlm == nleft.model); assumption(); }
                                                            unfold(nleft);
                                                            step(); # The null child satisfies the black-child guard.
                                                            let ls = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                            have ls.model == zlm by { rewrite(zlm == RbTree::Empty); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, clm, crm) => {
                                                            have zlm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(zlm == nleft.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == zlm); assumption(); }
                                                            apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                                            let { left: cl, right: cr } = unfold(nleft);
                                                            step(); # The owned black child's tag satisfies the guard.
                                                            let ls = fold(rb_at(tmp2), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                                            have ls.model == zlm by { rewrite(zlm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                                        },
                                                    }
                                                    step(); # Recolor the sibling red, preserving its parent.
                                                    have zid->__rb_parent_color == address(id) by { rewrite(id == parent); simp(); }
                                                    have (zid->__rb_parent_color & 1) == 0 by { rewrite(zid->__rb_parent_color == address(id)); arithmetic() using { aligned(id, 8); } }
                                                    have (zid->__rb_parent_color & 1) == color_bit(Color::Red) by { unfold(color_bit(Color::Red)); assumption(); }
                                                    have zid->__rb_parent_color == address(id) + (zid->__rb_parent_color & 1) by { rewrite((zid->__rb_parent_color & 1) == 0); rewrite(zid->__rb_parent_color == address(id)); normalize(); }
                                                    let sn = fold(rb_at(zid), { model: RbTree::Node(zid, id, Color::Red, zlm, zrm) }, { left: ls, right: rs });
                                                    have rb_parent_is(nt.model, id) == 1 by { rewrite(id == parent); assumption(); }
                                                    have rb_parent_is(sn.model, id) == 1 by { rewrite(sn.model == RbTree::Node(zid, id, Color::Red, zlm, zrm)); unfold(rb_parent_is(RbTree::Node(zid, id, Color::Red, zlm, zrm), id)); normalize(); }
                                                    unfold(rb_red_parent_tag(parent, sid));
                                                    have parent->__rb_parent_color == address(sid) by { assumption(); }
                                                    have (parent->__rb_parent_color & 1) == 0 by { rewrite(parent->__rb_parent_color == address(sid)); arithmetic() using { aligned(sid, 8); } }
                                                    mark red_flip;
                                                    have at(red_flip, parent->__rb_parent_color) == address(sid) by { assumption(); }
                                                    step(); step(); # Select the red parent and blacken it.
                                                    have parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1 by { simp(); }
                                                    have parent->__rb_parent_color == address(sid) + 1 by { rewrite(parent->__rb_parent_color == at(red_flip, parent->__rb_parent_color) + 1); rewrite(at(red_flip, parent->__rb_parent_color) == address(sid)); normalize(); }
                                                    have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(sid) + 1); arithmetic() using { aligned(sid, 8); } }
                                                    have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                    have parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                    let nc = fold(ctx_at(node, root), { model: Context::Left(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)) }, { sibling: sn, up: red_up });
                                                    have plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm))) by { rewrite(nc.model == Context::Left(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um))); unfold(plug(Context::Left(id, sid, Color::Black, RbTree::Node(zid, id, Color::Red, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model)); normalize(); }
                                                    have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)))); assumption(); }
                                                    have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by {
                                                        unfold(rb_tree_parent_consistent(plug(nc.model, nt.model)));
                                                        rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)))); assumption();
                                                    }
                                                    have plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm))) == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)), srm)) by { unfold(plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)))); normalize(); }
                                                    have plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)), srm)) by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)))); assumption(); }
                                                    apply(erase_flips_red_all_left_red_result(id, above, sid, zid, srm, zlm, zrm, um, nt.model));
                                                    have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)), srm))); rewrite(plug(um, RbTree::Node(sid, above, Color::Black, RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)), srm)) == erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), nt.model)); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                    have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)))); rewrite(rb_inorder(plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(id, sid, Color::Black, nt.model, RbTree::Node(zid, id, Color::Red, zlm, zrm)))) == rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model))); rewrite(rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), nt.model))); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                    step(); # The red-parent color flip completes the repair.

                                                } else {

                                                    match nright.model ensuring {
                                                        owns rs: rb_at(tmp1);
                                                        fact rs.model == zrm;
                                                    } {
                                                        RbTree::Empty => {
                                                            have zrm == RbTree::Empty by { rewrite(zrm == nright.model); assumption(); }
                                                            unfold(nright);
                                                            step(); # The null child satisfies the black-child guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                            have rs.model == zrm by { rewrite(zrm == RbTree::Empty); normalize(); }
                                                        },
                                                        RbTree::Node(cid, cp, cc, clm, crm) => {
                                                            have zrm == RbTree::Node(cid, cp, cc, clm, crm) by { rewrite(zrm == nright.model); assumption(); }
                                                            have rb_root_black(RbTree::Node(cid, cp, cc, clm, crm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, clm, crm) == zrm); assumption(); }
                                                            apply(rb_root_black_node_color_bit(cid, cp, cc, clm, crm));
                                                            let { left: cl, right: cr } = unfold(nright);
                                                            step(); # The owned black child's tag satisfies the guard.
                                                            let rs = fold(rb_at(tmp1), { model: RbTree::Node(cid, cp, cc, clm, crm) }, { left: cl, right: cr });
                                                            have rs.model == zrm by { rewrite(zrm == RbTree::Node(cid, cp, cc, clm, crm)); normalize(); }
                                                        },
                                                    }
                                                    step(); # Read the sibling's left child.
                                                    match nleft.model {
                                                        RbTree::Empty => {
                                                            have zlm == RbTree::Empty by { rewrite(zlm == nleft.model); assumption(); }
                                                            have rb_root_black(zlm) == 1 by { rewrite(zlm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                            contradiction(rb_root_black(zlm) == 1);
                                                        },
                                                        RbTree::Node(iid, ip, ic, irm, ilm) => {
                                                            have zlm == RbTree::Node(iid, ip, ic, irm, ilm) by { rewrite(zlm == nleft.model); assumption(); }
                                                            have not(rb_root_black(RbTree::Node(iid, ip, ic, irm, ilm)) == 1) by { rewrite(RbTree::Node(iid, ip, ic, irm, ilm) == zlm); assumption(); }
                                                            apply(outer_nonblack_node_color(iid, ip, ic, irm, ilm));
                                                            have rb_parent_is(RbTree::Node(iid, ip, ic, irm, ilm), zid) == 1 by { rewrite(RbTree::Node(iid, ip, ic, irm, ilm) == zlm); rewrite(zid == parent->rb_right); assumption(); }
                                                            apply(rb_parent_is_node_parent(iid, ip, ic, irm, ilm, zid));
                                                            have zlm == RbTree::Node(iid, zid, Color::Red, irm, ilm) by { rewrite(zlm == RbTree::Node(iid, ip, ic, irm, ilm)); rewrite(ip == zid); rewrite(ic == Color::Red); normalize(); }
                                                            have ctx_rb(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), Context::Left(sid, above, Color::Black, srm, um)), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(iid, zid, Color::Red, irm, ilm) == zlm); assumption(); }
                                                            have rb_parent_consistent(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model), 0) == 1 by { rewrite(RbTree::Node(iid, zid, Color::Red, irm, ilm) == zlm); assumption(); }
                                                            apply(ctx_erase_case3_left_exit(sid, id, Color::Red, zid, iid, nt.model, zrm, irm, ilm, Context::Left(sid, above, Color::Black, srm, um)));

                                                            apply(ctx_rb_left_sibling(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), Context::Left(sid, above, Color::Black, srm, um), Nat::Succ(black_height(nt.model)), Color::Black));
                                                            apply(is_rb_node_left(zid, id, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm));
                                                            apply(is_rb_red_node_right_child_is_black(iid, zid, irm, ilm));
                                                            let { right: il, left: ir } = unfold(nleft);
                                                            have tmp2 == iid;
                                                            have sibling == zid;
                                                            have (iid->__rb_parent_color & 1) == 0 by { rewrite((iid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Red)); normalize(); }
                                                            mark inner_inputs;
                                                            step(); # The red near child selects case 3.
                                                            step(); # Leave the untaken case-2 body.
                                                            step(); # Read its right child.
                                                            step(); # Move that child under the old sibling.
                                                            have zid->rb_left == tmp1;
                                                            mark sibling_link_written;
                                                            step(); # Put the old sibling under the red node.
                                                            step(); # Update the parent's child link.
                                                            have aligned(zid, 8);
                                                            have separate(memory(parent->__rb_parent_color), memory(tmp2->rb_right));
                                                            have separate(memory(parent->__rb_parent_color), memory(sibling->rb_left));
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { transport(at(inner_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red), parent->__rb_parent_color == address(sid) + color_bit(Color::Red)) using { at(inner_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red); separate(memory(parent->__rb_parent_color), memory(tmp2->rb_right)); separate(memory(parent->__rb_parent_color), memory(sibling->rb_left)); tmp2 == iid; sibling == zid; parent == id; }; }
                                                            have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                            have parent->rb_left == node;
                                                            have parent->rb_right == iid;
                                                            have iid->rb_right == zid;
                                                            have zid->rb_left == tmp1;
                                                            have zid->rb_right == at(inner_inputs, zid->rb_right);
                                                            have iid->rb_left == at(inner_inputs, iid->rb_left);
                                                            mark first_update;
                                                            match il.model ensuring {
                                                                owns first_near: rb_at(tmp1);
                                                                fact first_near.model == rb_reparent(ilm, zid);
                                                                fact parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                                fact parent->rb_left == node;
                                                                fact parent->rb_right == iid;
                                                                fact iid->rb_right == zid;
                                                                fact zid->rb_left == tmp1;
                                                                fact zid->rb_right == at(inner_inputs, zid->rb_right);
                                                                fact iid->rb_left == at(inner_inputs, iid->rb_left);
                                                            } {
                                                                RbTree::Empty => {
                                                                    have ilm == RbTree::Empty by { rewrite(ilm == il.model); assumption(); }
                                                                    unfold(il);
                                                                    step(); step(); # Select and leave the null grandchild branch.
                                                                    let first_near = fold(rb_at(tmp1), { model: RbTree::Empty });
                                                                    have first_near.model == rb_reparent(ilm, zid) by { rewrite(ilm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, zid)); normalize(); }
                                                                },
                                                                RbTree::Node(cid, cp, cc, crm, clm) => {
                                                                    have ilm == RbTree::Node(cid, cp, cc, crm, clm) by { rewrite(ilm == il.model); assumption(); }
                                                                    have rb_root_black(RbTree::Node(cid, cp, cc, crm, clm)) == 1 by { rewrite(RbTree::Node(cid, cp, cc, crm, clm) == ilm); assumption(); }
                                                                    apply(outer_black_node_color(cid, cp, cc, crm, clm));
                                                                    let { right: cl, left: cr } = unfold(il);
                                                                    have tmp1 == cid;
                                                                    have separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)) by assumption();
                                                                    step(); # Enter the nonempty grandchild update.
                                                                    step(); # Store its new black parent word.
                                                                    have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                                    have cid->__rb_parent_color == (address(zid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == cid; sibling == zid; } }
                                                                    have cid->__rb_parent_color == address(zid) + 1 by { rewrite(cid->__rb_parent_color == (address(zid) | 1)); arithmetic() using { aligned(zid, 8); } }
                                                                    have (cid->__rb_parent_color & 1) == 1 by normalize();
                                                                    have cid->__rb_parent_color == address(zid) + (cid->__rb_parent_color & 1) by { normalize() using { cid->__rb_parent_color == address(zid) + 1; (cid->__rb_parent_color & 1) == 1; } }
                                                                    have (cid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                                    let first_near = fold(rb_at(tmp1), { model: RbTree::Node(cid, zid, Color::Black, crm, clm) }, { right: cl, left: cr });
                                                                    have first_near.model == rb_reparent(ilm, zid) by { rewrite(ilm == RbTree::Node(cid, cp, cc, crm, clm)); rewrite(cc == Color::Black); unfold(rb_reparent(RbTree::Node(cid, cp, Color::Black, crm, clm), zid)); normalize(); }
                                                                    have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { transport(at(first_update, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red), parent->__rb_parent_color == address(sid) + color_bit(Color::Red)) using { at(first_update, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red); separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)); tmp1 == cid; }; }
                                                                    have parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color);
                                                                    have parent->rb_left == node by { normalize() using { at(first_update, parent->rb_left == node); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have parent->rb_right == iid by { normalize() using { at(first_update, parent->rb_right == iid); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have iid->rb_right == zid by { normalize() using { at(first_update, iid->rb_right == zid); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have zid->rb_left == tmp1 by { normalize() using { at(first_update, zid->rb_left == tmp1); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have zid->rb_right == at(inner_inputs, zid->rb_right) by { normalize() using { at(first_update, zid->rb_right == at(inner_inputs, zid->rb_right)); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                    have iid->rb_left == at(inner_inputs, iid->rb_left) by { normalize() using { at(first_update, iid->rb_left == at(inner_inputs, iid->rb_left)); tmp1 == cid; sibling == zid; tmp2 == iid; } }
                                                                },
                                                            }
                                                            step(); # The augmentation callback preserves tree fields.
                                                            step(); step(); # Select the new sibling and far child for case 4.
                                                            have tmp1 == zid;
                                                            have sibling == iid;
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == at(inner_inputs, parent->__rb_parent_color)); assumption(); }
                                                            have parent->rb_left == node by assumption();
                                                            have iid->rb_right == zid by assumption();
                                                            mark outer_inputs;
                                                            have separate(memory(parent->__rb_parent_color), memory(sibling->rb_left)) by assumption();
                                                            have separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)) by assumption();
                                                            step(); # Read the near child.
                                                            step(); # Attach the near child to the parent.
                                                            step(); # Attach the parent under the sibling.
                                                            step(); # Blacken the far child.
                                                            have tmp1->__rb_parent_color == (address(sibling) | 1) by assumption();
                                                            have zid->__rb_parent_color == (address(iid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == zid; sibling == iid; } }
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { transport(at(outer_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red), parent->__rb_parent_color == address(sid) + color_bit(Color::Red)) using { at(outer_inputs, parent->__rb_parent_color) == address(sid) + color_bit(Color::Red); separate(memory(parent->__rb_parent_color), memory(sibling->rb_left)); separate(memory(parent->__rb_parent_color), memory(tmp1->__rb_parent_color)); tmp1 == zid; sibling == iid; }; }
                                                            have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                            have parent->rb_left == node by { simp() using { at(outer_inputs, parent->rb_left) == node; tmp1 == zid; sibling == iid; } }
                                                            have parent->rb_right == tmp2 by { simp() using { tmp1 == zid; sibling == iid; } }
                                                            have sibling->rb_left == parent by assumption();
                                                            have iid->rb_left == parent by { rewrite(iid == sibling); normalize() using { sibling->rb_left == parent; } }
                                                            have sibling->rb_right == tmp1;
                                                            have iid->rb_right == zid by { rewrite(iid == sibling); rewrite(zid == tmp1); normalize() using { sibling->rb_right == tmp1; } }
                                                            have id->rb_left == node by { simp() using { parent->rb_left == node; parent == id; } }
                                                            mark near_update;
                                                            match ir.model ensuring {
                                                                owns near: rb_at(tmp2);
                                                                fact near.model == rb_reparent(irm, parent);
                                                                fact parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color);
                                                                fact parent->rb_left == node;
                                                                fact parent->rb_right == tmp2;
                                                                fact iid->rb_left == parent;
                                                                fact iid->rb_right == zid;
                                                                fact zid->__rb_parent_color == (address(iid) | 1);
                                                            } {
                                                                RbTree::Empty => {
                                                                    have irm == RbTree::Empty by { rewrite(irm == ir.model); assumption(); }
                                                                    unfold(ir);
                                                                    have tmp2 == 0;
                                                                    step(); step(); # Select and complete the empty C arm.
                                                                    let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                                    have near.model == rb_reparent(irm, parent) by { rewrite(irm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                                    have zid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, zid->__rb_parent_color == (address(iid) | 1)); sibling == iid; tmp1 == zid; } }
                                                                },
                                                                RbTree::Node(nid, np, nc, nrm, nlm) => {
                                                                    have irm == RbTree::Node(nid, np, nc, nrm, nlm) by { rewrite(irm == ir.model); assumption(); }
                                                                    let { right: nl, left: nr } = unfold(ir);
                                                                    have tmp2 == nid;
                                                                    have tmp2 != 0;
                                                                    have separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color));
                                                                    have separate(memory(iid->rb_left), memory(tmp2->__rb_parent_color)) by { transport(separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)), separate(memory(iid->rb_left), memory(tmp2->__rb_parent_color))) using { separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)); sibling == iid; }; }
                                                                    have (tmp2->__rb_parent_color & 1) == color_bit(nc);
                                                                    mark near_tag;
                                                                    step(); # Select the nonempty near-child parent update.
                                                                    step(rb_set_parent(tmp2, parent), {});
                                                                    have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                                    have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                                        rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                                        if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                    }
                                                                    have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                                        rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                                        if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                    }
                                                                    have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                                    let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nrm, nlm) }, { right: nl, left: nr });
                                                                    have near.model == rb_reparent(irm, parent) by { rewrite(irm == RbTree::Node(nid, np, nc, nrm, nlm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nrm, nlm), parent)); simp(); }
                                                                    have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { normalize() using { at(near_update, parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); tmp2 == nid; sibling == iid; tmp1 == zid; } }
                                                                    have id->rb_left == node;
                                                                    have parent->rb_left == node;
                                                                    have parent->rb_right == tmp2 by { normalize() using { at(near_update, parent->rb_right == tmp2); tmp2 == nid; sibling == iid; tmp1 == zid; } }
                                                                    have sibling->rb_left == parent by { transport(at(near_update, sibling->rb_left) == parent, sibling->rb_left == parent) using { at(near_update, sibling->rb_left) == parent; separate(memory(sibling->rb_left), memory(tmp2->__rb_parent_color)); tmp2 == nid; sibling == iid; parent == id; }; }
                                                                    have iid->rb_left == parent by { transport(at(near_update, iid->rb_left) == parent, iid->rb_left == parent) using { at(near_update, iid->rb_left) == parent; separate(memory(iid->rb_left), memory(tmp2->__rb_parent_color)); tmp2 == nid; }; }
                                                                    have sibling->rb_right == tmp1;
                                                                    have iid->rb_right == zid by { rewrite(iid == sibling); rewrite(zid == tmp1); normalize() using { sibling->rb_right == tmp1; } }
                                                                    have zid->__rb_parent_color == (address(iid) | 1) by { normalize() using { at(near_update, zid->__rb_parent_color == (address(iid) | 1)); tmp2 == nid; sibling == iid; tmp1 == zid; } }
                                                                },
                                                            }
                                                            have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by assumption();
                                                            have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                            have red_up.model == Context::Left(sid, above, Color::Black, srm, um) by assumption();
                                                            apply(ctx_parent_word_from_color(red_up.model, sid, parent->__rb_parent_color, Color::Red));
                                                            have parent->rb_left == node by assumption();
                                                            have parent->rb_right == tmp2 by assumption();
                                                            have iid->rb_left == parent by assumption();
                                                            have iid->rb_right == zid by assumption();
                                                            have zid->__rb_parent_color == (address(iid) | 1) by assumption();
                                                            have aligned(iid, 8);
                                                            have zid->__rb_parent_color == address(iid) + 1 by { rewrite(zid->__rb_parent_color == (address(iid) | 1)); arithmetic() using { aligned(iid, 8); } }
                                                            have (zid->__rb_parent_color & 1) == 1 by normalize();
                                                            have zid->__rb_parent_color == address(iid) + (zid->__rb_parent_color & 1) by { normalize() using { zid->__rb_parent_color == address(iid) + 1; (zid->__rb_parent_color & 1) == 1; } }
                                                            have (zid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                            apply(rb_reparent_parent_is(ilm, zid));
                                                            have zid->rb_left == at(first_update, tmp1) by { normalize() using { at(first_update, zid->rb_left == tmp1); sibling == iid; tmp1 == zid; }; }
                                                            let far_tree = fold(rb_at(zid), { model: RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm) }, { right: rs, left: first_near });
                                                            apply(rb_parent_is_node_of(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm));
                                                            fold(rb_child_links(iid, parent, zid));
                                                            fold(rb_child_links(parent, node, tmp2));
                                                            mark outer_rotation;
                                                            let { after: red_up } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: red_up });
                                                            step(); # The augmentation callback preserves the tree resources.
                                                            unfold(rb_child_links(iid, parent, zid));
                                                            unfold(rb_child_links(parent, node, tmp2));
                                                            have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color);
                                                            have iid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == iid; parent == id; } }
                                                            have iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(iid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                            have iid->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(iid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                            have (iid->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                                rewrite(iid->__rb_parent_color == address(sid) + color_bit(Color::Red));
                                                                if color_bit(Color::Red) == 0 { rewrite(color_bit(Color::Red) == 0); arithmetic() using { aligned(sid, 8); } } else { apply(color_bit_nonzero_is_one(Color::Red)); rewrite(color_bit(Color::Red) == 1); arithmetic() using { aligned(sid, 8); } }
                                                            }
                                                            have iid->__rb_parent_color == address(sid) + (iid->__rb_parent_color & 1) by { rewrite((iid->__rb_parent_color & 1) == color_bit(Color::Red)); assumption(); }
                                                            have parent->__rb_parent_color == address(iid) + 1;
                                                            have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(iid) + 1); arithmetic() using { aligned(iid, 8); } }
                                                            have parent->__rb_parent_color == address(iid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                            have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                            have iid->rb_left == parent by assumption();
                                                            have iid->rb_right == zid by assumption();
                                                            let rotated_up = fold(ctx_at(parent, root), { model: Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um)) }, { sibling: far_tree, up: red_up });
                                                            have ctx_node_is(Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um)), iid) == 1 by { unfold(ctx_node_is(Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um)), iid)); normalize(); }
                                                            apply(ctx_reroot_fixed(Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um)), iid));
                                                            have near.model == rb_reparent(irm, id) by { rewrite(id == parent); assumption(); }
                                                            apply(rb_reparent_parent_is(irm, id));
                                                            have parent->rb_left == node by assumption();
                                                            have parent->rb_right == tmp2 by assumption();
                                                            let nc = fold(ctx_at(node, root), { model: Context::Left(id, iid, Color::Black, rb_reparent(irm, id), Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um))) }, { sibling: near, up: rotated_up });
                                                            have plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm))) by { rewrite(nc.model == Context::Left(id, iid, Color::Black, rb_reparent(irm, id), Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um)))); unfold(plug(Context::Left(id, iid, Color::Black, rb_reparent(irm, id), Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um))), nt.model)); unfold(plug(Context::Left(iid, sid, Color::Red, RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm), Context::Left(sid, above, Color::Black, srm, um)), RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)))); normalize(); }
                                                            have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm)))); assumption(); }
                                                            have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm)))); assumption(); }
                                                            have plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm))) == erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), srm), um), nt.model) by {
                                                                unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), srm), um), nt.model));
                                                                apply(black_root_has_black_color(zrm)); rewrite(rb_color(zrm) == Color::Black); unfold(rb_color(RbTree::Node(iid, zid, Color::Red, irm, ilm))); normalize();
                                                            }
                                                            have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by {
                                                                rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm))));
                                                                rewrite(plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm))) == erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), srm), um), nt.model));
                                                                rewrite(RbTree::Node(iid, zid, Color::Red, irm, ilm) == zlm);
                                                                rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption();
                                                            }
                                                            have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by {
                                                                rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm))));
                                                                rewrite(rb_inorder(plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(iid, sid, Color::Red, RbTree::Node(id, iid, Color::Black, nt.model, rb_reparent(irm, id)), RbTree::Node(zid, iid, Color::Black, rb_reparent(ilm, zid), zrm)))) == rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, RbTree::Node(iid, zid, Color::Red, irm, ilm), zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model)));
                                                                rewrite(RbTree::Node(iid, zid, Color::Red, irm, ilm) == zlm);
                                                                rewrite(rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), nt.model)));
                                                                rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption();
                                                            }
                                                            step(); # Break after both rotations with a balanced whole tree.
                                                        },
                                                    }

                                                }
                                            } else {
                                                match nright.model {
                                                    RbTree::Empty => {
                                                        have zrm == RbTree::Empty by { rewrite(zrm == nright.model); assumption(); }
                                                        have rb_root_black(zrm) == 1 by { rewrite(zrm == RbTree::Empty); unfold(rb_root_black(RbTree::Empty)); normalize(); }
                                                        contradiction(rb_root_black(zrm) == 1);
                                                    },
                                                    RbTree::Node(rid, rp, rc, rrm, rlm) => {
                                                        have zrm == RbTree::Node(rid, rp, rc, rrm, rlm) by { rewrite(zrm == nright.model); assumption(); }
                                                        have not(rb_root_black(RbTree::Node(rid, rp, rc, rrm, rlm)) == 1) by { rewrite(RbTree::Node(rid, rp, rc, rrm, rlm) == zrm); assumption(); }
                                                        apply(outer_nonblack_node_color(rid, rp, rc, rrm, rlm));
                                                        have rb_parent_is(RbTree::Node(rid, rp, rc, rrm, rlm), zid) == 1 by { rewrite(RbTree::Node(rid, rp, rc, rrm, rlm) == zrm); assumption(); }
                                                        apply(rb_parent_is_node_parent(rid, rp, rc, rrm, rlm, zid));
                                                        have zrm == RbTree::Node(rid, zid, Color::Red, rrm, rlm) by { rewrite(zrm == RbTree::Node(rid, rp, rc, rrm, rlm)); rewrite(rp == zid); rewrite(rc == Color::Red); normalize(); }
                                                        have ctx_rb(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(rid, zid, Color::Red, rrm, rlm)), Context::Left(sid, above, Color::Black, srm, um)), Nat::Succ(black_height(nt.model)), Color::Black) == 1 by { rewrite(RbTree::Node(rid, zid, Color::Red, rrm, rlm) == zrm); assumption(); }
                                                        have rb_parent_consistent(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(rid, zid, Color::Red, rrm, rlm)), Context::Left(sid, above, Color::Black, srm, um)), nt.model), 0) == 1 by { rewrite(RbTree::Node(rid, zid, Color::Red, rrm, rlm) == zrm); assumption(); }
                                                        apply(ctx_erase_case4_left_exit(sid, id, Color::Red, zid, rid, nt.model, zlm, rrm, rlm, Context::Left(sid, above, Color::Black, srm, um)));
                                                        let { right: rl, left: rr } = unfold(nright);
                                                        have tmp1 == rid by { simp(); }
                                                        have sibling == zid by { simp(); }
                                                        have (rid->__rb_parent_color & 1) == 0 by { rewrite((rid->__rb_parent_color & 1) == color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                        have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == address(sid) + (parent->__rb_parent_color & 1)); rewrite((parent->__rb_parent_color & 1) == color_bit(Color::Red)); normalize(); }
                                                        have parent->rb_left == node by { simp(); }
                                                        have sibling->rb_right == tmp1 by { simp(); }
                                                        have zid->rb_right == sibling->rb_right by { normalize() using { sibling == zid; } }
                                                        have zid->rb_right == rid by { rewrite(zid->rb_right == sibling->rb_right); rewrite(sibling->rb_right == tmp1); assumption(); }
                                                        mark outer_inputs;
                                                        have at(outer_inputs, parent->__rb_parent_color) == address(sid) by { assumption(); }
                                                        fold(rb_red_parent_tag(parent, sid));
                                                        step(); # Red far child skips cases 2 and 3.
                                                        step(); # Read the near child.
                                                        step(); # Attach the near child to the parent.
                                                        step(); # Attach the parent under the sibling.
                                                        step(); # Blacken the far child.
                                                        step(); # Execute the far-child parent/color store.
                                                        have tmp1->__rb_parent_color == (address(sibling) | 1) by { assumption(); }
                                                        have rid->__rb_parent_color == (address(zid) | 1) by { simp() using { tmp1->__rb_parent_color == (address(sibling) | 1); tmp1 == rid; sibling == zid; } }
                                                        unfold(rb_red_parent_tag(parent, sid));
                                                        have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { rewrite(parent->__rb_parent_color == address(sid)); rewrite(at(outer_inputs, parent->__rb_parent_color) == address(sid)); normalize(); }
                                                        have parent->rb_left == node by { simp() using { at(outer_inputs, parent->rb_left) == node; tmp1 == rid; sibling == zid; } }
                                                        have parent->rb_right == tmp2 by { simp() using { tmp1 == rid; sibling == zid; } }
                                                        have sibling->rb_left == parent by { assumption(); }
                                                        have zid->rb_left == parent by { rewrite(zid == sibling); normalize() using { sibling->rb_left == parent; } }
                                                        have sibling->rb_right == tmp1 by { simp(); }
                                                        have zid->rb_right == sibling->rb_right by { normalize() using { sibling == zid; } }
                                                        have zid->rb_right == rid by { rewrite(zid->rb_right == sibling->rb_right); rewrite(sibling->rb_right == tmp1); assumption(); }
                                                        have id->rb_left == node by { simp() using { parent->rb_left == node; parent == id; } }
                                                        have rid->__rb_parent_color == (address(zid) | 1) by { assumption(); }
                                                        have aligned(zid, 8) by { simp(); }
                                                        have rid->__rb_parent_color == address(zid) + 1 by { rewrite(rid->__rb_parent_color == (address(zid) | 1)); arithmetic() using { aligned(zid, 8); } }
                                                        have (rid->__rb_parent_color & 1) == 1 by { normalize(); }
                                                        have rid->__rb_parent_color == address(zid) + (rid->__rb_parent_color & 1) by { normalize() using { rid->__rb_parent_color == address(zid) + 1; (rid->__rb_parent_color & 1) == 1; } }
                                                        have (rid->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); normalize(); }
                                                        let far_tree = fold(rb_at(rid), { model: RbTree::Node(rid, zid, Color::Black, rrm, rlm) }, { right: rl, left: rr });
                                                        apply(rb_parent_is_node_of(rid, zid, Color::Black, rrm, rlm));
                                                        fold(rb_child_links(zid, parent, rid));
                                                        fold(rb_child_links(parent, node, tmp2));
                                                        fold(rb_red_parent_tag(parent, sid));
                                                        match nleft.model ensuring {
                                                            owns near: rb_at(tmp2);
                                                            fact near.model == rb_reparent(zlm, parent);
                                                        } {
                                                            RbTree::Empty => {
                                                                have zlm == RbTree::Empty by { rewrite(zlm == nleft.model); assumption(); }
                                                                unfold(nleft);
                                                                have tmp2 == 0 by { simp(); }
                                                                step(); step();
                                                                let near = fold(rb_at(tmp2), { model: RbTree::Empty });
                                                                have near.model == rb_reparent(zlm, parent) by { rewrite(zlm == RbTree::Empty); unfold(rb_reparent(RbTree::Empty, parent)); normalize(); }
                                                            },
                                                            RbTree::Node(nid, np, nc, nrm, nlm) => {
                                                                have zlm == RbTree::Node(nid, np, nc, nrm, nlm) by { rewrite(zlm == nleft.model); assumption(); }
                                                                let { right: nr, left: nl } = unfold(nleft);
                                                                have tmp2 == nid by { simp(); }
                                                                have tmp2 != 0 by { simp(); }
                                                                have (tmp2->__rb_parent_color & 1) == color_bit(nc) by { simp(); }
                                                                mark near_tag;
                                                                step();
                                                                step(rb_set_parent(tmp2, parent), {});
                                                                have tmp2->__rb_parent_color == (color_bit(nc) | address(parent)) by { rewrite(tmp2->__rb_parent_color == ((at(near_tag, tmp2->__rb_parent_color) & 1) | address(parent))); rewrite((at(near_tag, tmp2->__rb_parent_color) & 1) == color_bit(nc)); normalize(); }
                                                                have tmp2->__rb_parent_color == address(parent) + color_bit(nc) by {
                                                                    rewrite(tmp2->__rb_parent_color == (color_bit(nc) | address(parent)));
                                                                    if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); normalize(); } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                }
                                                                have (tmp2->__rb_parent_color & 1) == color_bit(nc) by {
                                                                    rewrite(tmp2->__rb_parent_color == address(parent) + color_bit(nc));
                                                                    if color_bit(nc) == 0 { rewrite(color_bit(nc) == 0); arithmetic() using { aligned(parent, 8); }; } else { apply(color_bit_nonzero_is_one(nc)); rewrite(color_bit(nc) == 1); arithmetic() using { aligned(parent, 8); }; }
                                                                }
                                                                have tmp2->__rb_parent_color == address(parent) + (tmp2->__rb_parent_color & 1) by { rewrite((tmp2->__rb_parent_color & 1) == color_bit(nc)); assumption(); }
                                                                let near = fold(rb_at(tmp2), { model: RbTree::Node(nid, parent, nc, nrm, nlm) }, { right: nr, left: nl });
                                                                have near.model == rb_reparent(zlm, parent) by { rewrite(zlm == RbTree::Node(nid, np, nc, nrm, nlm)); unfold(rb_reparent(RbTree::Node(nid, np, nc, nrm, nlm), parent)); simp(); }
                                                            },
                                                        }
                                                        unfold(rb_red_parent_tag(parent, sid));
                                                        unfold(rb_child_links(zid, parent, rid));
                                                        unfold(rb_child_links(parent, node, tmp2));
                                                        have parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color) by { rewrite(parent->__rb_parent_color == address(sid)); rewrite(at(outer_inputs, parent->__rb_parent_color) == address(sid)); normalize(); }
                                                        have parent->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(parent->__rb_parent_color == at(outer_inputs, parent->__rb_parent_color)); assumption(); }
                                                        have red_up.model == Context::Left(sid, above, Color::Black, srm, um) by { assumption(); }
                                                        apply(ctx_parent_word_from_color(red_up.model, sid, parent->__rb_parent_color, Color::Red));
                                                        have parent->rb_left == node by { assumption(); }
                                                        have parent->rb_right == tmp2 by { assumption(); }
                                                        have zid->rb_left == parent by { assumption(); }
                                                        have zid->rb_right == rid by { assumption(); }
                                                        fold(rb_child_links(zid, parent, rid));
                                                        fold(rb_child_links(parent, node, tmp2));
                                                        mark outer_rotation;
                                                        let { after: red_up } = step(__rb_rotate_set_parents(parent, sibling, root, 1), { c: red_up });
                                                        step(); # The augmentation callback preserves the tree resources.
                                                        unfold(rb_child_links(zid, parent, rid));
                                                        unfold(rb_child_links(parent, node, tmp2));
                                                        have sibling->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { simp(); }
                                                        have zid->__rb_parent_color == sibling->__rb_parent_color by { normalize() using { sibling == zid; parent == id; } }
                                                        have zid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color) by { rewrite(zid->__rb_parent_color == sibling->__rb_parent_color); assumption(); }
                                                        have zid->__rb_parent_color == address(sid) + color_bit(Color::Red) by { rewrite(zid->__rb_parent_color == at(outer_rotation, parent->__rb_parent_color)); assumption(); }
                                                        have (zid->__rb_parent_color & 1) == color_bit(Color::Red) by {
                                                            rewrite(zid->__rb_parent_color == address(sid) + color_bit(Color::Red));
                                                            if color_bit(Color::Red) == 0 { rewrite(color_bit(Color::Red) == 0); arithmetic() using { aligned(sid, 8); } } else { apply(color_bit_nonzero_is_one(Color::Red)); rewrite(color_bit(Color::Red) == 1); arithmetic() using { aligned(sid, 8); } }
                                                        }
                                                        have zid->__rb_parent_color == address(sid) + (zid->__rb_parent_color & 1) by { rewrite((zid->__rb_parent_color & 1) == color_bit(Color::Red)); assumption(); }
                                                        have parent->__rb_parent_color == address(zid) + 1 by { simp(); }
                                                        have (parent->__rb_parent_color & 1) == 1 by { rewrite(parent->__rb_parent_color == address(zid) + 1); arithmetic() using { aligned(zid, 8); } }
                                                        have parent->__rb_parent_color == address(zid) + (parent->__rb_parent_color & 1) by { rewrite((parent->__rb_parent_color & 1) == 1); assumption(); }
                                                        have (parent->__rb_parent_color & 1) == color_bit(Color::Black) by { unfold(color_bit(Color::Black)); assumption(); }
                                                        have zid->rb_left == parent by { assumption(); }
                                                        have zid->rb_right == rid by { assumption(); }
                                                        have zid->__rb_parent_color == address(sid) by { rewrite(zid->__rb_parent_color == address(sid) + color_bit(Color::Red)); unfold(color_bit(Color::Red)); normalize(); }
                                                        let rotated_up = fold(ctx_at(parent, root), { model: Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um)) }, { sibling: far_tree, up: red_up });
                                                        have ctx_node_is(Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um)), zid) == 1 by { unfold(ctx_node_is(Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um)), zid)); normalize(); }
                                                        apply(ctx_reroot_fixed(Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um)), zid));
                                                        have near.model == rb_reparent(zlm, id) by { rewrite(id == parent); assumption(); }
                                                        apply(rb_reparent_parent_is(zlm, id));
                                                        have parent->rb_left == node by { assumption(); }
                                                        have parent->rb_right == tmp2 by { assumption(); }
                                                        let nc = fold(ctx_at(node, root), { model: Context::Left(id, zid, Color::Black, rb_reparent(zlm, id), Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um))) }, { sibling: near, up: rotated_up });
                                                        have plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm))) by { rewrite(nc.model == Context::Left(id, zid, Color::Black, rb_reparent(zlm, id), Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um)))); unfold(plug(Context::Left(id, zid, Color::Black, rb_reparent(zlm, id), Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um))), nt.model)); unfold(plug(Context::Left(zid, sid, Color::Red, RbTree::Node(rid, zid, Color::Black, rrm, rlm), Context::Left(sid, above, Color::Black, srm, um)), RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)))); normalize(); }
                                                        have is_rb_root(plug(nc.model, nt.model)) == 1 by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm)))); assumption(); }
                                                        have rb_tree_parent_consistent(plug(nc.model, nt.model)) == 1 by { unfold(rb_tree_parent_consistent(plug(nc.model, nt.model))); rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm)))); assumption(); }
                                                        have rb_root_black(RbTree::Node(rid, zid, Color::Red, rrm, rlm)) == 0 by { unfold(rb_root_black(RbTree::Node(rid, zid, Color::Red, rrm, rlm))); normalize(); }
                                                        have erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, RbTree::Node(rid, zid, Color::Red, rrm, rlm)), srm), um), nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm))) by { unfold(erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, RbTree::Node(rid, zid, Color::Red, rrm, rlm)), srm), um), nt.model)); unfold(rb_color(RbTree::Node(rid, zid, Color::Red, rrm, rlm))); normalize(); }
                                                        have plug(nc.model, nt.model) == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm)))); rewrite(plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm))) == erase_flips_red_all_result(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, RbTree::Node(rid, zid, Color::Red, rrm, rlm)), srm), um), nt.model)); rewrite(RbTree::Node(rid, zid, Color::Red, rrm, rlm) == zrm); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                        have rb_inorder(plug(nc.model, nt.model)) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(plug(nc.model, nt.model) == plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm)))); rewrite(rb_inorder(plug(Context::Left(sid, above, Color::Black, srm, um), RbTree::Node(zid, sid, Color::Red, RbTree::Node(id, zid, Color::Black, nt.model, rb_reparent(zlm, id)), RbTree::Node(rid, zid, Color::Black, rrm, rlm)))) == rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, RbTree::Node(rid, zid, Color::Red, rrm, rlm)), Context::Left(sid, above, Color::Black, srm, um)), nt.model))); rewrite(RbTree::Node(rid, zid, Color::Red, rrm, rlm) == zrm); rewrite(rb_inorder(plug(Context::Left(id, sid, Color::Red, RbTree::Node(zid, id, Color::Black, zlm, zrm), Context::Left(sid, above, Color::Black, srm, um)), nt.model)) == rb_inorder(plug(Context::Left(id, above, Color::Black, RbTree::Node(sid, id, Color::Red, RbTree::Node(zid, sid, Color::Black, zlm, zrm), srm), um), nt.model))); rewrite(RbTree::Node(zid, sid, Color::Black, zlm, zrm) == slm); assumption(); }
                                                        step(); # Break with a balanced context around the unchanged focus.

                                                    },
                                                }
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
    }
    mark refold;
    let { whole: whole } = refold_to_root(node, root, { c: c, t: t });
    have whole.model == erase_flips_red_all_result(old(c.model), RbTree::Empty) by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    have is_rb_root(whole.model) == 1 by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    have rb_tree_parent_consistent(whole.model) == 1 by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    have rb_inorder(whole.model) == rb_inorder(plug(old(c.model), RbTree::Empty)) by { rewrite(whole.model == at(refold, plug(c.model, t.model))); assumption(); }
    execute(); simp();
}
