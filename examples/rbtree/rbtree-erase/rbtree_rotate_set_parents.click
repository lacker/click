// Retarget a rotation's incoming link and packed parent/color words.
// The helper preserves the exact outer context for either parent link or root.
verifying "rb_erase_color.c";
import "../rbtree-model/rbtree_resources.click";

void __rb_change_child(struct rb_node* old, struct rb_node* new,
                       struct rb_node* parent, struct rb_root* root) {
    consumes before: ctx_at(old, root);
    owns old->__rb_parent_color;
    requires old != 0;
    requires ctx_node_is(before.model, parent) == 1;
    produces after: ctx_at(new, root);
    ensures after.model == old(before.model);
    ensures old->__rb_parent_color == old(old->__rb_parent_color);
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *))
        == old((old->__rb_parent_color & ~3) as (struct rb_node *));
} by {
    have old != 0 by close();
    match before.model {
        Context::Top => {
            have parent == 0 by {
                have ctx_node_is(Context::Top, parent) == 1 by {
                    rewrite(Context::Top, before.model); close();
                }
                if parent == 0 { close(); } else {
                    have ctx_node_is(Context::Top, parent) != 1 by {
                        unfold(ctx_node_is(Context::Top, parent)); normalize() using { not(parent == 0); };
                    }
                    contradiction(ctx_node_is(Context::Top, parent) == 1);
                }
            }
            unfold(before);
            step_until(function.exit);
            let after = fold(ctx_at(new, root), { model: Context::Top });
            close();
        },
        Context::Left(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Left(identity, grandparent, color, sibling_model, outer_model), before.model); close();
                }
                if parent == identity { close(); } else {
                    have ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) != 1 by {
                        unfold(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent)); normalize() using { not(parent == identity); };
                    }
                    contradiction(ctx_node_is(Context::Left(identity, grandparent, color, sibling_model, outer_model), parent) == 1);
                }
            }
            let { sibling: sibling, up: outer } = unfold(before);
            mark before_link_write;
            have separate(memory(parent->rb_left), memory(identity->__rb_parent_color)) by {
                rewrite(parent, identity); close();
            }
            step_until(function.exit);
            have separate(statement(0).statement(0).statement(0).footprint, memory(identity->__rb_parent_color)) by close();
            have identity->__rb_parent_color == at(before_link_write, identity->__rb_parent_color) by {
                preserve(memory(identity->__rb_parent_color), statement(0).statement(0).statement(0));
            }
            have ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent by {
                rewrite(identity->__rb_parent_color, at(before_link_write, identity->__rb_parent_color)); close();
            }
            let after = fold(ctx_at(new, root), {
                model: Context::Left(identity, grandparent, color, sibling_model, outer_model),
                up: outer,
                sibling: sibling
            });
            close();
        },
        Context::Right(identity, grandparent, color, sibling_model, outer_model) => {
            have parent == identity by {
                have ctx_node_is(Context::Right(identity, grandparent, color, sibling_model, outer_model), parent) == 1 by {
                    rewrite(Context::Right(identity, grandparent, color, sibling_model, outer_model), before.model); close();
                }
                if parent == identity { close(); } else {
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
                    have old != 0 by close();
                    have parent->rb_left != old by {
                        if parent->rb_left == old {
                            have old == 0 by { normalize() using { parent->rb_left == old; parent->rb_left == 0; }; }
                            contradiction(old != 0);
                        } else { close(); }
                    }
                    let sibling = fold(rb_at(0), { model: RbTree::Empty });
                    mark before_link_write;
                    have separate(memory(parent->rb_right), memory(identity->__rb_parent_color)) by {
                        rewrite(parent, identity); close();
                    }
                    step_until(function.exit);
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color)) by close();
                    have identity->__rb_parent_color == at(before_link_write, identity->__rb_parent_color) by {
                        preserve(memory(identity->__rb_parent_color), statement(0).statement(0).statement(1));
                    }
                    have ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent by {
                        rewrite(identity->__rb_parent_color, at(before_link_write, identity->__rb_parent_color)); close();
                    }
                    have separate(memory(parent->rb_right), memory(identity->rb_left)) by {
                        rewrite(parent, identity); close();
                    }
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->rb_left)) by close();
                    have identity->rb_left == at(before_link_write, identity->rb_left) by {
                        preserve(memory(identity->rb_left), statement(0).statement(0).statement(1));
                    }
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model),
                        up: outer,
                        sibling: sibling
                    });
                    close();
                },
                RbTree::Node(sid, sp, sc, sl, sr) => {
                    let { left: left, right: right } = unfold(sibling);
                    have separate(memory(identity->rb_left->__rb_parent_color), memory(old->__rb_parent_color)) by close();
                    have identity->rb_left != old by close();
                    have parent->rb_left != old by { rewrite(parent, identity); close(); }
                    let sibling = fold(rb_at(identity->rb_left), {
                        model: RbTree::Node(sid, sp, sc, sl, sr),
                        left: left, right: right
                    });
                    mark before_link_write;
                    have separate(memory(parent->rb_right), memory(identity->__rb_parent_color)) by {
                        rewrite(parent, identity); close();
                    }
                    step_until(function.exit);
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->__rb_parent_color)) by close();
                    have identity->__rb_parent_color == at(before_link_write, identity->__rb_parent_color) by {
                        preserve(memory(identity->__rb_parent_color), statement(0).statement(0).statement(1));
                    }
                    have ((identity->__rb_parent_color & ~3) as (struct rb_node *)) == grandparent by {
                        rewrite(identity->__rb_parent_color, at(before_link_write, identity->__rb_parent_color)); close();
                    }
                    have separate(memory(parent->rb_right), memory(identity->rb_left)) by {
                        rewrite(parent, identity); close();
                    }
                    have separate(statement(0).statement(0).statement(1).footprint, memory(identity->rb_left)) by close();
                    have identity->rb_left == at(before_link_write, identity->rb_left) by {
                        preserve(memory(identity->rb_left), statement(0).statement(0).statement(1));
                    }
                    let after = fold(ctx_at(new, root), {
                        model: Context::Right(identity, grandparent, color, sibling_model, outer_model),
                        up: outer,
                        sibling: sibling
                    });
                    close();
                },
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
    requires ((old->__rb_parent_color & ~3) as (struct rb_node *)) == ctx_identity(c.model);
    produces after: ctx_at(new, root);
    ensures after.model == old(c.model);
    ensures new->__rb_parent_color == old(old->__rb_parent_color);
    ensures old->__rb_parent_color == address(new) + color;
    ensures ((new->__rb_parent_color & ~3) as (struct rb_node *)) == ctx_identity(old(c.model));
    ensures ((old->__rb_parent_color & ~3) as (struct rb_node *)) == new;
} by {
    match c.model {
        Context::Top => {
            unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Top });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model, Context::Top); rewrite(Context::Top, old(c.model)); close(); }
            have (old->__rb_parent_color & ~3) == 0 by {
                if old->__rb_parent_color == 0 {
                    rewrite(old->__rb_parent_color, 0); normalize();
                } else {
                    have old->__rb_parent_color == 1 by {
                        if old->__rb_parent_color == 1 { close(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, Context::Top); unfold(ctx_parent_word(Context::Top, old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == 0); not(old->__rb_parent_color == 1); };
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color), 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    rewrite(old->__rb_parent_color, 1); normalize();
                }
            }
            step_until(assignment(parent, 0).entry);
            step();
            have parent == 0;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model, Context::Top); rewrite(parent, 0); unfold(ctx_node_is(Context::Top, 0)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color));
                if color == 0 { rewrite(color, 0); normalize(); } else {
                    have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
                    rewrite(color, 1);
                    close() using { aligned(new, 8); };
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by close();
            let { after: after } = step(__rb_change_child, { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color, at(words, old->__rb_parent_color)); close();
            }
            step_until(function.exit);
        },
        Context::Left(id, above, pc, sibling, up) => {
            unfold(ctx_identity(Context::Left(id, above, pc, sibling, up)));
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Left(id, above, pc, sibling, up), sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model, Context::Left(id, above, pc, sibling, up)); rewrite(Context::Left(id, above, pc, sibling, up), old(c.model)); close(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    close() using { old->__rb_parent_color == address(id); aligned(id, 8); };
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { close(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, Context::Left(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Left(id, above, pc, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); };
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color), 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    close() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); };
                }
            }
            step_until(assignment(parent, 0).entry);
            step();
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model, Context::Left(id, above, pc, sibling, up)); rewrite(parent, id); unfold(ctx_node_is(Context::Left(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color));
                if color == 0 { rewrite(color, 0); normalize(); } else {
                    have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
                    rewrite(color, 1);
                    close() using { aligned(new, 8); };
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by close();
            let { after: after } = step(__rb_change_child, { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color, at(words, old->__rb_parent_color)); close();
            }
            step_until(function.exit);
        },
        Context::Right(id, above, pc, sibling, up) => {
            unfold(ctx_identity(Context::Right(id, above, pc, sibling, up)));
            let { sibling: s, up: u } = unfold(c);
            let d = fold(ctx_at(old, root), { model: Context::Right(id, above, pc, sibling, up), sibling: s, up: u });
            have ctx_parent_word(d.model, old->__rb_parent_color) == 1 by { rewrite(d.model, Context::Right(id, above, pc, sibling, up)); rewrite(Context::Right(id, above, pc, sibling, up), old(c.model)); close(); }
            have (old->__rb_parent_color & ~3) == address(id) by {
                if old->__rb_parent_color == address(id) {
                    close() using { old->__rb_parent_color == address(id); aligned(id, 8); };
                } else {
                    have old->__rb_parent_color == address(id) + 1 by {
                        if old->__rb_parent_color == address(id) + 1 { close(); } else {
                            have ctx_parent_word(d.model, old->__rb_parent_color) == 0 by {
                                rewrite(d.model, Context::Right(id, above, pc, sibling, up)); unfold(ctx_parent_word(Context::Right(id, above, pc, sibling, up), old->__rb_parent_color));
                                normalize() using { not(old->__rb_parent_color == address(id)); not(old->__rb_parent_color == address(id) + 1); };
                            }
                            have not(ctx_parent_word(d.model, old->__rb_parent_color) == 1) by { rewrite(ctx_parent_word(d.model, old->__rb_parent_color), 0); normalize(); }
                            contradiction(ctx_parent_word(d.model, old->__rb_parent_color) == 1);
                        }
                    }
                    close() using { old->__rb_parent_color == address(id) + 1; aligned(id, 8); };
                }
            }
            step_until(assignment(parent, 0).entry);
            step();
            have parent == id;
            have ctx_node_is(d.model, parent) == 1 by { rewrite(d.model, Context::Right(id, above, pc, sibling, up)); rewrite(parent, id); unfold(ctx_node_is(Context::Right(id, above, pc, sibling, up), id)); normalize(); }
            step(); step();
            have old->__rb_parent_color == (address(new) | color);
            have old->__rb_parent_color == address(new) + color by {
                rewrite(old->__rb_parent_color, (address(new) | color));
                if color == 0 { rewrite(color, 0); normalize(); } else {
                    have color == 1 by { close() using { 0 <= color; color <= 1; not(color == 0); }; }
                    rewrite(color, 1);
                    close() using { aligned(new, 8); };
                }
            }
            mark words;
            have at(words, old->__rb_parent_color) == address(new) + color by close();
            let { after: after } = step(__rb_change_child, { before: d });
            have old->__rb_parent_color == address(new) + color by {
                have old->__rb_parent_color == at(words, old->__rb_parent_color);
                rewrite(old->__rb_parent_color, at(words, old->__rb_parent_color)); close();
            }
            step_until(function.exit);
        },
    }
}
