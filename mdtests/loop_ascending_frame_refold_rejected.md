# an ascent cannot keep the frame it consumed

Each iteration of an ascending walk spends one frame: `unfold(c)` takes the
frame apart, and the node it owned becomes the root of the larger focused
subtree, built from the old focus and the frame's sibling. That sibling is
consumed by the fold. A body that then rebuilds the frame it just unfolded, so
that the next iteration would hold both the larger subtree and the frame above
its own root, is refused by naming the child it no longer holds.

Without this an ascent could climb while keeping every frame it passed, and
`close_invariants()` would close over a context stack that no heap supports.
This is the ascending counterpart of
[`loop_context_frame_refold_rejected.md`](loop_context_frame_refold_rejected.md),
which catches the same error on a descent.

```c filename=loop_ascending_frame_refold_rejected.c
struct tree_node {
    int32 value;
    struct tree_node *left;
    struct tree_node *right;
    struct tree_node *parent;
};

struct tree_node *tree_root_of(struct tree_node *node, struct tree_node *parent) {
    while (parent != 0) {
        node = parent;
        parent = node->parent;
    }

    return node;
}
```

```click
verifying "loop_ascending_frame_refold_rejected.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

resource ptree_at(p: struct tree_node*, parent: struct tree_node*) {
    field model: HeapTree;
    match model {
        HeapTree::Empty => { fact p == 0; },
        HeapTree::Node(identity, value, left_model, right_model) => {
            owns p->value;
            owns p->left;
            owns p->right;
            owns p->parent;
            owns left: ptree_at(p->left, p);
            owns right: ptree_at(p->right, p);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact p->parent == parent;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

spec enum Context {
    Top,
    Left(struct tree_node*, struct tree_node*, int, HeapTree, Context),
    Right(struct tree_node*, struct tree_node*, int, HeapTree, Context),
}

resource pctx_at(child: struct tree_node*, parent: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => { fact parent == 0; },
        Context::Left(identity, grandparent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns parent->parent;
            owns sibling: ptree_at(parent->right, parent);
            owns up: pctx_at(parent, grandparent);
            fact parent != 0;
            fact parent == identity;
            fact parent->left == child;
            fact parent->value == value;
            fact parent->parent == grandparent;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(identity, grandparent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns parent->parent;
            owns sibling: ptree_at(parent->left, parent);
            owns up: pctx_at(parent, grandparent);
            fact parent != 0;
            fact parent == identity;
            fact parent->right == child;
            fact parent->value == value;
            fact parent->parent == grandparent;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}

function plug(ctx: Context, sub: HeapTree) -> HeapTree
    decreases ctx
{
    match ctx {
        Context::Top => sub,
        Context::Left(identity, grandparent, value, sibling_model, up_model) =>
            plug(up_model, HeapTree::Node(identity, value, sub, sibling_model)),
        Context::Right(identity, grandparent, value, sibling_model, up_model) =>
            plug(up_model, HeapTree::Node(identity, value, sibling_model, sub)),
    }
}

struct tree_node* tree_root_of(struct tree_node* node, struct tree_node* parent) {
    consumes c: pctx_at(node, parent);
    consumes t: ptree_at(node, parent);
    requires t.model != HeapTree::Empty;
    produces ctx: pctx_at(result, 0);
    produces sub: ptree_at(result, 0);
    ensures sub.model == plug(old(c.model), old(t.model));
} by {
    loop {
        owns c: pctx_at(node, parent);
        owns t: ptree_at(node, parent);
        decreases c;
        invariant t.model != HeapTree::Empty;
        invariant plug(c.model, t.model) == plug(old(c.model), old(t.model));

        initialize by simp;
        preserve by {
            match c.model {
                Context::Top => { contradiction(c.model == Context::Top); },
                Context::Left(identity, grandparent, value, sibling_model, up_model) => {
                    have plug(up_model,
                              HeapTree::Node(identity, value, t.model, sibling_model))
                        == plug(old(c.model), old(t.model)) by {
                        unfold(plug(Context::Left(identity, grandparent, value,
                                                  sibling_model, up_model), t.model));
                        rewrite(plug(up_model,
                                     HeapTree::Node(identity, value, t.model, sibling_model))
                            == plug(Context::Left(identity, grandparent, value,
                                                  sibling_model, up_model), t.model));
                        rewrite(Context::Left(identity, grandparent, value,
                                              sibling_model, up_model) == c.model);
                        assumption();
                    }
                    unfold(c) as { sibling: s, up: u };
                    step();
                    step();
                    let lifted = fold(ptree_at(node, parent), {
                        model: HeapTree::Node(identity, value, t.model, sibling_model)
                    }, { left: t, right: s });
                    let kept = fold(pctx_at(node, parent), {
                        model: Context::Left(identity, grandparent, value,
                                             sibling_model, up_model)
                    }, { sibling: s, up: u });
                    close_invariants();
                },
                Context::Right(identity, grandparent, value, sibling_model, up_model) => {
                    have plug(up_model,
                              HeapTree::Node(identity, value, sibling_model, t.model))
                        == plug(old(c.model), old(t.model)) by {
                        unfold(plug(Context::Right(identity, grandparent, value,
                                                   sibling_model, up_model), t.model));
                        rewrite(plug(up_model,
                                     HeapTree::Node(identity, value, sibling_model, t.model))
                            == plug(Context::Right(identity, grandparent, value,
                                                   sibling_model, up_model), t.model));
                        rewrite(Context::Right(identity, grandparent, value,
                                               sibling_model, up_model) == c.model);
                        assumption();
                    }
                    unfold(c) as { sibling: s, up: u };
                    step();
                    step();
                    let lifted = fold(ptree_at(node, parent), {
                        model: HeapTree::Node(identity, value, sibling_model, t.model)
                    }, { left: s, right: t });
                    close_invariants();
                },
            }
        }
    }
    have plug(c.model, t.model) == t.model by {
        rewrite(c.model == Context::Top);
        unfold(plug(Context::Top, t.model));
        normalize();
    }
    have t.model == plug(old(c.model), old(t.model)) by {
        rewrite(t.model == plug(c.model, t.model));
        assumption();
    }
    unfold(c);
    let ctx = fold(pctx_at(node, parent), { model: Context::Top });
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(identity, value, left_model, right_model) => {
            have HeapTree::Node(identity, value, left_model, right_model)
                == plug(old(c.model), old(t.model)) by {
                rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                assumption();
            }
            unfold(t) as { left: l, right: r };
            let sub = fold(ptree_at(node, parent), {
                model: HeapTree::Node(identity, value, left_model, right_model)
            }, { left: l, right: r });
            have sub.model == plug(old(c.model), old(t.model)) by {
                rewrite(sub.model
                    == HeapTree::Node(identity, value, left_model, right_model));
                assumption();
            }
            step();
            simp();
        },
    }
}
```

```expect
fail: child `s` is not owned in folded form
```
