# a descending loop's context frame is built from each child once

The frame a descent builds takes the enclosing context as its `up` child and
the untaken subtree as its `sibling`, so both are consumed by that fold.
A body that folds a second frame from the same children is refused by name:
ownership is linear, and a frame the proof no longer holds cannot become a
child twice. Without this a descent could keep the context it already spent
and close the invariants with a frame stack that no heap supports.

This is the verified descent of
[`examples/modeled-binary-tree`](../examples/modeled-binary-tree/README.md)
with one extra fold.

```c filename=loop_context_frame_refold_rejected.c
struct tree_node {
    int32 value;
    struct tree_node *left;
    struct tree_node *right;
};

struct tree_node *tree_leftmost(struct tree_node *root) {
    if (root == 0) {
        return 0;
    }

    while (root->left != 0) {
        root = root->left;
    }

    return root;
}
```

```click
verifying "loop_context_frame_refold_rejected.c";

spec enum HeapTree {
    Empty,
    Node(struct tree_node*, int, HeapTree, HeapTree),
}

resource tree_at(p: struct tree_node*) {
    field model: HeapTree;
    match model {
        HeapTree::Empty => { fact p == 0; },
        HeapTree::Node(identity, value, left_model, right_model) => {
            owns p->value;
            owns p->left;
            owns p->right;
            owns left: tree_at(p->left);
            owns right: tree_at(p->right);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact left.model == left_model;
            fact right.model == right_model;
        },
    }
}

spec enum Context {
    Top,
    Left(struct tree_node*, int, HeapTree, Context),
    Right(struct tree_node*, int, HeapTree, Context),
}

resource ctx_at(child: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => { },
        Context::Left(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->right);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->left == child;
            fact parent->value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->left);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->right == child;
            fact parent->value == value;
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
        Context::Left(parent, value, sibling_model, up_model) =>
            plug(up_model, HeapTree::Node(parent, value, sub, sibling_model)),
        Context::Right(parent, value, sibling_model, up_model) =>
            plug(up_model, HeapTree::Node(parent, value, sibling_model, sub)),
    }
}

theorem plug_top_frame(sub: HeapTree) {
    ensures plug(Context::Top, sub) == sub by {
        unfold(plug(Context::Top, sub));
        normalize();
    }
}

theorem plug_left_frame(parent: struct tree_node*, value: int, sibling: HeapTree,
                        up: Context, sub: HeapTree) {
    ensures plug(Context::Left(parent, value, sibling, up), sub)
        == plug(up, HeapTree::Node(parent, value, sub, sibling)) by {
        unfold(plug(Context::Left(parent, value, sibling, up), sub));
        normalize();
    }
}

theorem plug_right_frame(parent: struct tree_node*, value: int, sibling: HeapTree,
                         up: Context, sub: HeapTree) {
    ensures plug(Context::Right(parent, value, sibling, up), sub)
        == plug(up, HeapTree::Node(parent, value, sibling, sub)) by {
        unfold(plug(Context::Right(parent, value, sibling, up), sub));
        normalize();
    }
}

function heap_left(tree: HeapTree) -> HeapTree {
    match tree {
        HeapTree::Empty => HeapTree::Empty,
        HeapTree::Node(node, value, left, right) => left,
    }
}

struct tree_node* tree_leftmost(struct tree_node* root) {
    consumes t: tree_at(root);
    requires t.model != HeapTree::Empty;
    produces ctx: ctx_at(result);
    produces sub: tree_at(result);
    ensures plug(ctx.model, sub.model) == old(t.model);
    ensures heap_left(sub.model) == HeapTree::Empty;
} by {
    step();
    step();
    let ctx = fold(ctx_at(root), { model: Context::Top });
    have plug(ctx.model, t.model) == old(t.model) by {
        rewrite(ctx.model == Context::Top);
        unfold(plug(Context::Top, t.model));
        normalize();
    }
    loop {
        owns ctx: ctx_at(root);
        owns t: tree_at(root);
        decreases t;
        invariant t.model != HeapTree::Empty;
        invariant plug(ctx.model, t.model) == old(t.model);

        initialize by simp;
        preserve by {
            match t.model {
                HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
                HeapTree::Node(identity, value, left_model, right_model) => {
                    have plug(Context::Left(identity, value, right_model, ctx.model), left_model)
                        == old(t.model) by {
                        unfold(plug(Context::Left(identity, value, right_model, ctx.model),
                            left_model));
                        rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                        assumption();
                    }
                    unfold(t) as { left: l, right: rt };
                    have plug(Context::Left(root, value, right_model, ctx.model), left_model)
                        == old(t.model) by {
                        rewrite(root == identity);
                        assumption();
                    }
                    let frame = fold(ctx_at(root->left), {
                        model: Context::Left(root, value, right_model, ctx.model)
                    }, { sibling: rt, up: ctx });
                    let again = fold(ctx_at(root->left), {
                        model: Context::Left(root, value, right_model, Context::Top)
                    }, { sibling: rt, up: ctx });
                    step();
                    close_invariants();
                },
            }
        }
    }
    match t.model {
        HeapTree::Empty => { contradiction(t.model == HeapTree::Empty); },
        HeapTree::Node(identity, value, left_model, right_model) => {
            have plug(ctx.model, HeapTree::Node(identity, value, left_model, right_model))
                == old(t.model) by {
                rewrite(HeapTree::Node(identity, value, left_model, right_model) == t.model);
                assumption();
            }
            unfold(t) as { left: l, right: rt };
            have heap_left(HeapTree::Node(identity, value, left_model, right_model))
                == left_model by {
                unfold(heap_left(HeapTree::Node(identity, value, left_model, right_model)));
                normalize();
            }
            let sub = fold(tree_at(root), {
                model: HeapTree::Node(identity, value, left_model, right_model)
            }, { left: l, right: rt });
            have heap_left(sub.model) == HeapTree::Empty by {
                rewrite(sub.model == HeapTree::Node(identity, value, left_model, right_model));
                rewrite(heap_left(HeapTree::Node(identity, value, left_model, right_model))
                    == left_model);
                assumption();
            }
            have plug(ctx.model, sub.model) == old(t.model) by {
                rewrite(sub.model == HeapTree::Node(identity, value, left_model, right_model));
                assumption();
            }
            step();
            simp();
        },
    }
}
```

```expect
fail: child `rt` is not owned in folded form
```
