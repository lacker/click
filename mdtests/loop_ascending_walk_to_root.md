# an ascending walk climbs a zipper and returns at the root

A descending walk pushes frames onto a context; an ascending one pops them.
The C keeps the pair every Linux rbtree fixup loop keeps — the focused node
and its parent — and the proof keeps the matching pair of instances, the
focused subtree `t: ptree_at(node, parent)` and the frames above it,
`c: pctx_at(node, parent)`. Each iteration consumes one frame: it unfolds the
frame, takes the C step that moves the cursor up, and folds the node the frame
owned into a larger subtree from the old focus and the frame's sibling. The
measure is the context, `decreases c;`, because the focused subtree grows
while the context strictly loses a frame.

Three things make the two ends of the walk work.

The frame takes the focused child's parent as a resource argument, per the D3
amendment in
[`issues/recursive-structure-models.md`](../issues/recursive-structure-models.md),
so the arm owns `parent`'s cells and the loop names `parent` as the C local it
already maintains. The frame's own node is then not a resource argument of the
frame above it, so `Left` and `Right` carry it as the payload `identity`
beside the grandparent: `plug` rebuilds a node from the frame, and the frame
must say which node that is.

At the loop head the guard `parent != 0` refutes the `Top` arm's
`fact parent == 0`, which is what lets the body's proof `match` close `Top` by
contradiction. At the loop exit the same rule runs with the failed guard:
`parent == 0` refutes the `Left` and `Right` arms' `fact parent != 0`, so the
exit learns `c.model == Context::Top` and `unfold(c)` has its constructor
without a `match` after the loop.

The walk ends at the root, whose parent is null, and null is the only truthful
spelling of that position: `parent` is a parameter the body reassigned, so it
means its entry value on the return side, which is a different node. A
resource argument may therefore be the C null pointer constant, and the
produced instances are `pctx_at(result, 0)` and `ptree_at(result, 0)`. The
walk hands its final instances to those binders the way
`examples/modeled-binary-tree`'s descent does, by refolding them under the
produced names at the arguments the exit reached.

```c filename=loop_ascending_walk_to_root.c
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
verifying "loop_ascending_walk_to_root.c";

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
pass
```
