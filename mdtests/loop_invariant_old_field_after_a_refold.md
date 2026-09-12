# a loop invariant's `old(t.model)` after the body refolded `t`

`walk` holds one modelled instance, unfolds it to read a cell, folds it back
under the same name, and then runs a loop that carries it. Its one invariant is
the instance's entry model, `t.model == old(t.model)`, which is what every
ascent and fixup loop states when the tree it walks must end up related to the
tree it started from.

Take the `unfold` and the matching `fold` away and the same invariant lowers:
the entry instance is the contract's, and `old(t.model)` reads it. Put them
back and lowering the invariant at the loop's entry runs out of paths:

```
`walk.contract (loop 0 invariant 0 entry)` proof 0: could not lower pure goal:
the kernel lowering hit Paths
```

This is package C3's blocker on the Linux insert fixup. `__rb_insert` must
unfold `rb_at(node)` before the loop — the first statement is `parent =
rb_red_parent(node)`, and the parent word's value is a fact of the node's own
arm — and the fixup loop's invariant is that the in-order sequence of
`plug(c.model, t.model)` is the one the function was given. Naming that entry
sequence through `old(t.model)` is refused here; naming it through the entry
`match` arm's constructor, which the arm bindings spell out, is the shape
[`rb_insert_color.md`](rb_insert_color.md) uses instead.

It is the focused instance that matters, not `old` itself: in the insert
fixture `old(c.model)` on the never-unfolded context lowers in the same
invariant that `old(t.model)` refuses.

```c filename=walk.c
struct node {
    struct node *parent;
    int value;
};

int walk(struct node *n)
{
    struct node *p = n->parent;
    int i = 0;
    while (i < 1) {
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "walk.c";

spec enum Tree {
    Empty,
    Node(struct node*, struct node*, int),
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(identity, parent, value) => {
            owns p->parent;
            owns p->value;
            fact p != 0;
            fact p == identity;
            fact p->parent == parent;
            fact p->value == value;
        },
    }
}

int walk(struct node* n) {
    consumes t: tree_at(n);
    requires t.model != Tree::Empty;
    produces u: tree_at(n);
    ensures result == 0;
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(identity, node_parent, value) => {
            unfold(t);
            step();
            step();
            let t = fold(tree_at(n), { model: old(t.model) });
            step();
            step();
            loop {
                owns t: tree_at(n);
                invariant t.model == old(t.model);
            }
            let u = fold(tree_at(n), { model: t.model });
            execute();
            simp();
        },
    }
}
```

```expect
fail: could not lower pure goal: the kernel lowering hit Paths
```
