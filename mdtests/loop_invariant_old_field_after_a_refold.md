# a loop invariant's `old(t.model)` after the body refolded `t`

`walk` holds one modelled instance, unfolds it inside its entry `match` arm to
read a cell, folds it back under the same name, and then runs a loop that
carries it. Its one invariant is the instance's entry model,
`t.model == old(t.model)`, which is what every ascent and fixup loop states
when the tree it walks must end up related to the tree it started from.

The unfold here precedes the proof's first `step()`, so the C execution starts
from a state that does not hold `t` at all, and the refold leaves a later
generation of the instance there. A frontier loop used to resolve `old(...)`
in its clauses against that execution-start state instead of the contract's
checked entry state, so lowering the invariant at the loop's entry ran out of
paths:

```
`walk.contract (loop 0 invariant 0 entry)` proof 0: could not lower pure goal:
the kernel lowering hit Paths
```

This is the shape package C3 needs on the Linux insert fixup. `__rb_insert`
must unfold `rb_at(node)` before the loop — the first statement is
`parent = rb_red_parent(node)`, and the parent word's value is a fact of the
node's own arm — and the fixup loop's invariant is that the in-order sequence
of `plug(c.model, t.model)` is the one the function was given. Naming that
entry sequence through `old(t.model)` lowers here; naming it through the entry
`match` arm's constructor, which the arm bindings spell out, is the other
spelling, and [`rb_insert_color.md`](rb_insert_color.md) uses that one.

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
    owns t: tree_at(n);
    requires t.model != Tree::Empty;
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
            execute();
            simp();
        },
    }
}
```

```termination
pending: unranked loop
```

```expect
pass
```
