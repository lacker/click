# An empty proof `match` arm inside `preserve` reports its frontier

A `preserve` body may open a proof `match` on the loop binder's model and
finish each arm's path separately. An arm with no tactics reaches the
region's end at once, with the body's statements still ahead, so that path
is unfinished. The frontier report names the arm's emptiness rather than
saying "after tactic 0 `match`", which reads as if the `match` itself were
the last thing that ran. The `Tree::Empty` arm here is refutable (the
invariant fixes the model at `Tree::Node`), and the proof that refutes it is
a `contradiction`; leaving the arm empty instead is the shape this fixture
pins.

```c filename=loop_clause_reads_arm_bindings.c
struct node { int value; struct node *left; };

int spin(struct node *p, int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return p->value;
}
```

```click
verifying "loop_clause_reads_arm_bindings.c";

spec enum Tree {
    Empty,
    Node(struct node*, int, Tree),
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, value, left_model) => {
            owns p->value;
            owns &p->left;
            owns left: tree_at(p->left);
            fact p != 0;
            fact p == id;
            fact p->value == value;
            fact left.model == left_model;
        },
    }
}

int spin(struct node* p, int n) {
    requires n >= 0;
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, value, left_model) => {
            step();
            step();
            loop {
                owns t: tree_at(p);
                invariant i >= 0;
                invariant i <= n;
                invariant t.model == Tree::Node(id, value, left_model);

                initialize by simp;
                preserve by {
                    match t.model {
                        Tree::Empty => { },
                        Tree::Node(id2, value2, left2) => {
                            step();
                            close_invariants();
                        },
                    }
                }
            }
            step();
            simp();
        },
    }
}
```

```expect
fail: after tactic 0 `match, inside an arm with no tactics`; still ahead on this path: the body's end. Already complete: 1 at the body's end
```
