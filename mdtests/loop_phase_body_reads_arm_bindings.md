# A loop phase body written inside a proof `match` arm names the arm's bindings

[`loop_clause_reads_arm_bindings.md`](loop_clause_reads_arm_bindings.md) resolves
the proof scope into a loop's *clauses*. Its `initialize` and `preserve`
*bodies* are written in the same scope and must resolve the same names: a
`have` inside a phase body is as much part of the enclosing arm as a `have`
written beside the `loop`.

Each phase runs as its own sub-proof, built from a fresh root at the loop's
entry or body-entry state. A fresh root carries no proof locals, so before
this fixture a phase body that named an arm binding was refused with
"`left_model` is not an algebraic binding in this scope", and, where the goal
lowered to nothing at all, with the contentless "body did not construct a
completed proof object". The scope is now attached to all three phase roots:
the per-invariant entry planner, the automatic preservation walk, and the
written `preserve` body.

What is *not* a trigger, checked while reducing this: whether the loop is
ranked, and whether an earlier `have` in the same body was proved by `simp`.
A `simp`-proved `have` kept working only because its goal named no binding, and
a `have` whose goal names none still works after one that does. The same `have`
written beside the `loop` in the arm, rather than in a phase body, always
worked. Both loops below carry a measure, as every loop must; they differ in
which phase bodies name the arm's bindings, `spin` from `initialize` and
`preserve` and `spin_ranked` only from `preserve`, and both phase bodies prove
the same definitional equation by `unfold` and `normalize`.

`spin`'s `initialize` is written in the shape the entry planner checks: one
`have` per invariant, then `assumption()`. The helper `have` that needs the
arm's bindings is nested inside the invariant's own body, which is where a
phase body of any depth now resolves them.

```c filename=loop_phase_body_reads_arm_bindings.c
struct node { int value; struct node *left; };

int spin(struct node *p, int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return p->value;
}

int spin_ranked(struct node *p, int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return p->value;
}
```

```click
verifying "loop_phase_body_reads_arm_bindings.c";

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

function head_value(m: Tree) -> int32 {
    match m {
        Tree::Empty => 0,
        Tree::Node(id, value, left_model) => value,
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
                decreases n - i;
                invariant i >= 0;
                invariant i <= n;
                invariant t.model == Tree::Node(id, value, left_model);

                initialize by {
                    have i >= 0 by { normalize(); }
                    have i <= n by {
                        apply(int32_ge_implies_reversed_le(n, 0)) using { n >= 0; }
                    }
                    have t.model == Tree::Node(id, value, left_model) by {
                        have head_value(Tree::Node(id, value, left_model)) == value by {
                            unfold(head_value(Tree::Node(id, value, left_model)));
                            normalize();
                        }
                        assumption();
                    }
                    assumption();
                }
                preserve by {
                    have head_value(Tree::Node(id, value, left_model)) == value by {
                        unfold(head_value(Tree::Node(id, value, left_model)));
                        normalize();
                    }
                    have 0 <= n - i - 1 by { arithmetic() using { i < n; i >= 0; n >= 0; } }
                    have n - i - 1 < n - i by { arithmetic() using { i < n; i >= 0; n >= 0; } }
                    step();
                    close_invariants();
                }
            }
            step();
            simp();
        },
    }
}

int spin_ranked(struct node* p, int n) {
    requires n >= 0;
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures n >= 0;
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, value, left_model) => {
            step();
            step();
            loop {
                owns t: tree_at(p);
                decreases n - i;
                invariant i >= 0;
                invariant i <= n;

                initialize by simp;
                preserve by {
                    have head_value(Tree::Node(id, value, left_model)) == value by {
                        unfold(head_value(Tree::Node(id, value, left_model)));
                        normalize();
                    }
                    step();
                    close_invariants();
                }
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
