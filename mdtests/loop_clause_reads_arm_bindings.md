# A loop written inside a proof `match` arm names the arm's bindings

A proof `match` on an instance's model binds the constructor's payloads for
the arm, and every term the arm writes may name them: `have` goals, theorem
arguments, and, when the arm contains a loop, that loop's clauses. Here the
loop's invariant states the binder's model as the constructor built from the
arm's pointer, integer, and model bindings, and the post-loop claim follows
from it. Loop clauses are lowered when the loop tactic runs at its frontier,
so the frontier's proof locals are resolved into them first, exactly as a
`have` goal at that point resolves the same names.

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
            owns p->left;
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
                decreases n - i;
                owns t: tree_at(p);
                invariant i >= 0;
                invariant i <= n;
                invariant t.model == Tree::Node(id, value, left_model);

                initialize by simp;
                preserve by {
                    step();
                    close_invariants by {
                        both {
                            apply(int32_increment_greater_equal_lower_bound(at(statement(3).entry, i), at(statement(3).entry, 0), at(statement(3).entry, n))) using {
                                at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                at(statement(3).entry, i) < at(statement(3).entry, n);
                            }
                        } and {
                            both {
                                intro();
                                apply(int32_increment_upper_bound(at(statement(3).entry, i), at(statement(3).entry, n))) using {
                                    at(statement(3).entry, i) < at(statement(3).entry, n);
                                }
                            } and {
                                both {
                                    intro();
                                    intro();
                                    simp();
                                } and {
                                    both {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: n >= 0 => n >= 0;
                                            premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                            premise 2: at(statement(3).entry, i) < at(statement(3).entry, n) => at(statement(3).entry, i) < at(statement(3).entry, n);
                                            interval_from_affine 0 (n) (0) (2147483647);
                                            interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                            interval_subtract 3, 4 3 (-2147483647) (2147483647);
                                            interval_atom (1) (1) (1);
                                            interval_subtract 5, 6 5 (-2147483648) (2147483646);
                                            affine_conclusion 2 7 => 0 <= ((n - at(statement(3).entry, i)) - 1);
                                            conclusion 8;
                                        }
                                    } and {
                                        arithmetic_certificate signed_int32 {
                                            premise 0: n >= 0 => n >= 0;
                                            premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                            interval_from_affine 0 (n) (0) (2147483647);
                                            interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                            interval_subtract 2, 3 2 (-2147483647) (2147483647);
                                            interval_atom (1) (1) (1);
                                            interval_subtract 4, 5 4 (-2147483648) (2147483646);
                                            interval_subtract 2, 3 2 (-2147483647) (2147483647);
                                            trivial => 0 <= 0;
                                            affine_conclusion_pair 8 6 7 => ((n - at(statement(3).entry, i)) - 1) < (n - at(statement(3).entry, i));
                                            conclusion 9;
                                        }
                                    }
                                }
                            }
                        }
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
pass
```
