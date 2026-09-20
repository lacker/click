# A `simp() using` premise inside a `have` body names an arm binding

The uniform-scoping slices resolve a proof `match` arm's bindings the way a
`have` goal resolves them: in theorem arguments and `apply ... using` premises,
in `instantiate`, in `extract`
([`theorem_argument_arm_binding.md`](theorem_argument_arm_binding.md)), in a
`loop` written inside the arm
([`loop_clause_reads_arm_bindings.md`](loop_clause_reads_arm_bindings.md)),
and in the `initialize` and `preserve` bodies of that loop
([`loop_phase_body_reads_arm_bindings.md`](loop_phase_body_reads_arm_bindings.md)).

One site was missed: the premises of a `simp() using { ... }` or a
`normalize() using { ... }` written inside a `have` body that the smart planner
discharges. The goal of that `have` was materialized against the enclosing
proof's lexical bindings before planning, but the body's premises were lowered
without them, so the arm's name was read as an unbound C variable and the
premise was refused with `` `color` is not an algebraic binding in this
scope ``. The planner now lowers the goal and each premise with the same
bindings the goal is materialized with. The written spellings stay what the
certificate records and expansion prints, and `click audit` agrees with
`click verify` at every site here.

`peek` proves two `have`s in the arm, each citing the unfolded body fact that
names the arm's colour: one closed by `simp() using`, one by `normalize()
using`. `spin` puts the same `have` inside the `preserve` body of a loop
written in the arm, where the phase planner lowers it from a fresh root
carrying the arm's scope.

A premise must still be an exactly available fact. Naming the binding does
not make a premise true: `color_bit(color) == color_bit(color)` is refused as
not available, and a premise that reads memory through the arm's pointer
binding together with a pure call is a separate lowering gap
([`have_goal_reads_through_an_arm_binding.md`](have_goal_reads_through_an_arm_binding.md)).

```c filename=simp_using_binding.c
struct node { unsigned long word; struct node *left; };

unsigned long peek(struct node *p) {
    return p->word;
}

unsigned long spin(struct node *p, int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return p->word;
}
```

```click
verifying "simp_using_binding.c";

spec enum Color { Red, Black }

function color_bit(color: Color) -> int {
    match color {
        Color::Red => 0,
        Color::Black => 1,
    }
}

spec enum Tree {
    Empty,
    Node(struct node*, Color, Tree),
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, color, left_model) => {
            owns p->word;
            owns p->left;
            owns left: tree_at(p->left);
            fact p != 0;
            fact p == id;
            fact (p->word & 1) == color_bit(color);
            fact left.model == left_model;
        },
    }
}

unsigned long peek(struct node* p) {
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            let { left: l } = unfold(t);
            have color_bit(color) == (p->word & 1) by {
                simp() using { (p->word & 1) == color_bit(color); }
            }
            have (p->word & 1) == color_bit(color) by {
                normalize() using { (p->word & 1) == color_bit(color); }
            }
            step();
            let t = fold(tree_at(p), { model: Tree::Node(id, color, left_model) },
                { left: l });
            simp();
        },
    }
}

unsigned long spin(struct node* p, int n) {
    owns t: tree_at(p);
    requires n >= 0;
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, color, left_model) => {
            step();
            step();
            loop {
                decreases n - i;
                owns t: tree_at(p);
                invariant i >= 0;
                invariant i <= n;
                invariant t.model == Tree::Node(id, color, left_model);
                initialize by simp;
                preserve by {
                    have color_bit(color) == color_bit(color) by {
                        simp() using { t.model == Tree::Node(id, color, left_model); }
                    }
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
