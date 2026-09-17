# A proof `match` runs at a loop-body frontier

At an arbitrary loop head a binder's model is a fresh symbolic value, so
`unfold(c)` has no constructor to open. A proof `match` on `c.model` inside
`preserve` supplies one: each arm's path gets the constructor equation with
fresh bindings, and the arm that the invariants exclude closes by
`contradiction` without running an iteration.

Each arm runs to the loop's own boundary rather than to function exit. Nothing
joins the arms: the live arm refolds its own instance and closes the invariants
on its own path, so the back edge sees the resource state that arm produced.

```c filename=loop_body_proof_match.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return node->value;
}
```

```click
verifying "loop_body_proof_match.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    requires c.model != Maybe::None;
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);
        invariant c.model != Maybe::None;

        initialize by simp;
        preserve by {
            match c.model {
                Maybe::None => { contradiction(c.model == Maybe::None); },
                Maybe::Some(value) => {
                    have Maybe::Some(value) == old(c.model) by {
                        simp() using { c.model == Maybe::Some(value); c.model == old(c.model); }
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Maybe::Some(value) });
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
                                        intro();
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
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
