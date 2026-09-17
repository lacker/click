# one arm publication point per frontier

Selection, refutation, the cells the surviving arms agree on, and the naming of
the cells an `unfold` exposes are one mechanism. It runs at the eight frontiers
a proof passes through, listed in `docs/concepts/resources.md`, and each of
them decides from its own premises. This file states the same refutation at
every one of them over one resource, so a site that stops publishing fails here
rather than being found by the next proof shape that needs it.

`counted`'s `Count::Zero` arm states `fact n == 0`, so any premise that forces
`n` away from zero refutes it. `Count::Many` is then the one arm left, and
because it carries no fields the model has only one value: the equation itself
is published, which is what grants the arm's cells and lets `unfold` and proof
`match` name the constructor.

Two of the loops here never take their back edge toward the guard: `loop_exit`
holds `i` at zero and `guard_conjunct` never changes the conjunct it waits on,
so each runs forever whenever its guard is true on entry. They say so with the
`diverges` marker rather than with a measure, and the publication their site
checks still happens — `loop_exit`'s postcondition is proved at the guard-false
exit it does reach. The counted loops carry the distance to their bound.

```c filename=arm_publication_sites.c
struct cell {
    int32 value;
    struct cell* next;
};

int32 entry_lowering(struct cell *node, int32 n) {
    return 0;
}

int32 unfold_site(struct cell *node, int32 n) {
    return node->value;
}

void loop_head(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        node->value = 7;
        i = i + 1;
    }
}

void loop_exit(struct cell *node, int32 n) {
    int32 i;
    int32 t;
    i = 0;
    t = 0;
    while (i < n) {
        t = 1;
    }
}

void contract_return(struct cell *node, int32 n) {
    int32 t;
    t = n;
}

void back_edge(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}

void case_split(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}

void guard_conjunct(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (n != 0 && node->value < 5) {
        i = 1;
    }
}
```

```click
verifying "arm_publication_sites.c";

spec enum Count {
    Zero,
    Many,
}

resource counted(p: struct cell*, n: int32) {
    field model: Count;
    match model {
        Count::Zero => { fact n == 0; },
        Count::Many => { owns p->value; owns p->next; fact n != 0; },
    }
}

int32 entry_lowering(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    ensures c.model == Count::Many;
} by {
    execute();
    simp();
}

int32 unfold_site(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    ensures c.model == Count::Many;
} by {
    unfold(c);
    execute();
    let c = fold(counted(node, n), { model: Count::Many }, {});
    simp();
}

void loop_head(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    requires n <= 1000;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counted(node, n);
        invariant i >= 0;
        invariant i <= n;
        invariant n > 0;

        initialize by simp;
        preserve by {
            match c.model {
                Count::Zero => { contradiction(c.model == Count::Zero); },
                Count::Many => {
                    unfold(c);
                    step();
                    step();
                    let c = fold(counted(node, n), { model: Count::Many }, {});
                    close_invariants();
                },
            }
        }
    }
    execute();
    simp();
}

void loop_exit(struct cell* node, int32 n) diverges {
    owns c: counted(node, n);
    requires n >= 0;
    requires n <= 1000;
    ensures c.model == Count::Zero;
} by {
    step();
    step();
    step();
    step();
    loop diverges {
        owns c: counted(node, n);
        invariant i == 0;
        invariant n >= 0;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}

void contract_return(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires c.model != Count::Zero;
    owns node->next->value;
} by {
    execute();
    simp();
}

void back_edge(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    requires n <= 1000;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counted(node, n);
        invariant i >= 0;
        invariant i <= n;
        invariant n > 0;
        invariant c.model != Count::Zero;

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
                                intro();
                                intro();
                                intro();
                                simp();
                            } and {
                                both {
                                    arithmetic_certificate signed_int32 {
                                        premise 0: n > 0 => n > 0;
                                        premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                        premise 2: at(statement(3).entry, i) < at(statement(3).entry, n) => at(statement(3).entry, i) < at(statement(3).entry, n);
                                        premise 3: n <= 1000 => n <= 1000;
                                        interval_from_affine 0 (n) (1) (2147483647);
                                        interval_from_affine 3 (n) (-2147483648) (1000);
                                        interval_intersect 4, 5 (1) (1000);
                                        interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                        interval_subtract 6, 7 6 (-2147483646) (1000);
                                        interval_atom (1) (1) (1);
                                        interval_subtract 8, 9 8 (-2147483647) (999);
                                        affine_conclusion 2 10 => 0 <= ((n - at(statement(3).entry, i)) - 1);
                                        conclusion 11;
                                    }
                                } and {
                                    arithmetic_certificate signed_int32 {
                                        premise 0: n > 0 => n > 0;
                                        premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                        premise 2: n <= 1000 => n <= 1000;
                                        interval_from_affine 0 (n) (1) (2147483647);
                                        interval_from_affine 2 (n) (-2147483648) (1000);
                                        interval_intersect 3, 4 (1) (1000);
                                        interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                        interval_subtract 5, 6 5 (-2147483646) (1000);
                                        interval_atom (1) (1) (1);
                                        interval_subtract 7, 8 7 (-2147483647) (999);
                                        interval_subtract 5, 6 5 (-2147483646) (1000);
                                        trivial => 0 <= 0;
                                        affine_conclusion_pair 11 9 10 => ((n - at(statement(3).entry, i)) - 1) < (n - at(statement(3).entry, i));
                                        conclusion 12;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    execute();
    simp();
}

void case_split(struct cell* node, int32 n) {
    owns c: counted(node, n);
    requires n > 0;
    requires n <= 1000;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counted(node, n);
        invariant i >= 0;
        invariant i <= n;
        invariant n > 0;

        initialize by simp;
        preserve by {
            step();
            match c.model {
                Count::Zero => { contradiction(c.model == Count::Zero); },
                Count::Many => { close_invariants(); },
            }
        }
    }
    execute();
    simp();
}

void guard_conjunct(struct cell* node, int32 n) diverges {
    owns c: counted(node, n);
    requires n != 0;
} by {
    step();
    step();
    loop diverges {
        owns c: counted(node, n);
        invariant n != 0;

        initialize by simp;
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
