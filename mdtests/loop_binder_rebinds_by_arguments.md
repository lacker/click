# A loop binder is rebound by its arguments, not by the body's name

The body folds its result under a new name, `d`. The back edge selects the
loop binder the same way the head did — the one owned `counter(p)` — so `c`
names the instance the body called `d`, and the invariants are checked against
that instance's fresh model. No binder map is written anywhere.

```c filename=loop_binder_rebinds_by_arguments.c
struct cell { int32 value; };

void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_rebinds_by_arguments.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures c.count == old(c.count) + n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant c.count == old(c.count) + i;

        initialize by simp;
        preserve by {
            unfold(c);
            step();
            step();
            let d = fold(counter(p), { count: old(c.count) + i });
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
                                    premise 3: n <= 1000 => n <= 1000;
                                    interval_from_affine 0 (n) (0) (2147483647);
                                    interval_from_affine 3 (n) (-2147483648) (1000);
                                    interval_intersect 4, 5 (0) (1000);
                                    interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                    interval_subtract 6, 7 6 (-2147483647) (1000);
                                    interval_atom (1) (1) (1);
                                    interval_subtract 8, 9 8 (-2147483648) (999);
                                    affine_conclusion 2 10 => 0 <= ((n - at(statement(3).entry, i)) - 1);
                                    conclusion 11;
                                }
                            } and {
                                arithmetic_certificate signed_int32 {
                                    premise 0: n >= 0 => n >= 0;
                                    premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                    premise 2: n <= 1000 => n <= 1000;
                                    interval_from_affine 0 (n) (0) (2147483647);
                                    interval_from_affine 2 (n) (-2147483648) (1000);
                                    interval_intersect 3, 4 (0) (1000);
                                    interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                    interval_subtract 5, 6 5 (-2147483647) (1000);
                                    interval_atom (1) (1) (1);
                                    interval_subtract 7, 8 7 (-2147483648) (999);
                                    interval_subtract 5, 6 5 (-2147483647) (1000);
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
    have i == n by simp;
    execute();
    simp();
}
```

```expect
pass
```
