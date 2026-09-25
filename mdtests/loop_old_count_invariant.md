# loop invariant lowers old-state stdlib count

This checks that `old(...)` in a loop invariant re-elaborates its body in the
entry-state spec context. In particular, `old(count(...))` reaches the stdlib
`count` function and keeps its `.fold` as pure spec/core over entry memory.

```c filename=loop_old_count_invariant.c
int32 loop_old_count_invariant(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_old_count_invariant.c";

int32 loop_old_count_invariant(int32 p[3]) {
    requires viewable(p[0..3]);
    ensures result_value: result == 3;
} by {
    step();
    step();
    loop {
        decreases (3 - i);
        invariant i >= 0 and i <= 3;
        invariant old(count(p, 0, 3, p[0])) == old(count(p, 0, 3, p[0]));
        initialize by {
            have i >= 0 and i <= 3 by {
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have old(count(p, 0, 3, p[0])) == old(count(p, 0, 3, p[0])) by {
                normalize();
            }
        }
        preserve by {
            mark iteration;
            step();
            have i >= 0 and i <= 3 by {
                both {
                    extract(at(statement(3).entry, i) <= at(statement(3).entry, 3));
                    extract(at(statement(3).entry, i) >= at(statement(3).entry, 0));
                    apply(int32_increment_greater_equal_lower_bound(at(statement(3).entry, i), at(statement(3).entry, 0), at(statement(3).entry, 3))) using {
                        at(statement(3).entry, i) >= at(statement(3).entry, 0);
                        at(statement(3).entry, i) < at(statement(3).entry, 3);
                    }
                } and {
                    extract(at(statement(3).entry, i) <= at(statement(3).entry, 3));
                    extract(at(statement(3).entry, i) >= at(statement(3).entry, 0));
                    apply(int32_increment_upper_bound(at(statement(3).entry, i), at(statement(3).entry, 3))) using {
                        at(statement(3).entry, i) < at(statement(3).entry, 3);
                    }
                }
            }
            close_invariants by {
                extract(i >= 0);
                extract(i <= 3);
                extract(at(statement(3).entry, i) >= at(statement(3).entry, 0));
                extract(at(statement(3).entry, i) <= at(statement(3).entry, 3));
                both {
                    normalize();
                } and {
                    both {
                        arithmetic_certificate signed_int32 {
                            premise 0: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                            premise 1: at(statement(3).entry, i) < at(statement(3).entry, 3) => at(statement(3).entry, i) < at(statement(3).entry, 3);
                            interval_atom (0) (0) (0);
                            interval_from_affine 0 (at(statement(3).entry, i)) (0) (2147483647);
                            interval_from_affine 1 (at(statement(3).entry, i)) (-2147483648) (2);
                            interval_intersect 3, 4 (0) (2);
                            interval_subtract 2, 5 2 (-2) (0);
                            interval_atom (2) (2) (2);
                            interval_add_bounded 6, 7 (0) (2);
                            affine_conclusion 1 8 => 0 <= ((0 - at(statement(3).entry, i)) + 2);
                            conclusion 9;
                        }
                    } and {
                        arithmetic_certificate signed_int32 {
                            premise 0: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                            premise 1: at(statement(3).entry, i) < at(statement(3).entry, 3) => at(statement(3).entry, i) < at(statement(3).entry, 3);
                            interval_atom (0) (0) (0);
                            interval_from_affine 0 (at(statement(3).entry, i)) (0) (2147483647);
                            interval_from_affine 1 (at(statement(3).entry, i)) (-2147483648) (2);
                            interval_intersect 3, 4 (0) (2);
                            interval_subtract 2, 5 2 (-2) (0);
                            interval_atom (2) (2) (2);
                            interval_add_bounded 6, 7 (0) (2);
                            interval_subtract 2, 5 2 (-2) (0);
                            interval_atom (3) (3) (3);
                            interval_add_bounded 9, 10 (1) (3);
                            trivial => 0 <= 0;
                            affine_conclusion_pair 12 8 11 => ((0 - at(statement(3).entry, i)) + 2) < ((0 - at(statement(3).entry, i)) + 3);
                            conclusion 13;
                        }
                    }
                }
            }
        }
    }
    step();
    have result == 3 by {
        extract(at(loop(0).exit, i) <= at(loop(0).exit, 3));
        extract(at(loop(0).exit, i) >= at(loop(0).exit, 0));
        apply(int32_le_and_not_lt_implies_eq(at(loop(0).exit, i), at(loop(0).exit, 3))) using {
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
        }
    }
    assumption();
}
```

```expect
pass
```
