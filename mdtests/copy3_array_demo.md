# copy3 verifies a small array-copy loop

This is a compact launch-shaped example: two array parameters, a fixed pointer
loop, reads from source memory, writes to destination memory, explicit
source/destination separation, loop invariants, and `old(...)`
postconditions.

```c filename=copy3.c
int32 copy3(int32 dst[3], int32 src[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        dst[i] = src[i];
        i = i + 1;
    }
    return dst[2];
}
```

```click
verifying "copy3.c";

int32 copy3(int32 dst[3], int32 src[3]) {
    requires viewable(dst[0..3]);
    requires viewable(src[0..3]);
    consumes dst[0..3];
    views src[0..3];
    requires separate(memory(dst[0..3]), memory(src[0..3]));
    ensures copies_first: dst[0] == old(src[0]);
    ensures copies_second: dst[1] == old(src[1]);
    ensures copies_third: dst[2] == old(src[2]);
    ensures returns_third: result == old(src[2]);
} by {
    step();
    step();
    loop {
        decreases (3 - i);
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) };
        invariant forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) };
        initialize by {
            have i >= 0 and i <= 3 by {
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) } by {
                intro();
                intro();
                normalize();
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                enumerate();
            }
        }
        preserve by {
            have 0 <= i;
            mark iteration;
            step();
            step();
            have forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) } by {
                intro(); intro();
                extract(0 <= k); extract(k < 3);
                instantiate(at(iteration, forall (j: int32) {
                    0 <= j and j < 3 implies src[j] == old(src[j])
                }), k) using { 0 <= k; k < 3; };
                transport(at(iteration, src[k]) == old(src[k]), src[k] == old(src[k])) using {
                    at(iteration, src[k]) == old(src[k]);
                    separate(memory(dst[0..3]), memory(src[0..3]));
                    0 <= k; k < 3;
                    0 <= at(iteration, i); at(iteration, i) < 3;
                };
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                if to_integer(k) < to_integer((i - 1)) {
                    have to_integer(k) != to_integer((i - 1)) by {
                        have to_integer(k) < to_integer((i - 1)) by {
                            assumption();
                        }
                        intro();
                        arithmetic_certificate {
                            premise 0: to_integer(k) < to_integer((i - 1)) => to_integer(k) < to_integer((i -
                                1));
                            premise 1: to_integer(k) == to_integer((i - 1)) => to_integer(k) == to_integer((i -
                                1));
                            less_equal_from_equal 1 reverse => to_integer((i - 1)) <= to_integer(k);
                            add 0, 2 => (to_integer(k) + to_integer((i - 1))) < (to_integer((i - 1)) +
                                to_integer(k));
                            trivial => -1 <= 0;
                            equal_from_bounds 3, 4 => false == true;
                            conclusion 5;
                        }
                    }
                    instantiate(forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry, k) < at(region(3).entry, i) implies at(region(3).entry, dst[k]) == old(src[k]) }, k);
                    transport(at(region(3).entry, dst[k]) == old(src[k]), dst[k] == old(src[k])) using {
                        at(region(3).entry, dst[k]) == old(src[k]);
                    };
                } else {
                    have to_integer(k) == to_integer((i - 1)) by {
                        have to_integer(k) <= to_integer((i - 1)) by {
                            arithmetic_certificate signed_int32 {
                                premise 0: at(region(3).entry, i) < at(region(3).entry, 3) =>
                                    at(region(3).entry, i) < at(region(3).entry, 3);
                                premise 1: k < i => k < i;
                                premise 2: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                    at(region(3).entry, i) >= at(region(3).entry, 0);
                                interval_from_affine 2 (at(region(3).entry, i)) (0) (2147483647);
                                interval_from_affine 0 (at(region(3).entry, i)) (-2147483648) (2);
                                interval_intersect 3, 4 (0) (2);
                                interval_atom (1) (1) (1);
                                interval_add_bounded 5, 6 (1) (3);
                                affine_premise 1 7 7 => k < i;
                                conclusion 8;
                            }
                        }
                        have to_integer(k) == (to_integer(i) - 1) by {
                            have to_integer(k) <= (to_integer(i) - 1) by {
                                arithmetic_certificate {
                                    negated_goal => (to_integer(i) - 1) < to_integer(k);
                                    premise 0: to_integer(k) < to_integer(i) => to_integer(k) < to_integer(i);
                                    add 0, 1 => ((to_integer(i) - 1) + 1 + (to_integer(k) + 1)) <=
                                        (to_integer(k) + to_integer(i));
                                    conclusion 2;
                                }
                            }
                            have (to_integer(i) - 1) <= to_integer(k) by {
                                have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                    arithmetic_certificate {
                                        negated_goal => (to_integer(at(region(3).entry, i)) + 1) < -2147483648;
                                        premise 0: 0 <= to_integer(at(region(3).entry, i)) => 0 <=
                                            to_integer(at(region(3).entry, i));
                                        add 0, 1 => (to_integer(at(region(3).entry, i)) + 1 + 0) < (-2147483648
                                            + to_integer(at(region(3).entry, i)));
                                        conclusion 2;
                                    }
                                }
                                have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                    arithmetic_certificate {
                                        negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) + 1);
                                        premise 0: to_integer(at(region(3).entry, i)) < 3 =>
                                            to_integer(at(region(3).entry, i)) < 3;
                                        add 0, 1 => (2147483647 + 1 + (to_integer(at(region(3).entry, i)) + 1))
                                            <= (to_integer(at(region(3).entry, i)) + 1 + 3);
                                        conclusion 2;
                                    }
                                }
                                have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                    arithmetic_certificate rules {
                                        premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) =>
                                            -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
                                        premise 1: (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 =>
                                            (to_integer(at(region(3).entry, i)) + 1) <= 2147483647;
                                        integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                            (to_integer(at(region(3).entry, i)) + 1);
                                        conclusion 0;
                                    }
                                }
                                arithmetic_certificate {
                                    negated_goal => to_integer(k) < (to_integer(i) - 1);
                                    premise 0: to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) =>
                                        to_integer(i) == (to_integer(at(region(3).entry, i)) + 1);
                                    less_equal_from_equal 1 => to_integer(i) <= (to_integer(at(region(3).entry,
                                        i)) + 1);
                                    premise 1: to_integer(at(region(3).entry, i)) <= to_integer(k) =>
                                        to_integer(at(region(3).entry, i)) <= to_integer(k);
                                    add 0, 2 => (to_integer(k) + to_integer(i)) < ((to_integer(i) - 1) +
                                        (to_integer(at(region(3).entry, i)) + 1));
                                    add 4, 3 => (to_integer(k) + to_integer(i) + to_integer(at(region(3).entry,
                                        i))) < ((to_integer(i) - 1) + (to_integer(at(region(3).entry, i)) + 1) +
                                        to_integer(k));
                                    conclusion 5;
                                }
                            }
                            arithmetic_certificate {
                                premise 0: to_integer(k) <= (to_integer(i) - 1) => to_integer(k) <=
                                    (to_integer(i) - 1);
                                premise 1: (to_integer(i) - 1) <= to_integer(k) => (to_integer(i) - 1) <=
                                    to_integer(k);
                                equal_from_bounds 0, 1 => to_integer(k) == (to_integer(i) - 1);
                                conclusion 2;
                            }
                        }
                        assumption();
                    }
                    instantiate(forall (k: int32) { at(region(3).entry, 0) <= at(region(3).entry, k) and at(region(3).entry, k) < at(region(3).entry, 3) implies at(region(3).entry, src[k]) == old(src[k]) }, k) using {
                        0 <= k;
                        at(region(3).entry, i) < at(region(3).entry, 3);
                        not to_integer(k) < to_integer((i - 1));
                        k < i;
                        at(region(3).entry, i) <= at(region(3).entry, 3);
                        at(region(3).entry, i) >= at(region(3).entry, 0);
                        to_integer(k) == to_integer((i - 1));
                    };
                    transport(at(region(3).entry, src[k]) == old(src[k]), dst[k] == old(src[k])) using {
                        at(region(3).entry, src[k]) == old(src[k]);
                        to_integer(k) == to_integer((i - 1));
                    };
                }
            }
            close_invariants() by {
                both {
                    both {
                        extract(at(region(3).entry, i) >= at(region(3).entry, 0));
                        arithmetic_certificate signed_int32 {
                            premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) => at(region(3).entry,
                                i) >= at(region(3).entry, 0);
                            premise 1: at(region(3).entry, i) < at(region(3).entry, 3) => at(region(3).entry, i)
                                < at(region(3).entry, 3);
                            interval_from_affine 0 (at(region(3).entry, i)) (0) (2147483647);
                            interval_from_affine 1 (at(region(3).entry, i)) (-2147483648) (2);
                            interval_intersect 2, 3 (0) (2);
                            interval_atom (1) (1) (1);
                            interval_add_bounded 4, 5 (1) (3);
                            trivial => -1 <= 0;
                            add 0, 7 => ((at(region(3).entry, 0) + -1) as int32) <= ((at(region(3).entry, i) +
                                0) as int32);
                            affine_conclusion 8 6 => (i as int32) >= (0 as int32);
                            conclusion 9;
                        }
                    } and {
                        extract(at(region(3).entry, i) >= at(region(3).entry, 0));
                        arithmetic_certificate signed_int32 {
                            premise 0: at(region(3).entry, i) < at(region(3).entry, 3) => at(region(3).entry, i)
                                < at(region(3).entry, 3);
                            interval_from_affine 0 (at(region(3).entry, i)) (-2147483648) (2);
                            interval_atom (1) (1) (1);
                            interval_add_bounded 1, 2 (-2147483647) (3);
                            affine_conclusion 0 3 => (i as int32) <= (3 as int32);
                            conclusion 4;
                        }
                    }
                } and {
                    both {
                        intro();
                        assumption();
                    } and {
                        both {
                            intro();
                            intro();
                            assumption();
                        } and {
                            both {
                                have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                    arithmetic_certificate {
                                        premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                            at(region(3).entry, i) >= at(region(3).entry, 0);
                                        trivial => -2147483649 <= 0;
                                        add 0, 1 => (at(region(3).entry, 0) + -2147483649) <=
                                            (at(region(3).entry, to_integer(i)) + 0);
                                        conclusion 2;
                                    }
                                }
                                have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                    arithmetic_certificate {
                                        premise 0: at(region(3).entry, i) < at(region(3).entry, 3) =>
                                            at(region(3).entry, i) < at(region(3).entry, 3);
                                        trivial => -2147483644 <= 0;
                                        add 0, 1 => (at(region(3).entry, to_integer(i)) + -2147483644) <
                                            (at(region(3).entry, 3) + 0);
                                        conclusion 2;
                                    }
                                }
                                have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                    arithmetic_certificate rules {
                                        premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) =>
                                            -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
                                        premise 1: (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 =>
                                            (to_integer(at(region(3).entry, i)) + 1) <= 2147483647;
                                        integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                            (to_integer(at(region(3).entry, i)) + 1);
                                        conclusion 0;
                                    }
                                }
                                arithmetic_certificate {
                                    premise 0: at(region(3).entry, i) < at(region(3).entry, 3) =>
                                        at(region(3).entry, i) < at(region(3).entry, 3);
                                    premise 1: to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) =>
                                        to_integer(i) == (to_integer(at(region(3).entry, i)) + 1);
                                    less_equal_from_equal 1 => to_integer(i) <= (to_integer(at(region(3).entry,
                                        i)) + 1);
                                    add 0, 2 => (at(region(3).entry, to_integer(i)) + to_integer(i)) <
                                        (at(region(3).entry, 3) + (to_integer(at(region(3).entry, i)) + 1));
                                    conclusion 3;
                                }
                            } and {
                                have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                    arithmetic_certificate {
                                        premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                            at(region(3).entry, i) >= at(region(3).entry, 0);
                                        trivial => -2147483649 <= 0;
                                        add 0, 1 => (at(region(3).entry, 0) + -2147483649) <=
                                            (at(region(3).entry, to_integer(i)) + 0);
                                        conclusion 2;
                                    }
                                }
                                have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                    arithmetic_certificate {
                                        premise 0: at(region(3).entry, i) < at(region(3).entry, 3) =>
                                            at(region(3).entry, i) < at(region(3).entry, 3);
                                        trivial => -2147483644 <= 0;
                                        add 0, 1 => (at(region(3).entry, to_integer(i)) + -2147483644) <
                                            (at(region(3).entry, 3) + 0);
                                        conclusion 2;
                                    }
                                }
                                have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                    arithmetic_certificate rules {
                                        premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) =>
                                            -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
                                        premise 1: (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 =>
                                            (to_integer(at(region(3).entry, i)) + 1) <= 2147483647;
                                        integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                            (to_integer(at(region(3).entry, i)) + 1);
                                        conclusion 0;
                                    }
                                }
                                arithmetic_certificate {
                                    premise 0: to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) =>
                                        to_integer(i) == (to_integer(at(region(3).entry, i)) + 1);
                                    less_equal_from_equal 0 reverse => (to_integer(at(region(3).entry, i)) + 1)
                                        <= to_integer(i);
                                    conclusion 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    have dst[0] == old(src[0]) by {
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 0) using {
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
        };
        assumption();
    }
    have dst[1] == old(src[1]) by {
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 1) using {
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
        };
        assumption();
    }
    have dst[2] == old(src[2]) by {
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 2) using {
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
        };
        assumption();
    }
    step();
    have dst[0] == old(src[0]) by {
        assumption();
    }
    have dst[1] == old(src[1]) by {
        assumption();
    }
    have dst[2] == old(src[2]) by {
        assumption();
    }
    have result == old(src[2]) by {
        assumption();
    }
    assumption();
    assumption();
    assumption();
    assumption();
}
```

```expect
pass
```
