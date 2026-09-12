# Integer range fold summation

The loop invariant tracks the exact prefix sum and bounds it using the element
range, which proves the intermediate machine addition stays within `int32`.
At loop exit, `i <= n` together with `not i < n` establishes `i == n`; the
final proof rewrites that endpoint explicitly before returning so the exact
prefix invariant matches the full range in the postcondition.

```c filename=integer_sum_range_fold.c
int32 sum(int32 a[], int32 n) {
    int32 total;
    int32 i;
    total = 0;
    i = 0;
    while (i < n) {
        total = total + a[i];
        i = i + 1;
    }
    return total;
}
```

```click
verifying "integer_sum_range_fold.c";

int32 sum(int32 a[], int32 n) {
    requires 0 <= n and n <= 1000;
    requires loadable(a[0..n]);
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies
            -1000 <= a[k] and a[k] <= 1000
    };
    ensures result_sum: to_integer(result) ==
        (0..n).fold(0, |acc, k| { acc + to_integer(a[k]) });
} by {
    step();
    step();
    step();
    step();
    have 0 <= 0 by { simp(); }
    have (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) == 0 by {
        apply(integer_range_fold_empty(
            (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) })
        )) using {
            0 <= 0;
        }
    }
    have 0 == (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) by {
        normalize() using {
            (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) == 0;
        }
    }
    have 0 <= (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) by {
        arithmetic_certificate {
            premise 0: (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) == 0 =>
                (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) == 0;
            eq_to_le 0 reverse =>
                0 <= (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) });
            conclusion 1;
        }
    }
    have (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) <= 0 by {
        arithmetic_certificate {
            premise 0: (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) == 0 =>
                (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) == 0;
            eq_to_le 0 =>
                (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) <= 0;
            conclusion 1;
        }
    }
    loop as sum {
        invariant 0 <= i;
        invariant i <= n;
        invariant to_integer(total) ==
            (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
        invariant -1000 * to_integer(i) <=
            (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
        invariant (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) <=
            1000 * to_integer(i);

        initialize by simp;
        preserve by {
            have -1000 <= a[i] and a[i] <= 1000 by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies
                        -1000 <= a[k] and a[k] <= 1000
                }, i) using {
                    0 <= i;
                    i < n;
                }
                assumption();
            }
            have -1000 <= to_integer(a[i]) by {
                apply(int32_less_equal_to_integer(-1000, a[i])) using {
                    -1000 <= a[i];
                }
                simp();
            }
            have to_integer(a[i]) <= 1000 by {
                apply(int32_less_equal_to_integer(a[i], 1000)) using {
                    a[i] <= 1000;
                }
                simp();
            }
            have 0 <= to_integer(i) by {
                apply(int32_less_equal_to_integer(0, i)) using {
                    0 <= i;
                }
                simp();
            }
            have to_integer(i) <= 1000 by {
                have to_integer(i) <= to_integer(n) by {
                    apply(int32_less_equal_to_integer(i, n)) using {
                        i <= n;
                    }
                }
                have to_integer(n) <= 1000 by {
                    apply(int32_less_equal_to_integer(n, 1000)) using {
                        n <= 1000;
                    }
                    simp();
                }
                simp() using {
                    to_integer(i) <= to_integer(n);
                    to_integer(n) <= 1000;
                }
            }
            have -1000 * to_integer(i) <= to_integer(total) by {
                simp() using {
                    to_integer(total) ==
                        (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                    -1000 * to_integer(i) <=
                        (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                }
            }
            have to_integer(total) <= 1000 * to_integer(i) by {
                simp() using {
                    to_integer(total) ==
                        (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                    (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) <=
                        1000 * to_integer(i);
                }
            }
            have -1000 * to_integer(i) - 1000 <=
                to_integer(total) + to_integer(a[i]) by {
                simp() using {
                    -1000 * to_integer(i) <= to_integer(total);
                    -1000 <= to_integer(a[i]);
                }
            }
            have to_integer(total) + to_integer(a[i]) >=
                -2147483648 by {
                simp() using {
                    -1000 * to_integer(i) - 1000 <=
                        to_integer(total) + to_integer(a[i]);
                    to_integer(i) <= 1000;
                }
            }
            have to_integer(total) + to_integer(a[i]) <=
                1000 * to_integer(i) + 1000 by {
                simp() using {
                    to_integer(total) <= 1000 * to_integer(i);
                    to_integer(a[i]) <= 1000;
                }
            }
            have to_integer(total) + to_integer(a[i]) <=
                2147483647 by {
                simp() using {
                    to_integer(total) + to_integer(a[i]) <=
                        1000 * to_integer(i) + 1000;
                    to_integer(i) <= 1000;
                }
            }
            have defined(a[i]) by {
                simp() using {
                    loadable(a[0..n]);
                    0 <= i;
                    i < n;
                }
            }
            have defined(total + a[i]) by {
                apply(int32_add_defined_by_integer_bounds(total, a[i])) using {
                    to_integer(total) + to_integer(a[i]) >= -2147483648;
                    to_integer(total) + to_integer(a[i]) <= 2147483647;
                }
                both { simp(); } and { assumption(); }
            }
            have to_integer(total + a[i]) ==
                to_integer(total) + to_integer(a[i]) by {
                apply(int32_add_to_integer(total, a[i])) using {
                    defined(total + a[i]);
                }
            }
            have to_integer(total + a[i]) ==
                (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) +
                    to_integer(a[i]) by {
                simp() using {
                    to_integer(total + a[i]) ==
                        to_integer(total) + to_integer(a[i]);
                    to_integer(total) ==
                        (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                }
            }
            have i < 2147483647 by {
                have i < 1000 by {
                    apply(int32_lt_le_transitive(i, n, 1000)) using {
                        i < n;
                        n <= 1000;
                    }
                }
                have 1000 < 2147483647 by {
                    simp();
                }
                apply(int32_lt_transitive(i, 1000, 2147483647)) using {
                    i < 1000;
                    1000 < 2147483647;
                }
            }
            have defined(i + 1) by {
                apply(int32_increment_below_max_is_defined(i));
                assumption();
            }
            have to_integer(i + 1) == to_integer(i) + to_integer(1) by {
                apply(int32_add_to_integer(i, 1));
            }
            have -1000 * to_integer(i + 1) <=
                to_integer(total) + to_integer(a[i]) by {
                simp() using {
                    -1000 * to_integer(i) - 1000 <=
                        to_integer(total) + to_integer(a[i]);
                    to_integer(i + 1) == to_integer(i) + to_integer(1);
                }
            }
            have -1000 * to_integer(i + 1) <= to_integer(total + a[i]) by {
                simp() using {
                    -1000 * to_integer(i + 1) <=
                        to_integer(total) + to_integer(a[i]);
                    to_integer(total + a[i]) ==
                        to_integer(total) + to_integer(a[i]);
                }
            }
            have to_integer(total) + to_integer(a[i]) <=
                1000 * to_integer(i + 1) by {
                simp() using {
                    to_integer(total) + to_integer(a[i]) <=
                        1000 * to_integer(i) + 1000;
                    to_integer(i + 1) == to_integer(i) + to_integer(1);
                }
            }
            have to_integer(total + a[i]) <=
                1000 * to_integer(i + 1) by {
                simp() using {
                    to_integer(total + a[i]) ==
                        to_integer(total) + to_integer(a[i]);
                    to_integer(total) + to_integer(a[i]) <=
                        1000 * to_integer(i + 1);
                }
            }
            step();
            step();
            have i == at(statement(5).entry, i) + 1 by { simp(); }
            have (0..(at(statement(5).entry, i) + 1)).fold(
                0, |acc, k| { acc + to_integer(a[k]) }
            ) ==
                (0..at(statement(5).entry, i)).fold(
                    0, |acc, k| { acc + to_integer(a[k]) }
                ) + to_integer(a[at(statement(5).entry, i)]) by {
                apply(integer_range_fold_append(
                    (0..at(statement(5).entry, i)).fold(
                        0, |acc, k| { acc + to_integer(a[k]) }
                    )
                )) using {
                    0 <= at(statement(5).entry, i);
                    at(statement(5).entry, i) < n;
                    at(statement(5).entry, i) < 2147483647;
                    loadable(a[0..n]);
                    forall (k: int32) {
                        0 <= k and k < n implies
                            -1000 <= a[k] and a[k] <= 1000
                    };
                }
            }
            have 0 <= i by { simp(); }
            have i <= n by { simp(); }
            have to_integer(total) ==
                (0..(at(statement(5).entry, i) + 1)).fold(
                    0, |acc, k| { acc + to_integer(a[k]) }
                ) by {
                simp() using {
                    to_integer(total) ==
                        (0..at(statement(5).entry, i)).fold(
                            0, |acc, k| { acc + to_integer(a[k]) }
                        ) + to_integer(a[at(statement(5).entry, i)]);
                    (0..(at(statement(5).entry, i) + 1)).fold(
                        0, |acc, k| { acc + to_integer(a[k]) }
                    ) ==
                        (0..at(statement(5).entry, i)).fold(
                            0, |acc, k| { acc + to_integer(a[k]) }
                        ) + to_integer(a[at(statement(5).entry, i)]);
                }
            }
            have to_integer(total) ==
                (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) by {
                rewrite(i == at(statement(5).entry, i) + 1);
                assumption();
            }
            have -1000 * to_integer(i) <=
                (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) by {
                simp() using {
                    -1000 * to_integer(i) <= to_integer(total);
                    to_integer(total) ==
                        (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                }
            }
            have (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) <=
                1000 * to_integer(i) by {
                simp() using {
                    to_integer(total) <= 1000 * to_integer(i);
                    to_integer(total) ==
                        (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                }
            }
            have forall (k: int32) {
                k >= 0 and k < i implies defined(a[k])
            } by {
                intro();
                intro();
                have k < n by {
                    apply(int32_lt_le_transitive(k, i, n)) using {
                        k < i;
                        i <= n;
                    }
                }
                simp() using {
                    loadable(a[0..n]);
                    k >= 0;
                    k < n;
                }
            }
            close_invariants by { simp(); }
        }
    }
    have i == n by {
        apply(int32_le_and_not_lt_implies_eq(i, n)) using {
            i <= n;
            not i < n;
        }
    }
    have n == i by {
        simp() using {
            i == n;
        }
    }
    have to_integer(total) ==
        (0..n).fold(0, |acc, k| { acc + to_integer(a[k]) }) by {
        rewrite(n == i);
        assumption();
    }
    step();
    simp();
}
```

```expect
pass
```
