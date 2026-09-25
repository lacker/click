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
    requires n <= 1073741823;
    requires viewable(a[0..n]);
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
    have 0 <= 0 by {
        normalize();
    }
    have (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 by {
        apply(integer_range_fold_empty((0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) using {
            0 <= 0;
        }
    }
    have 0 == (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        normalize() using {
            (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0;
        }
    }
    have 0 <= (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        arithmetic_certificate {
            premise 0: (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 => (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0;
            eq_to_le 0 reverse => 0 <= (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) });
            conclusion 1;
        }
    }
    have (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0 by {
        arithmetic_certificate {
            premise 0: (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 => (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0;
            eq_to_le 0 => (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0;
            conclusion 1;
        }
    }
    loop as sum {
        decreases (n - i);
        invariant 0 <= i;
        invariant i <= n;
        invariant to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
        invariant (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
        invariant (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i));
        initialize by {
            have 0 <= i by {
                normalize();
            }
            have i <= n by {
                if n < 1073741823 {
                    have n != 1073741823 by {
                        apply(int32_lt_implies_neq(n, 1073741823)) using {
                            n < 1073741823;
                        }
                    }
                    assumption();
                } else {
                    have n == 1073741823 by {
                        have n <= 1073741823 by {
                            assumption();
                        }
                        extract(n <= 1000);
                        apply(int32_le_and_not_lt_implies_eq(n, 1073741823)) using {
                            n <= 1073741823;
                            not n < 1073741823;
                        }
                    }
                    rewrite(n == 1073741823);
                    normalize();
                }
            }
            have to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                assumption();
            }
            have (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                assumption();
            }
            have (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) by {
                assumption();
            }
        }
        preserve by {
            have -1000 <= a[i] and a[i] <= 1000 by {
                instantiate(forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and a[k] <= 1000 }, i) using {
                    0 <= i;
                    i < n;
                }
                assumption();
            }
            have -1000 <= to_integer(a[i]) by {
                apply(int32_less_equal_to_integer(-1000, a[i])) using {
                    -1000 <= a[i];
                }
            }
            have to_integer(a[i]) <= 1000 by {
                apply(int32_less_equal_to_integer(a[i], 1000)) using {
                    a[i] <= 1000;
                }
            }
            have 0 <= to_integer(i) by {
                apply(int32_less_equal_to_integer(0, i)) using {
                    0 <= i;
                }
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
                }
                arithmetic_certificate {
                    premise 0: to_integer(i) <= to_integer(n) => to_integer(i) <= to_integer(n);
                    premise 1: to_integer(n) <= 1000 => to_integer(n) <= 1000;
                    add 0, 1 => (to_integer(i) + to_integer(n)) <= (to_integer(n) + 1000);
                    conclusion 2;
                }
            }
            have (-1000 * to_integer(i)) <= to_integer(total) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    eq_to_le 0 reverse => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= to_integer(total);
                    premise 1: (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 1, 2 => ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + (-1000 * to_integer(i))) <= (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 3;
                }
            }
            have to_integer(total) <= (1000 * to_integer(i)) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    eq_to_le 0 => to_integer(total) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    premise 1: (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i));
                    add 1, 2 => (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) })) <= ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + (1000 * to_integer(i)));
                    conclusion 3;
                }
            }
            have ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) by {
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer(i)) <= to_integer(total) => (-1000 * to_integer(i)) <= to_integer(total);
                    premise 1: -1000 <= to_integer(a[i]) => -1000 <= to_integer(a[i]);
                    add 0, 1 => ((-1000 * to_integer(i)) + -1000) <= (to_integer(total) + to_integer(a[i]));
                    conclusion 2;
                }
            }
            have (to_integer(total) + to_integer(a[i])) >= -2147483648 by {
                arithmetic_certificate {
                    premise 0: ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) => ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer(i) <= 1000 => to_integer(i) <= 1000;
                    scale 1 by 1000 => (1000 * to_integer(i)) <= (1000 * 1000);
                    add 0, 2 => (((-1000 * to_integer(i)) - 1000) + (1000 * to_integer(i))) <= ((to_integer(total) + to_integer(a[i])) + (1000 * 1000));
                    trivial => -2146482648 <= 0;
                    add 3, 4 => ((((-1000 * to_integer(i)) - 1000) + (1000 * to_integer(i))) + -2146482648) <= (((to_integer(total) + to_integer(a[i])) + (1000 * 1000)) + 0);
                    conclusion 5;
                }
            }
            have (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) <= (1000 * to_integer(i)) => to_integer(total) <= (1000 * to_integer(i));
                    premise 1: to_integer(a[i]) <= 1000 => to_integer(a[i]) <= 1000;
                    add 0, 1 => (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000);
                    conclusion 2;
                }
            }
            have (to_integer(total) + to_integer(a[i])) <= 2147483647 by {
                arithmetic_certificate {
                    premise 0: (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) => (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000);
                    premise 1: to_integer(i) <= 1000 => to_integer(i) <= 1000;
                    scale 1 by 1000 => (1000 * to_integer(i)) <= (1000 * 1000);
                    add 0, 2 => ((to_integer(total) + to_integer(a[i])) + (1000 * to_integer(i))) <= (((1000 * to_integer(i)) + 1000) + (1000 * 1000));
                    trivial => -2146482647 <= 0;
                    add 3, 4 => (((to_integer(total) + to_integer(a[i])) + (1000 * to_integer(i))) + -2146482647) <= ((((1000 * to_integer(i)) + 1000) + (1000 * 1000)) + 0);
                    conclusion 5;
                }
            }
            have defined(a[i]) by {
                transport(viewable(a[0..n]), defined(a[i])) using {
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    0 <= i;
                    i < n;
                }
            }
            have defined((total + a[i])) by {
                apply(int32_add_defined_by_integer_bounds(total, a[i])) using {
                    (to_integer(total) + to_integer(a[i])) >= -2147483648;
                    (to_integer(total) + to_integer(a[i])) <= 2147483647;
                }
                both {
                    assumption();
                } and {
                    assumption();
                }
            }
            have to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) by {
                apply(int32_add_to_integer(total, a[i])) using {
                    defined((total + a[i]));
                }
            }
            have to_integer((total + a[i])) == ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[i])) by {
                arithmetic_certificate {
                    premise 0: to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) => to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 0, 1 => (to_integer((total + a[i])) + to_integer(total)) == ((to_integer(total) + to_integer(a[i])) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 2;
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
                    normalize();
                }
                apply(int32_lt_transitive(i, 1000, 2147483647)) using {
                    i < 1000;
                    1000 < 2147483647;
                }
            }
            have defined((i + 1)) by {
                apply(int32_increment_below_max_is_defined(i)) using {
                    i < 2147483647;
                }
            }
            have to_integer((i + 1)) == (to_integer(i) + to_integer(1)) by {
                apply(int32_add_to_integer(i, 1)) using {
                    defined((i + 1));
                }
            }
            have (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i])) by {
                arithmetic_certificate {
                    premise 0: ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) => ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer((i + 1)) == (to_integer(i) + to_integer(1)) => to_integer((i + 1)) == (to_integer(i) + to_integer(1));
                    eq_to_le 1 reverse => (to_integer(i) + to_integer(1)) <= to_integer((i + 1));
                    scale 2 by 1000 => (1000 * (to_integer(i) + to_integer(1))) <= (1000 * to_integer((i + 1)));
                    add 0, 3 => (((-1000 * to_integer(i)) - 1000) + (1000 * (to_integer(i) + to_integer(1)))) <= ((to_integer(total) + to_integer(a[i])) + (1000 * to_integer((i + 1))));
                    conclusion 4;
                }
            }
            have (-1000 * to_integer((i + 1))) <= to_integer((total + a[i])) by {
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i])) => (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) => to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
                    eq_to_le 1 reverse => (to_integer(total) + to_integer(a[i])) <= to_integer((total + a[i]));
                    add 0, 2 => ((-1000 * to_integer((i + 1))) + (to_integer(total) + to_integer(a[i]))) <= ((to_integer(total) + to_integer(a[i])) + to_integer((total + a[i])));
                    conclusion 3;
                }
            }
            have (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1))) by {
                arithmetic_certificate {
                    premise 0: (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) => (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000);
                    premise 1: to_integer((i + 1)) == (to_integer(i) + to_integer(1)) => to_integer((i + 1)) == (to_integer(i) + to_integer(1));
                    eq_to_le 1 reverse => (to_integer(i) + to_integer(1)) <= to_integer((i + 1));
                    scale 2 by 1000 => (1000 * (to_integer(i) + to_integer(1))) <= (1000 * to_integer((i + 1)));
                    add 0, 3 => ((to_integer(total) + to_integer(a[i])) + (1000 * (to_integer(i) + to_integer(1)))) <= (((1000 * to_integer(i)) + 1000) + (1000 * to_integer((i + 1))));
                    conclusion 4;
                }
            }
            have to_integer((total + a[i])) <= (1000 * to_integer((i + 1))) by {
                arithmetic_certificate {
                    premise 0: to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) => to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
                    eq_to_le 0 => to_integer((total + a[i])) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1))) => (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1)));
                    add 1, 2 => (to_integer((total + a[i])) + (to_integer(total) + to_integer(a[i]))) <= ((to_integer(total) + to_integer(a[i])) + (1000 * to_integer((i + 1))));
                    conclusion 3;
                }
            }
            step();
            step();
            have i == (at(statement(5).entry, i) + 1) by {
                normalize();
            }
            have (0..(at(statement(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)])) by {
                apply(integer_range_fold_append((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) using {
                    0 <= at(statement(5).entry, i);
                    at(statement(5).entry, i) < n;
                    at(statement(5).entry, i) < 2147483647;
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and a[k] <= 1000 };
                }
            }
            have 0 <= i by {
                apply(int32_increment_lower_bound(at(statement(6).entry, i), at(statement(5).entry, 0), at(statement(6).entry, 2147483647))) using {
                    at(statement(5).entry, 0) <= at(statement(5).entry, i);
                    at(statement(6).entry, i) < at(statement(6).entry, 2147483647);
                }
            }
            have i <= n by {
                apply(int32_increment_upper_bound(at(statement(5).entry, i), at(statement(5).entry, n))) using {
                    at(statement(5).entry, i) < at(statement(5).entry, n);
                }
            }
            have to_integer(total) == (0..(at(statement(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) == ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)])) => to_integer(total) == ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)]));
                    premise 1: (0..(at(statement(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)])) => (0..(at(statement(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)]));
                    scale 1 by -1 => (-1 * (0..(at(statement(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) })) == (-1 * ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)])));
                    add 0, 2 => (to_integer(total) + (-1 * (0..(at(statement(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) == (((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)])) + (-1 * ((0..at(statement(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(statement(5).entry, i)]))));
                    conclusion 3;
                }
            }
            have to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                rewrite(i == (at(statement(5).entry, i) + 1));
                assumption();
            }
            have (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer(i)) <= to_integer(total) => (-1000 * to_integer(i)) <= to_integer(total);
                    premise 1: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    eq_to_le 1 => to_integer(total) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 0, 2 => ((-1000 * to_integer(i)) + to_integer(total)) <= (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 3;
                }
            }
            have (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) <= (1000 * to_integer(i)) => to_integer(total) <= (1000 * to_integer(i));
                    premise 1: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    eq_to_le 1 reverse => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= to_integer(total);
                    add 0, 2 => (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) })) <= ((1000 * to_integer(i)) + to_integer(total));
                    conclusion 3;
                }
            }
            have forall (k: int32) { k >= 0 and k < i implies defined(a[k]) } by {
                intro();
                intro();
                have k < n by {
                    apply(int32_lt_le_transitive(k, i, n)) using {
                        k < i;
                        i <= n;
                    }
                }
                transport(viewable(a[0..n]), defined(a[k])) using {
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    k >= 0;
                    k < n;
                }
            }
            close_invariants by {
                extract(n <= 1000);
                both {
                    assumption();
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
                                arithmetic_certificate signed_int32 {
                                    premise 0: at(statement(5).entry, 0) <= at(statement(5).entry, i) => at(statement(5).entry, 0) <= at(statement(5).entry, i);
                                    premise 1: at(statement(5).entry, i) < at(statement(5).entry, n) => at(statement(5).entry, i) < at(statement(5).entry, n);
                                    premise 2: 0 <= n => 0 <= n;
                                    premise 3: n <= 1000 => n <= 1000;
                                    interval_from_affine 2 (n) (0) (2147483647);
                                    interval_from_affine 3 (n) (-2147483648) (1000);
                                    interval_intersect 4, 5 (0) (1000);
                                    add 1, 3 => (at(statement(5).entry, i) + n) < (at(statement(5).entry, n) + 1000);
                                    interval_from_affine 0 (at(statement(5).entry, i)) (0) (2147483647);
                                    interval_from_affine 7 (at(statement(5).entry, i)) (-2147483648) (999);
                                    interval_intersect 8, 9 (0) (999);
                                    interval_subtract 6, 10 6 (-999) (1000);
                                    interval_atom (1) (1) (1);
                                    interval_subtract 11, 12 11 (-1000) (999);
                                    affine_conclusion 1 13 => 0 <= ((n - at(statement(5).entry, i)) - 1);
                                    conclusion 14;
                                }
                            } and {
                                arithmetic_certificate signed_int32 {
                                    premise 0: at(statement(5).entry, 0) <= at(statement(5).entry, i) => at(statement(5).entry, 0) <= at(statement(5).entry, i);
                                    premise 1: at(statement(5).entry, i) < at(statement(5).entry, n) => at(statement(5).entry, i) < at(statement(5).entry, n);
                                    premise 2: 0 <= n => 0 <= n;
                                    premise 3: n <= 1000 => n <= 1000;
                                    interval_from_affine 2 (n) (0) (2147483647);
                                    interval_from_affine 3 (n) (-2147483648) (1000);
                                    interval_intersect 4, 5 (0) (1000);
                                    add 1, 3 => (at(statement(5).entry, i) + n) < (at(statement(5).entry, n) + 1000);
                                    interval_from_affine 0 (at(statement(5).entry, i)) (0) (2147483647);
                                    interval_from_affine 7 (at(statement(5).entry, i)) (-2147483648) (999);
                                    interval_intersect 8, 9 (0) (999);
                                    interval_subtract 6, 10 6 (-999) (1000);
                                    interval_atom (1) (1) (1);
                                    interval_subtract 11, 12 11 (-1000) (999);
                                    interval_subtract 6, 10 6 (-999) (1000);
                                    trivial => 0 <= 0;
                                    affine_conclusion_pair 15 13 14 => ((n - at(statement(5).entry, i)) - 1) < (n - at(statement(5).entry, i));
                                    conclusion 16;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    have i == n by {
        apply(int32_le_and_not_lt_implies_eq(i, n)) using {
            i <= n;
            not i < n;
        }
    }
    have n == i by {
        rewrite(n == i);
        normalize();
    }
    have to_integer(total) == (0..n).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        rewrite(n == i);
        assumption();
    }
    step();
    have to_integer(result) == (0..n).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        assumption();
    }
    assumption();
}
```

```expect
pass
```
