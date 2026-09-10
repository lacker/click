# bubble_sort3_two_pass proves sortedness with loop invariants

This checks that a fixed-size two-pass bubble sort over three cells can prove
sortedness from loop VCs and quantified invariants, without bounded execution.

The proof below is a saved expansion of explicit branch arguments and invariant
closure bodies. Keeping the simple steps avoids repeating the expensive `simp`
search; the C and invariants are unchanged.

```c filename=bubble_sort3_two_pass.c
int32 bubble_sort3_two_pass(int32 p[3]) {
    int32 j;
    int32 tmp;
    j = 0;
    while (j < 2) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        }
        j = j + 1;
    }
    j = 0;
    while (j < 1) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        }
        j = j + 1;
    }
    return 0;
}
```

```click
verifying "bubble_sort3_two_pass.c";

predicate sorted(p: int32[], n: int32) {
    sorted_range(p, 0, n)
}

predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_sort3_two_pass(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3);
} by {
    step();
    step();
    step();
    loop {
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            have j >= 0 and j <= 2 by {
                unfold(all_le_range);
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have all_le_range(p, 0, j, p[j]) by {
                unfold(all_le_range);
                normalize();
            }
        }
        preserve by {
            if p[(j + 1)] < p[j] {
                unfold(all_le_range);
                step();
                step();
                step();
                step();
                step();
                have all_le_range(p, 0, j, p[j]) by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(0 <= k);
                    extract(k < j);
                    if k < (j - 1) {
                        have k != (j - 1) by {
                            apply(int32_lt_implies_neq(k, (j - 1))) using {
                                k < (j - 1);
                            }
                        }
                        instantiate(forall (__click_q0: int32) { at(statement(6).entry, 0) <= at(statement(6).entry, __click_q0) and at(statement(6).entry, 0) <= at(statement(6).entry, __click_q0) and at(statement(6).entry, __click_q0) < at(statement(6).entry, j) implies at(statement(6).entry, p[__click_q0]) <= at(statement(6).entry, tmp) }, k) using {
                            at(statement(4).entry, j) < at(statement(4).entry, 2);
                            k < (j - 1);
                            k < j;
                            at(statement(7).entry, p[(j + 1)]) < at(statement(7).entry, tmp);
                            0 <= k;
                            at(statement(4).entry, j) <= at(statement(4).entry, 2);
                            at(statement(4).entry, j) >= at(statement(4).entry, 0);
                            k != (j - 1);
                            at(function.entry, loadable(p[0..3]));
                        }
                        transport(at(statement(6).entry, p[k]) <= at(statement(6).entry, tmp), p[k] <= p[j]) using {
                            at(statement(6).entry, p[k]) <= at(statement(6).entry, tmp);
                            at(statement(4).entry, j) < at(statement(4).entry, 2);
                            k < (j - 1);
                            k < j;
                            at(statement(7).entry, p[(j + 1)]) < at(statement(7).entry, tmp);
                            0 <= k;
                            at(statement(4).entry, j) <= at(statement(4).entry, 2);
                            at(statement(4).entry, j) >= at(statement(4).entry, 0);
                            k != (j - 1);
                            at(function.entry, loadable(p[0..3]));
                        }
                    } else {
                        have k == (j - 1) by {
                            have k <= (j - 1) by {
                                apply(int32_lt_successor_implies_le(k, (j - 1))) using {
                                    k < j;
                                }
                            }
                            apply(int32_le_and_not_lt_implies_eq(k, (j - 1))) using {
                                k <= (j - 1);
                                not k < (j - 1);
                            }
                        }
                        rewrite(k == (j - 1));
                        apply(int32_lt_implies_le(at(statement(7).entry, p[(j + 1)]), at(statement(7).entry, tmp))) using {
                            at(statement(7).entry, p[(j + 1)]) < at(statement(7).entry, tmp);
                        }
                    }
                }
                close_invariants by {
                    both {
                        both {
                            apply(int32_increment_greater_equal_lower_bound(at(statement(4).entry, j), at(statement(4).entry, 0), at(statement(4).entry, 2))) using {
                                at(statement(4).entry, j) >= at(statement(4).entry, 0);
                                at(statement(4).entry, j) < at(statement(4).entry, 2);
                            }
                        } and {
                            apply(int32_increment_upper_bound(at(statement(4).entry, j), at(statement(4).entry, 2))) using {
                                at(statement(4).entry, j) < at(statement(4).entry, 2);
                            }
                        }
                    } and {
                        both {
                            intro();
                            intro();
                            extract(0 <= __click_q0);
                            extract(0 <= __click_q0);
                            extract(__click_q0 < j);
                            if __click_q0 < (j - 1) {
                                have __click_q0 != (j - 1) by {
                                    apply(int32_lt_implies_neq(__click_q0, (j - 1))) using {
                                        __click_q0 < (j - 1);
                                    }
                                }
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                    __click_q0 < j;
                                    0 <= __click_q0;
                                    at(statement(4).entry, j) <= at(statement(4).entry, 2);
                                    at(function.entry, loadable(p[0..3]));
                                }
                            } else {
                                have __click_q0 == (j - 1) by {
                                    have __click_q0 <= (j - 1) by {
                                        apply(int32_lt_successor_implies_le(__click_q0, (j - 1))) using {
                                            __click_q0 < j;
                                        }
                                    }
                                    apply(int32_le_and_not_lt_implies_eq(__click_q0, (j - 1))) using {
                                        __click_q0 <= (j - 1);
                                        not __click_q0 < (j - 1);
                                    }
                                }
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                    at(statement(4).entry, j) <= at(statement(4).entry, 2);
                                    at(statement(4).entry, j) >= at(statement(4).entry, 0);
                                    __click_q0 == (j - 1);
                                    at(function.entry, loadable(p[0..3]));
                                }
                            }
                        } and {
                            intro();
                            extract(j >= 0);
                            extract(j <= 2);
                            intro();
                            intro();
                            intro();
                            instantiate(forall (k: int32) { at(statement(10).entry, 0) <= at(statement(10).entry, k) and at(statement(10).entry, 0) <= at(statement(10).entry, k) and at(statement(10).entry, k) < at(statement(10).entry, j) implies at(statement(10).entry, p[k]) <= at(statement(10).entry, p[j]) }, __click_q0) using {
                                0 <= __click_q0 and 0 <= __click_q0 and __click_q0 < j;
                            }
                            assumption();
                        }
                    }
                }
            } else {
                unfold(all_le_range);
                step();
                step();
                step();
                have all_le_range(p, 0, j, p[j]) by {
                    intro();
                    intro();
                    extract(0 <= k);
                    extract(0 <= k);
                    extract(k < j);
                    if k < (j - 1) {
                        have k != (j - 1) by {
                            apply(int32_lt_implies_neq(k, (j - 1))) using {
                                k < (j - 1);
                            }
                        }
                        instantiate(forall (__click_q0: int32) { at(statement(9).entry, 0) <= at(statement(9).entry, __click_q0) and at(statement(9).entry, 0) <= at(statement(9).entry, __click_q0) and at(statement(9).entry, __click_q0) < at(statement(9).entry, j) implies at(statement(9).entry, p[__click_q0]) <= at(statement(9).entry, p[j]) }, k) using {
                            at(statement(4).entry, j) < at(statement(4).entry, 2);
                            k < (j - 1);
                            k < j;
                            not at(statement(9).entry, p[(j + 1)]) < at(statement(9).entry, p[j]);
                            0 <= k;
                            at(statement(4).entry, j) <= at(statement(4).entry, 2);
                            at(statement(4).entry, j) >= at(statement(4).entry, 0);
                            k != (j - 1);
                            at(function.entry, loadable(p[0..3]));
                        }
                        transport(at(statement(9).entry, p[k]) <= at(statement(9).entry, p[j]), p[k] <= p[j]) using {
                            at(statement(9).entry, p[k]) <= at(statement(9).entry, p[j]);
                            at(statement(4).entry, j) < at(statement(4).entry, 2);
                            k < (j - 1);
                            k < j;
                            not at(statement(9).entry, p[(j + 1)]) < at(statement(9).entry, p[j]);
                            0 <= k;
                            at(statement(4).entry, j) <= at(statement(4).entry, 2);
                            at(statement(4).entry, j) >= at(statement(4).entry, 0);
                            k != (j - 1);
                            at(function.entry, loadable(p[0..3]));
                        }
                    } else {
                        have k == (j - 1) by {
                            have k <= (j - 1) by {
                                apply(int32_lt_successor_implies_le(k, (j - 1))) using {
                                    k < j;
                                }
                            }
                            apply(int32_le_and_not_lt_implies_eq(k, (j - 1))) using {
                                k <= (j - 1);
                                not k < (j - 1);
                            }
                        }
                        rewrite(k == (j - 1));
                        apply(int32_not_lt_implies_ge(at(statement(9).entry, p[(j + 1)]), at(statement(9).entry, p[j]))) using {
                            not at(statement(9).entry, p[(j + 1)]) < at(statement(9).entry, p[j]);
                        }
                        apply(int32_ge_implies_reversed_le(at(statement(9).entry, p[(j + 1)]), at(statement(9).entry, p[j]))) using {
                            at(statement(9).entry, p[(j + 1)]) >= at(statement(9).entry, p[j]);
                        }
                    }
                }
                close_invariants by {
                    both {
                        both {
                            apply(int32_increment_greater_equal_lower_bound(at(statement(4).entry, j), at(statement(4).entry, 0), at(statement(4).entry, 2))) using {
                                at(statement(4).entry, j) >= at(statement(4).entry, 0);
                                at(statement(4).entry, j) < at(statement(4).entry, 2);
                            }
                        } and {
                            apply(int32_increment_upper_bound(at(statement(4).entry, j), at(statement(4).entry, 2))) using {
                                at(statement(4).entry, j) < at(statement(4).entry, 2);
                            }
                        }
                    } and {
                        both {
                            intro();
                            intro();
                            extract(0 <= __click_q0);
                            extract(0 <= __click_q0);
                            extract(__click_q0 < j);
                            if __click_q0 < (j - 1) {
                                have __click_q0 != (j - 1) by {
                                    apply(int32_lt_implies_neq(__click_q0, (j - 1))) using {
                                        __click_q0 < (j - 1);
                                    }
                                }
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                    __click_q0 < j;
                                    0 <= __click_q0;
                                    at(statement(4).entry, j) <= at(statement(4).entry, 2);
                                    at(function.entry, loadable(p[0..3]));
                                }
                            } else {
                                have __click_q0 == (j - 1) by {
                                    have __click_q0 <= (j - 1) by {
                                        apply(int32_lt_successor_implies_le(__click_q0, (j - 1))) using {
                                            __click_q0 < j;
                                        }
                                    }
                                    apply(int32_le_and_not_lt_implies_eq(__click_q0, (j - 1))) using {
                                        __click_q0 <= (j - 1);
                                        not __click_q0 < (j - 1);
                                    }
                                }
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                    at(statement(4).entry, j) <= at(statement(4).entry, 2);
                                    at(statement(4).entry, j) >= at(statement(4).entry, 0);
                                    __click_q0 == (j - 1);
                                    at(function.entry, loadable(p[0..3]));
                                }
                            }
                        } and {
                            both {
                                intro();
                                intro();
                                extract(0 <= __click_q0);
                                extract(0 <= __click_q0);
                                extract(__click_q0 < j);
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + j)[0..1])) using {
                                    at(statement(4).entry, j) < at(statement(4).entry, 2);
                                    at(statement(4).entry, j) >= at(statement(4).entry, 0);
                                    at(function.entry, loadable(p[0..3]));
                                }
                            } and {
                                intro();
                                extract(j >= 0);
                                extract(j <= 2);
                                intro();
                                intro();
                                intro();
                                intro();
                                instantiate(forall (k: int32) { at(statement(10).entry, 0) <= at(statement(10).entry, k) and at(statement(10).entry, 0) <= at(statement(10).entry, k) and at(statement(10).entry, k) < at(statement(10).entry, j) implies at(statement(10).entry, p[k]) <= at(statement(10).entry, p[j]) }, __click_q0) using {
                                    0 <= __click_q0 and 0 <= __click_q0 and __click_q0 < j;
                                }
                                assumption();
                            }
                        }
                    }
                }
            }
        }
    }
    step();
    loop {
        invariant j >= 0 and j <= 1;
        invariant all_le_range(p, 0, 2, p[2]);
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            have j >= 0 and j <= 1 by {
                unfold(all_le_range);
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have all_le_range(p, 0, 2, p[2]) by {
                unfold(all_le_range);
                intro();
                intro();
                instantiate(forall (__click_q0: int32) { at(statement(10).entry, 0) <= at(statement(10).entry, __click_q0) and at(statement(10).entry, 0) <= at(statement(10).entry, __click_q0) and at(statement(10).entry, __click_q0) < at(statement(10).entry, j) implies at(statement(10).entry, p[__click_q0]) <= at(statement(10).entry, p[j]) }, k) using {
                    0 <= k and 0 <= k and k < 2;
                    not at(loop(0).exit, j) < at(loop(0).exit, 2);
                    at(loop(0).exit, j) <= at(loop(0).exit, 2);
                    at(loop(0).exit, j) >= at(loop(0).exit, 0);
                }
                transport(at(statement(10).entry, p[k]) <= at(statement(10).entry, p[j]), p[k] <= p[2]) using {
                    at(statement(10).entry, p[k]) <= at(statement(10).entry, p[j]);
                    0 <= k and 0 <= k and k < 2;
                    not at(loop(0).exit, j) < at(loop(0).exit, 2);
                    at(loop(0).exit, j) <= at(loop(0).exit, 2);
                    at(loop(0).exit, j) >= at(loop(0).exit, 0);
                }
            }
            have all_le_range(p, 0, j, p[j]) by {
                unfold(all_le_range);
                normalize();
            }
        }
        preserve by {
            if p[(j + 1)] < p[j] {
                unfold(all_le_range);
                have j == 0 by {
                    apply(int32_lt_successor_implies_le(j, 0)) using {
                        j < 1;
                    }
                    apply(int32_le_and_not_lt_implies_eq(j, 0)) using {
                        j <= 0;
                        j >= 0;
                    }
                }
                have p[0] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0) using {
                    }
                    assumption();
                }
                have p[1] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1) using {
                    }
                    assumption();
                }
                mark before_swap;
                unfold(all_le_range);
                step();
                step();
                step();
                step();
                step();
                transport(at(before_swap, p[1] <= p[2]), p[0] <= p[2]) using {
                    at(before_swap, p[1] <= p[2]);
                    at(before_swap, j) == 0;
                }
                transport(at(before_swap, p[0] <= p[2]), p[1] <= p[2]) using {
                    at(before_swap, p[0] <= p[2]);
                    at(before_swap, j) == 0;
                }
                have forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] } by {
                    enumerate();
                }
                have j == 1 by {
                    rewrite(at(statement(17).entry, j) == at(statement(17).entry, 0));
                    normalize();
                }
                transport(at(before_swap, p[(j + 1)] < p[j]), p[0] < p[1]) using {
                    at(before_swap, j) == 0;
                    at(before_swap, p[(j + 1)] < p[j]);
                }
                have p[0] <= p[1] by {
                    apply(int32_lt_implies_le(p[0], p[1])) using {
                        p[0] < p[1];
                    }
                }
                have all_le_range(p, 0, j, p[j]) by {
                    unfold(all_le_range);
                    rewrite(j == 1);
                    enumerate();
                }
                close_invariants by {
                    both {
                        rewrite(at(statement(17).entry, j) == at(statement(17).entry, 0));
                        both {
                            normalize();
                        } and {
                            normalize();
                        }
                    } and {
                        both {
                            have loadable((p + 0)[0..1]) by {
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + 0)[0..1])) using {
                                    at(function.entry, loadable(p[0..3]));
                                }
                            }
                            have loadable((p + 1)[0..1]) by {
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + 1)[0..1])) using {
                                    at(function.entry, loadable(p[0..3]));
                                }
                            }
                            enumerate();
                        } and {
                            both {
                                have loadable((p + 2)[0..1]) by {
                                    transport(at(function.entry, loadable(p[0..3])), loadable((p + 2)[0..1])) using {
                                        at(function.entry, loadable(p[0..3]));
                                    }
                                }
                                have loadable((p + 2)[0..1]) by {
                                    assumption();
                                }
                                enumerate();
                            } and {
                                both {
                                    intro();
                                    intro();
                                    intro();
                                    enumerate();
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        extract(0 <= __click_q0);
                                        extract(0 <= __click_q0);
                                        extract(__click_q0 < j);
                                        if __click_q0 < (j - 1) {
                                            have __click_q0 != (j - 1) by {
                                                apply(int32_lt_implies_neq(__click_q0, (j - 1))) using {
                                                    __click_q0 < (j - 1);
                                                }
                                            }
                                            transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                                __click_q0 < j;
                                                0 <= __click_q0;
                                                at(function.entry, j) == at(function.entry, 1);
                                                at(function.entry, loadable(p[0..3]));
                                            }
                                        } else {
                                            have __click_q0 == (j - 1) by {
                                                have __click_q0 <= (j - 1) by {
                                                    apply(int32_lt_successor_implies_le(__click_q0, (j - 1))) using {
                                                        __click_q0 < j;
                                                    }
                                                }
                                                apply(int32_le_and_not_lt_implies_eq(__click_q0, (j - 1))) using {
                                                    __click_q0 <= (j - 1);
                                                    not __click_q0 < (j - 1);
                                                }
                                            }
                                            transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                                __click_q0 == (j - 1);
                                                at(function.entry, j) == at(function.entry, 1);
                                                at(function.entry, loadable(p[0..3]));
                                            }
                                        }
                                    } and {
                                        intro();
                                        extract(j >= 0);
                                        extract(j <= 1);
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        intro();
                                        instantiate(forall (k: int32) { at(statement(18).entry, 0) <= at(statement(18).entry, k) and at(statement(18).entry, 0) <= at(statement(18).entry, k) and at(statement(18).entry, k) < at(statement(18).entry, j) implies at(statement(18).entry, p[k]) <= at(statement(18).entry, p[j]) }, __click_q0) using {
                                            0 <= __click_q0 and 0 <= __click_q0 and __click_q0 < j;
                                        }
                                        assumption();
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                unfold(all_le_range);
                have j == 0 by {
                    apply(int32_lt_successor_implies_le(j, 0)) using {
                        j < 1;
                    }
                    apply(int32_le_and_not_lt_implies_eq(j, 0)) using {
                        j <= 0;
                        j >= 0;
                    }
                }
                have p[0] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0) using {
                    }
                    assumption();
                }
                have p[1] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1) using {
                    }
                    assumption();
                }
                mark before_swap;
                unfold(all_le_range);
                step();
                step();
                step();
                have j == 1 by {
                    rewrite(at(statement(17).entry, j) == at(statement(17).entry, 0));
                    normalize();
                }
                transport(at(before_swap, not p[(j + 1)] < p[j]), not p[1] < p[0]) using {
                    at(before_swap, j) == 0;
                    at(before_swap, not p[(j + 1)] < p[j]);
                }
                have p[0] <= p[1] by {
                    apply(int32_not_lt_implies_ge(p[1], p[0])) using {
                        not p[1] < p[0];
                    }
                    apply(int32_not_lt_implies_ge(at(statement(18).entry, p[1]), at(statement(18).entry, p[0]))) using {
                        not at(statement(18).entry, p[1]) < at(statement(18).entry, p[0]);
                    }
                    apply(int32_ge_implies_reversed_le(at(statement(18).entry, p[1]), at(statement(18).entry, p[0]))) using {
                        at(statement(18).entry, p[1]) >= at(statement(18).entry, p[0]);
                    }
                }
                have all_le_range(p, 0, j, p[j]) by {
                    unfold(all_le_range);
                    rewrite(j == 1);
                    enumerate();
                }
                close_invariants by {
                    both {
                        rewrite(at(statement(17).entry, j) == at(statement(17).entry, 0));
                        both {
                            normalize();
                        } and {
                            normalize();
                        }
                    } and {
                        both {
                            have loadable((p + 0)[0..1]) by {
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + 0)[0..1])) using {
                                    at(function.entry, loadable(p[0..3]));
                                }
                            }
                            have loadable((p + 1)[0..1]) by {
                                transport(at(function.entry, loadable(p[0..3])), loadable((p + 1)[0..1])) using {
                                    at(function.entry, loadable(p[0..3]));
                                }
                            }
                            enumerate();
                        } and {
                            both {
                                have loadable((p + 2)[0..1]) by {
                                    transport(at(function.entry, loadable(p[0..3])), loadable((p + 2)[0..1])) using {
                                        at(function.entry, loadable(p[0..3]));
                                    }
                                }
                                have loadable((p + 2)[0..1]) by {
                                    assumption();
                                }
                                enumerate();
                            } and {
                                both {
                                    intro();
                                    intro();
                                    intro();
                                    assumption();
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        extract(0 <= __click_q0);
                                        extract(0 <= __click_q0);
                                        extract(__click_q0 < j);
                                        if __click_q0 < (j - 1) {
                                            have __click_q0 != (j - 1) by {
                                                apply(int32_lt_implies_neq(__click_q0, (j - 1))) using {
                                                    __click_q0 < (j - 1);
                                                }
                                            }
                                            transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                                __click_q0 < j;
                                                0 <= __click_q0;
                                                at(function.entry, j) == at(function.entry, 1);
                                                at(function.entry, loadable(p[0..3]));
                                            }
                                        } else {
                                            have __click_q0 == (j - 1) by {
                                                have __click_q0 <= (j - 1) by {
                                                    apply(int32_lt_successor_implies_le(__click_q0, (j - 1))) using {
                                                        __click_q0 < j;
                                                    }
                                                }
                                                apply(int32_le_and_not_lt_implies_eq(__click_q0, (j - 1))) using {
                                                    __click_q0 <= (j - 1);
                                                    not __click_q0 < (j - 1);
                                                }
                                            }
                                            transport(at(function.entry, loadable(p[0..3])), loadable((p + __click_q0)[0..1])) using {
                                                __click_q0 == (j - 1);
                                                at(function.entry, j) == at(function.entry, 1);
                                                at(function.entry, loadable(p[0..3]));
                                            }
                                        }
                                    } and {
                                        both {
                                            intro();
                                            intro();
                                            extract(0 <= __click_q0);
                                            extract(0 <= __click_q0);
                                            extract(__click_q0 < j);
                                            transport(at(function.entry, loadable(p[0..3])), loadable((p + j)[0..1])) using {
                                                at(function.entry, j) == at(function.entry, 1);
                                                at(function.entry, loadable(p[0..3]));
                                            }
                                        } and {
                                            rewrite(at(statement(17).entry, j) == at(statement(17).entry, 0));
                                            intro();
                                            intro();
                                            intro();
                                            intro();
                                            intro();
                                            intro();
                                            enumerate();
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    step();
    unfold(sorted);
    unfold(sorted_range);
    unfold(all_le_range);
    unfold(sorted);
    have sorted(p, 3) by {
        have p[0] <= p[1] by {
            instantiate(forall (k: int32) { 0 <= k and at(loop(1).exit, 0) <= k and k < at(loop(1).exit, j) implies at(loop(1).exit, p)[k] <= at(loop(1).exit, p[j]) }, 0) using {
                not at(loop(1).exit, j) < at(loop(1).exit, 1);
                at(loop(1).exit, j) <= at(loop(1).exit, 1);
                at(loop(1).exit, j) >= at(loop(1).exit, 0);
            }
            transport(at(loop(1).exit, p)[0] <= at(loop(1).exit, p[j]), p[0] <= p[1]) using {
            }
        }
        have p[1] <= p[2] by {
            instantiate(all_le_range(at(loop(1).exit, p), at(loop(1).exit, 0), at(loop(1).exit, 2), at(loop(1).exit, p[2])), 1) using {
            }
            assumption();
        }
        have p[0] <= p[2] by {
            instantiate(all_le_range(at(loop(1).exit, p), at(loop(1).exit, 0), at(loop(1).exit, 2), at(loop(1).exit, p[2])), 0) using {
            }
            assumption();
        }
        enumerate();
    }
    assumption();
}
```

```expect
pass
```
