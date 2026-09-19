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
        decreases 3 - i;
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
                intro();
                intro();
                normalize();
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                intro();
                intro();
                intro();
                enumerate();
            }
        }
        preserve by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k < i);
                if k < (i - 1) {
                    have k != (i - 1) by {
                        apply(int32_lt_implies_neq(k, (i - 1))) using {
                            k < (i - 1);
                        }
                    }
                    instantiate(forall (k: int32) { at(statement(3).entry, 0) <= at(statement(3).entry, k) and at(statement(3).entry, k) < at(statement(3).entry, i) implies at(statement(3).entry, dst[k]) == old(src[k]) }, k) using {
                        0 <= k;
                        k < (i - 1);
                    }
                    transport(at(statement(3).entry, dst[k]) == old(src[k]), dst[k] == old(src[k])) using {
                        at(statement(3).entry, dst[k]) == old(src[k]);
                    }
                } else {
                    have k == (i - 1) by {
                        have k <= (i - 1) by {
                            apply(int32_lt_successor_implies_le(k, (i - 1))) using {
                                k < i;
                            }
                        }
                        apply(int32_le_and_not_lt_implies_eq(k, (i - 1))) using {
                            k <= (i - 1);
                            not k < (i - 1);
                        }
                    }
                    instantiate(forall (k: int32) { at(statement(3).entry, 0) <= at(statement(3).entry, k) and at(statement(3).entry, k) < at(statement(3).entry, 3) implies at(statement(3).entry, src[k]) == old(src[k]) }, k) using {
                        0 <= k;
                        at(statement(3).entry, i) < at(statement(3).entry, 3);
                        not k < (i - 1);
                        k < i;
                        at(statement(3).entry, i) <= at(statement(3).entry, 3);
                        at(statement(3).entry, i) >= at(statement(3).entry, 0);
                        k == (i - 1);
                    }
                    transport(at(statement(3).entry, src[k]) == old(src[k]), dst[k] == old(src[k])) using {
                        at(statement(3).entry, src[k]) == old(src[k]);
                        k == (i - 1);
                    }
                }
            }
            close_invariants by {
                both {
                    both {
                        apply(int32_increment_greater_equal_lower_bound(at(statement(3).entry, i), at(statement(3).entry, 0), at(statement(3).entry, 3))) using {
                            at(statement(3).entry, i) >= at(statement(3).entry, 0);
                            at(statement(3).entry, i) < at(statement(3).entry, 3);
                        }
                    } and {
                        apply(int32_increment_upper_bound(at(statement(3).entry, i), at(statement(3).entry, 3))) using {
                            at(statement(3).entry, i) < at(statement(3).entry, 3);
                        }
                    }
                } and {
                    both {
                        have viewable((src + 0)[0..1]) by {
                            transport(at(function.entry, viewable(src[0..3])), viewable((src + 0)[0..1])) using {
                                at(function.entry, viewable(src[0..3]));
                            }
                        }
                        have viewable((src + 1)[0..1]) by {
                            transport(at(function.entry, viewable(src[0..3])), viewable((src + 1)[0..1])) using {
                                at(function.entry, viewable(src[0..3]));
                            }
                        }
                        have viewable((src + 2)[0..1]) by {
                            transport(at(function.entry, viewable(src[0..3])), viewable((src + 2)[0..1])) using {
                                at(function.entry, viewable(src[0..3]));
                            }
                        }
                        enumerate();
                    } and {
                        both {
                            have at(function.entry, viewable((src + 0)[0..1])) by {
                                transport(at(function.entry, viewable(src[0..3])), at(function.entry, viewable((src + 0)[0..1]))) using {
                                    at(function.entry, viewable(src[0..3]));
                                }
                            }
                            have at(function.entry, viewable((src + 1)[0..1])) by {
                                transport(at(function.entry, viewable(src[0..3])), at(function.entry, viewable((src + 1)[0..1]))) using {
                                    at(function.entry, viewable(src[0..3]));
                                }
                            }
                            have at(function.entry, viewable((src + 2)[0..1])) by {
                                transport(at(function.entry, viewable(src[0..3])), at(function.entry, viewable((src + 2)[0..1]))) using {
                                    at(function.entry, viewable(src[0..3]));
                                }
                            }
                            enumerate();
                        } and {
                            both {
                                simp();
                            } and {
                                both {
                                    intro();
                                    intro();
                                    extract(0 <= __click_q0);
                                    extract(__click_q0 < i);
                                    if __click_q0 < (i - 1) {
                                        have __click_q0 != (i - 1) by {
                                            apply(int32_lt_implies_neq(__click_q0, (i - 1))) using {
                                                __click_q0 < (i - 1);
                                            }
                                        }
                                        transport(at(function.entry, viewable(dst[0..3])), viewable((dst + __click_q0)[0..1])) using {
                                            __click_q0 < i;
                                            at(statement(3).entry, i) < at(statement(3).entry, 3);
                                            0 <= __click_q0;
                                            at(function.entry, viewable(dst[0..3]));
                                        }
                                    } else {
                                        have __click_q0 == (i - 1) by {
                                            have __click_q0 <= (i - 1) by {
                                                apply(int32_lt_successor_implies_le(__click_q0, (i - 1))) using {
                                                    __click_q0 < i;
                                                }
                                            }
                                            apply(int32_le_and_not_lt_implies_eq(__click_q0, (i - 1))) using {
                                                __click_q0 <= (i - 1);
                                                not __click_q0 < (i - 1);
                                            }
                                        }
                                        transport(at(function.entry, viewable(dst[0..3])), viewable((dst + __click_q0)[0..1])) using {
                                            at(statement(3).entry, i) < at(statement(3).entry, 3);
                                            at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                            __click_q0 == (i - 1);
                                            at(function.entry, viewable(dst[0..3]));
                                        }
                                    }
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        extract(0 <= __click_q0);
                                        extract(__click_q0 < i);
                                        if __click_q0 < (i - 1) {
                                            have __click_q0 != (i - 1) by {
                                                apply(int32_lt_implies_neq(__click_q0, (i - 1))) using {
                                                    __click_q0 < (i - 1);
                                                }
                                            }
                                            transport(at(function.entry, viewable(src[0..3])), at(function.entry, viewable((src + __click_q0)[0..1]))) using {
                                                __click_q0 < i;
                                                at(statement(3).entry, i) < at(statement(3).entry, 3);
                                                0 <= __click_q0;
                                                at(function.entry, viewable(src[0..3]));
                                            }
                                        } else {
                                            have __click_q0 == (i - 1) by {
                                                have __click_q0 <= (i - 1) by {
                                                    apply(int32_lt_successor_implies_le(__click_q0, (i - 1))) using {
                                                        __click_q0 < i;
                                                    }
                                                }
                                                apply(int32_le_and_not_lt_implies_eq(__click_q0, (i - 1))) using {
                                                    __click_q0 <= (i - 1);
                                                    not __click_q0 < (i - 1);
                                                }
                                            }
                                            transport(at(function.entry, viewable(src[0..3])), at(function.entry, viewable((src + __click_q0)[0..1]))) using {
                                                at(statement(3).entry, i) < at(statement(3).entry, 3);
                                                at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                                __click_q0 == (i - 1);
                                                at(function.entry, viewable(src[0..3]));
                                            }
                                        }
                                    } and {
                                both {
                                                                            intro();
                                                                            extract(i >= 0);
                                                                            extract(i <= 3);
                                                                            intro();
                                                                            intro();
                                                                            intro();
                                                                            intro();
                                                                            intro();
                                                                            intro();
                                                                            intro();
                                                                            instantiate(forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) }, __click_q0) using {
                                                                                0 <= __click_q0 and __click_q0 < i;
                                                                            }
                                                                            assumption();
                                                                        
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
        }
        assumption();
    }
    have dst[1] == old(src[1]) by {
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 1) using {
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
        }
        assumption();
    }
    have dst[2] == old(src[2]) by {
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 2) using {
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            at(loop(0).exit, i) >= at(loop(0).exit, 0);
        }
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
