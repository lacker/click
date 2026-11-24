# bubble_sort3_two_pass proves sortedness with loop invariants

This checks that a fixed-size two-pass bubble sort over three cells can prove
sortedness from loop VCs and quantified invariants, without bounded execution.

The proof below is a saved expansion of explicit branch arguments and invariant
closure bodies. Each swap preserves untouched cells with explicit separation
and one-store `preserve` steps. The two stored-value equalities name the
respective store exits, and ordinary arithmetic combines the resulting facts.
No written or expanded `transport` is needed; the C and invariants are unchanged.

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
    requires viewable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3);
} by {
    step();
    step();
    step();
    loop {
        decreases (2 - j);
        invariant j >= 0 and j <= 2;
        invariant forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] };
        initialize by {
            have j >= 0 and j <= 2 by {
                all {
                    j >= 0 => {
                        normalize();
                    }
                    j <= 2 => {
                        normalize();
                    }
                }
            }
            have forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] } by {
                enumerate();
            }
        }
        maintain by {
            if p[(j + 1)] < p[j] {
                step();
                step();
                step();
                step();
                step();
                have forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] } by {
                    intro();
                    intro();
                    if k < (j - 1) {
                        have k < at(region(4).entry, j);
                        instantiate(forall (__click_q0: int32) { at(region(6).entry, 0) <= at(region(6).entry, __click_q0) and at(region(6).entry, 0) <= at(region(6).entry, __click_q0) and at(region(6).entry, __click_q0) < at(region(6).entry, j) implies at(region(6).entry, p[__click_q0]) <= at(region(6).entry, tmp) }, k);
                        have at(region(4).entry, j) != k by { close(); }
                        have at(region(4).entry, separate(memory(p[j]), memory(p[k]))) by {
                            apply(click::separation::separate_elements(p, at(region(4).entry, j), k));
                        }
                        have separate(statement(3).statement(0).statement(1).footprint, memory(p[k])) by {
                            normalize() using { at(region(4).entry, separate(memory(p[j]), memory(p[k]))); };
                        }
                        have at(statement(3).statement(0).statement(1).exit, p[k]) == at(statement(3).statement(0).statement(1).entry, p[k]) by {
                            preserve(memory(p[k]), statement(3).statement(0).statement(1));
                        }
                        have j != k by { close(); }
                        have separate(memory(p[j]), memory(p[k])) by {
                            apply(click::separation::separate_elements(p, j, k));
                        }
                        have separate(statement(3).statement(0).statement(2).footprint, memory(p[k])) by {
                            normalize() using { separate(memory(p[j]), memory(p[k])); };
                        }
                        have at(statement(3).statement(0).statement(2).exit, p[k]) == at(statement(3).statement(0).statement(2).entry, p[k]) by {
                            preserve(memory(p[k]), statement(3).statement(0).statement(2));
                        }
                        close();
                    } else {
                        have k == (j - 1);
                        have to_integer(k) == to_integer(at(region(4).entry, j));
                        have j != k by { close(); }
                        have separate(memory(p[j]), memory(p[k])) by {
                            apply(click::separation::separate_elements(p, j, k));
                        }
                        have separate(statement(3).statement(0).statement(2).footprint, memory(p[k])) by {
                            normalize() using { separate(memory(p[j]), memory(p[k])); };
                        }
                        have at(statement(3).statement(0).statement(2).exit, p[k]) == at(statement(3).statement(0).statement(2).entry, p[k]) by {
                            preserve(memory(p[k]), statement(3).statement(0).statement(2));
                        }

                        have at(statement(3).statement(0).statement(1).exit, p[k])
                            == at(statement(3).statement(0).statement(1).entry, p[j + 1]) by {
                            rewrite(k, at(region(4).entry, j));
                            close();
                        }
                        have p[k] == at(statement(3).statement(0).statement(1).entry, p[j + 1]) by {
                            close() using {
                                at(statement(3).statement(0).statement(1).exit, p[k]) == at(statement(3).statement(0).statement(1).entry, p[j + 1]);
                                at(statement(3).statement(0).statement(2).exit, p[k]) == at(statement(3).statement(0).statement(2).entry, p[k]);
                            };
                        }
                        have p[j] == at(region(7).entry, tmp) by { close(); }
                        close() using {
                            k == at(region(4).entry, j);
                            p[k] == at(statement(3).statement(0).statement(1).entry, p[j + 1]);
                            p[j] == at(region(7).entry, tmp);
                            at(region(7).entry, p[(j + 1)]) < at(region(7).entry, tmp);
                        };
                    }
                }
            } else {
                step();
                step();
                step();
                have forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] } by {
                    intro();
                    intro();
                    if k < (j - 1) {
                        have k < at(region(4).entry, j);
                        instantiate(forall (__click_q0: int32) { at(region(9).entry, 0) <= at(region(9).entry, __click_q0) and at(region(9).entry, 0) <= at(region(9).entry, __click_q0) and at(region(9).entry, __click_q0) < at(region(9).entry, j) implies at(region(9).entry, p[__click_q0]) <= at(region(9).entry, p[j]) }, k);
                        have p[k] <= p[j] by {
                            close() using {
                                at(region(9).entry, p[k]) <= at(region(9).entry, p[j]);
                                not at(region(9).entry, p[(j + 1)]) < at(region(9).entry, p[j]);
                            };
                        }
                        close();
                    } else {
                        have k == (j - 1);
                        have to_integer(k) == to_integer(at(region(4).entry, j));
                        rewrite(k, at(region(4).entry, j));
                        have at(region(9).entry, p[(j + 1)]) >= at(region(9).entry, p[j]);
                        close() using {
                            at(region(9).entry, p[(j + 1)]) >= at(region(9).entry, p[j]);
                        };
                    }
                }
            }
        }
    }
    have j == 2 by close();
    have p[j] == p[2] by { normalize() using { j == 2; }; }
    mark first_pass_done;
    step();
    loop {
        decreases (1 - j);
        invariant j >= 0 and j <= 1;
        invariant forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] };
        invariant forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] };
        initialize by {
            have j >= 0 and j <= 1 by {
                all {
                    j >= 0 => {
                        normalize();
                    }
                    j <= 1 => {
                        normalize();
                    }
                }
            }
            have forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] } by {
                intro(); intro();
                have at(first_pass_done, k < j) by close();
                instantiate(at(first_pass_done, forall (m: int32) {
                    0 <= m and 0 <= m and m < j implies p[m] <= p[j]
                }), k);
                have separate(memory(j), memory(p[k])) by close();
                have separate(statement(4).footprint, memory(p[k])) by {
                    normalize() using { separate(memory(j), memory(p[k])); };
                }
                have p[k] == at(first_pass_done, p[k]) by {
                    preserve(memory(p[k]), statement(4));
                }
                have separate(memory(j), memory(p[2])) by close();
                have separate(statement(4).footprint, memory(p[2])) by {
                    normalize() using { separate(memory(j), memory(p[2])); };
                }
                have p[2] == at(first_pass_done, p[2]) by {
                    preserve(memory(p[2]), statement(4));
                }
                close() using {
                    p[k] == at(first_pass_done, p[k]);
                    p[2] == at(first_pass_done, p[2]);
                    at(first_pass_done, p[j] == p[2]);
                    at(first_pass_done, p[k] <= p[j]);
                };
            }
            have forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] } by {
                enumerate();
            }
        }
        maintain by {
            if p[(j + 1)] < p[j] {
                have j == 0 by {
                    have j <= 0;
                    close() using {
                        j <= 0;
                        j >= 0;
                    };
                }
                have p[0] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0);
                    close();
                }
                have p[1] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1);
                    close();
                }
                mark before_swap;
                step();
                step();
                step();
                step();
                step();
                have at(before_swap, j) != 2 by { close(); }
                have at(before_swap, separate(memory(p[j]), memory(p[2]))) by {
                    apply(click::separation::separate_elements(p, at(before_swap, j), 2));
                }
                have separate(statement(5).statement(0).statement(1).footprint, memory(p[2])) by {
                    normalize() using { at(before_swap, separate(memory(p[j]), memory(p[2]))); };
                }
                have at(statement(5).statement(0).statement(1).exit, p[2]) == at(statement(5).statement(0).statement(1).entry, p[2]) by {
                    preserve(memory(p[2]), statement(5).statement(0).statement(1));
                }
                have j != 2 by { close(); }
                have separate(memory(p[j]), memory(p[2])) by {
                    apply(click::separation::separate_elements(p, j, 2));
                }
                have separate(statement(5).statement(0).statement(2).footprint, memory(p[2])) by {
                    normalize() using { separate(memory(p[j]), memory(p[2])); };
                }
                have at(statement(5).statement(0).statement(2).exit, p[2]) == at(statement(5).statement(0).statement(2).entry, p[2]) by {
                    preserve(memory(p[2]), statement(5).statement(0).statement(2));
                }
                have j != 0 by { close(); }
                have separate(memory(p[j]), memory(p[0])) by {
                    apply(click::separation::separate_elements(p, j, 0));
                }
                have separate(statement(5).statement(0).statement(2).footprint, memory(p[0])) by {
                    normalize() using { separate(memory(p[j]), memory(p[0])); };
                }
                have at(statement(5).statement(0).statement(2).exit, p[0]) == at(statement(5).statement(0).statement(2).entry, p[0]) by {
                    preserve(memory(p[0]), statement(5).statement(0).statement(2));
                }
                have at(statement(5).statement(0).statement(1).exit, p[0]) == at(before_swap, p[1]) by {
                    normalize() using { at(before_swap, j) == 0; };
                }
                have p[0] == at(before_swap, p[1]) by { close(); }
                have at(statement(5).statement(0).statement(2).exit, p[1]) == at(before_swap, p[0]) by {
                    normalize() using { at(before_swap, j) == 0; };
                }
                have p[1] == at(before_swap, p[0]) by { close(); }
                have p[2] == at(before_swap, p[2]) by { close(); }
                have p[0] <= p[2] by { close() using { p[0] == at(before_swap, p[1]); p[2] == at(before_swap, p[2]); at(before_swap, p[1] <= p[2]); }; }
                have p[1] <= p[2] by { close() using { p[1] == at(before_swap, p[0]); p[2] == at(before_swap, p[2]); at(before_swap, p[0] <= p[2]); }; }
                have forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] } by {
                    enumerate();
                }
                have j == 1 by {
                    rewrite(at(region(17).entry, j), at(region(17).entry, 0));
                    normalize();
                }
                have p[0] < p[1] by { close(); }
                have p[0] <= p[1] by {
                    close() using {
                        p[0] < p[1];
                    };
                }
                have forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] } by {
                    intro(); intro();
                    have k == 0 by close();
                    have p[j] == p[1] by { normalize() using { j == 1; }; }
                    rewrite(k, 0);
                    rewrite(p[j], p[1]);
                    close();
                }
            } else {
                have j == 0 by {
                    have j <= 0;
                    close() using {
                        j <= 0;
                        j >= 0;
                    };
                }
                have p[0] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0);
                    close();
                }
                have p[1] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1);
                    close();
                }
                mark before_swap;
                step();
                step();
                step();
                have j == 1 by {
                    rewrite(at(region(17).entry, j), at(region(17).entry, 0));
                    normalize();
                }
                have not p[1] < p[0] by { close(); }
                have p[0] <= p[1] by {
                    have p[0] <= p[1] by {
                        close() using {
                            not p[1] < p[0];
                        };
                    }
                    have p[0] <= p[1] by {
                        close() using {
                            not at(region(18).entry, p[1]) < at(region(18).entry, p[0]);
                        };
                    }
                    close() using {
                        at(region(18).entry, p[1]) >= at(region(18).entry, p[0]);
                    };
                }
                have forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] } by {
                    intro(); intro();
                    have k == 0 by close();
                    have p[j] == p[1] by { normalize() using { j == 1; }; }
                    rewrite(k, 0);
                    rewrite(p[j], p[1]);
                    close();
                }
            }
        }
    }
    have j == 1 by close();
    have p[j] == p[1] by { normalize() using { j == 1; }; }
    have p[0] <= p[1] by {
        have 0 < j by close();
        instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] }, 0);
        rewrite(p[1], p[j]);
        close();
    }
    have p[1] <= p[2] by {
        instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1);
        close();
    }
    have p[0] <= p[2] by {
        instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0);
        close();
    }
    step_until(function.exit);
    have sorted(p, 3) by {
        unfold(sorted(p, 3));
        unfold(sorted_range(p, 0, 3));
        enumerate();
    }
    close();
}
```

```expect
pass
```
