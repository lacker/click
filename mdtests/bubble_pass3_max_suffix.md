# bubble_pass3 moves the maximum to the end

This checks the first loop-invariant sorting step: one bubble-sort pass over
three cells should establish that every earlier cell is less than or equal to
the final cell. It intentionally does not prove permutation.

The invariant depends on whether the swap ran, so the two arms of the C `if`
cannot be joined keeping only what they agree on, which is all the automatic
loop closer does at an `if`. The body is written out, and its `branch` says
what both arms establish: after the `if`, `p[j] <= p[j + 1]`, and every
earlier cell is at most `p[j + 1]`. Each arm proves both from what it did,
and the rest of the iteration is checked once on the path that leaves the
`if`.

The interface includes `defined(j + 1)`, proved in both arms. Its facts
can use `p[j + 1]` only while carrying the condition that `j + 1` does not
overflow
([`an_interface_fact_needs_its_terms_defined_in_each_arm.md`](an_interface_fact_needs_its_terms_defined_in_each_arm.md)).

The swap arm explicitly preserves earlier cells across each store using
element separation and explicit preservation steps.

```c filename=bubble_pass3.c
int32 bubble_pass3(int32 p[3]) {
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
    return 0;
}
```

```click
import click::separation;
verifying "bubble_pass3.c";

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_pass3(int32 p[3]) {
    consumes p[0..3];
    ensures max_at_end: all_le_range(p, 0, 2, p[2]);
} by {
    step();
    step();
    step();
    loop {
        decreases 2 - j;
        invariant j >= 0 and j <= 2;
        invariant forall (m: int32) { 0 <= m and 0 <= m and m < j implies p[m] <= p[j] };
        initialize by close();
        maintain by {
            branch ensuring {
                fact defined(j + 1);
                fact p[j] <= p[j + 1];
                fact forall (k: int32) { 0 <= k and 0 <= k and k < j implies defined(j + 1) };
                fact forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j + 1] };
            } {
                true => {
                    mark before_swap;
                    step();
                    step();
                    step();
                    have defined(j + 1);
                    have p[j] <= p[j + 1];
                    have all_le_range(p, 0, j, p[j + 1]) by {
                        if j == 0 {
                            unfold(all_le_range(p, 0, j, p[j + 1]));
                            close();
                        } else {
                            have j == 1 by close();
                            have separate(memory(p[1]), memory(p[0])) by {
                                apply(separation::separate_elements(p, 1 as uint64, 0 as uint64));
                            }
                            have separate(memory(p[2]), memory(p[0])) by {
                                apply(separation::separate_elements(p, 2 as uint64, 0 as uint64));
                            }
                            have separate(memory(p[j]), memory(p[0])) by { rewrite(j, 1); close(); }
                            have separate(memory(p[j + 1]), memory(p[0])) by { rewrite(j, 1); close(); }
                            have separate(loop(0).statement(0).statement(1).footprint, memory(p[0])) by {
                                normalize() using { separate(memory(p[j]), memory(p[0])); };
                            }
                            have at(loop(0).statement(0).statement(1).exit, p[0]) == at(loop(0).statement(0).statement(1).entry, p[0]) by {
                                preserve(memory(p[0]), loop(0).statement(0).statement(1));
                            }
                            have separate(loop(0).statement(0).statement(2).footprint, memory(p[0])) by {
                                normalize() using { separate(memory(p[j + 1]), memory(p[0])); };
                            }
                            have at(loop(0).statement(0).statement(2).exit, p[0]) == at(loop(0).statement(0).statement(2).entry, p[0]) by {
                                preserve(memory(p[0]), loop(0).statement(0).statement(2));
                            }
                            unfold(all_le_range(p, 0, j, p[j + 1]));
                            intro(); intro();
                            have k == 0 by close();
                            have at(before_swap, 0 <= k and 0 <= k and k < j) by close();
                            instantiate(at(before_swap, forall (m: int32) {
                                0 <= m and 0 <= m and m < j implies p[m] <= p[j]
                            }), k);
                            have p[k] == at(before_swap, p[k]) by {
                                rewrite(k, 0);
                                close() using {
                                    at(loop(0).statement(0).statement(1).exit, p[0]) == at(loop(0).statement(0).statement(1).entry, p[0]);
                                    at(loop(0).statement(0).statement(2).exit, p[0]) == at(loop(0).statement(0).statement(2).entry, p[0]);
                                };
                            }
                            have p[j + 1] == at(before_swap, p[j]) by { close(); }
                            close() using {
                                p[k] == at(before_swap, p[k]);
                                p[j + 1] == at(before_swap, p[j]);
                                at(before_swap, p[k] <= p[j]);
                            };
                        }
                    }
                    have forall (k: int32) { 0 <= k and 0 <= k and k < j implies defined(j + 1) } by {
                        intro(); intro(); close();
                    }
                    unfold(all_le_range(p, 0, j, p[j + 1]));
                }
                false => {
                    have defined(j + 1);
                    have p[j] <= p[j + 1];
                    have all_le_range(p, 0, j, p[j + 1]) by {
                        unfold(all_le_range(p, 0, j, p[j + 1]));
                        intro(); intro();
                        instantiate(forall (i: int32) { 0 <= i and 0 <= i and i < j implies p[i] <= p[j] }, k);
                        close() using { p[k] <= p[j]; p[j] <= p[j + 1]; };
                    }
                    have forall (k: int32) { 0 <= k and 0 <= k and k < j implies defined(j + 1) } by {
                        intro(); intro(); close();
                    }
                    unfold(all_le_range(p, 0, j, p[j + 1]));
                }
            }
            step();
            close();
        }
        owns p[0..3];
    }
    have j == 2 by close();
    have p[j] == p[2] by { normalize() using { j == 2; }; }
    have all_le_range(p, 0, 2, p[2]) by {
        unfold(all_le_range(p, 0, 2, p[2]));
        intro(); intro();
        have k < j by { close() using { j == 2; k < 2; }; }
        instantiate(forall (m: int32) { 0 <= m and 0 <= m and m < j implies p[m] <= p[j] }, k);
        rewrite(p[2], p[j]);
        close();
    }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
