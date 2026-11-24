# An interface fact needs its terms defined in each arm

This is `bubble_pass3_max_suffix` without `defined(j + 1)` in the interface
or its arms. Both arms establish the stated ordering facts, including explicit
preservation of earlier cells across the swap. The join refuses the interface:
`p[j + 1]` requires `j + 1` not to overflow, and that condition must be carried
along with the ordering facts.

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
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range(p, 0, j, p[j]));
            close();
        }
        maintain by {
            unfold(all_le_range(p, 0, j, p[j]));
            have p[0] <= p[j] by {
                if j == 0 {
                    rewrite(j, 0);
                    close();
                } else {
                    close();
                }
            }
            branch ensuring {
                fact p[j] <= p[j + 1];
                fact all_le_range(p, 0, j, p[j + 1]);
            } {
                true => {
                    step();
                    step();
                    step();
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
                            rewrite(k, 0);
                            close();
                        }
                    }
                }
                false => {
                    have p[j] <= p[j + 1];
                    have all_le_range(p, 0, j, p[j + 1]) by {
                        unfold(all_le_range(p, 0, j, p[j + 1]));
                        close();
                    }
                }
            }
            step();
            unfold(all_le_range(p, 0, j, p[j + 1]));
        }
        owns p[0..3];
    }
    step();
    unfold(all_le_range(p, 0, j, p[j + 1]));
    close();
}
```

```expect
fail: could not abstract `branch ensuring` fact
```
