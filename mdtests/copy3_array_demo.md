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
                all {
                    i >= 0 => {
                        close();
                    }
                    i <= 3 => {
                        close();
                    }
                }
            }
            have forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) } by {
                intro();
                intro();
                close();
            }
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                enumerate();
            }
        }
        maintain by {
            mark iteration;
            have contains(memory(dst[0..3]), memory(dst[i])) by {
                apply(click::separation::contains_element(dst, 0, 3, i));
            }
            have contains(memory(src[0..3]), memory(src[0..3])) by {
                apply(click::separation::contains_refl(memory(src[0..3])));
            }
            have separate(memory(dst[i]), memory(src[0..3])) by {
                apply(click::separation::separate_restrict(memory(dst[0..3]), memory(src[0..3]), memory(dst[i]), memory(src[0..3])));
            }
            step();
            have forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) } by {
                intro(); intro();
                instantiate(at(iteration, forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) }), k);
                have contains(memory(src[0..3]), memory(src[k])) by {
                    apply(click::separation::contains_element(src, 0, 3, k));
                }
                have contains(memory(dst[i]), memory(dst[i])) by {
                    apply(click::separation::contains_refl(memory(dst[i])));
                }
                have separate(memory(dst[i]), memory(src[k])) by {
                    apply(click::separation::separate_restrict(memory(dst[i]), memory(src[0..3]), memory(dst[i]), memory(src[k])));
                }
                have separate(statement(2).statement(0).footprint, memory(src[k])) by {
                    close() using { separate(memory(dst[i]), memory(src[k])); };
                }
                have src[k] == at(iteration, src[k]) by {
                    preserve(memory(src[k]), statement(2).statement(0));
                }
                close();
            }
            step();
            have forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) } by {
                intro(); intro();
                if k < at(iteration, i) {
                    have 0 <= k and k < i;
                    instantiate(at(iteration, forall (k: int32) { 0 <= k and k < i implies dst[k] == old(src[k]) }), k);
                    have k != at(iteration, i) by { close() using { k < at(iteration, i); }; }
                    have at(iteration, separate(memory(dst[i]), memory(dst[k]))) by {
                        apply(click::separation::separate_elements(dst, at(iteration, i), k));
                    }
                    have separate(statement(2).statement(0).footprint, memory(dst[k])) by {
                        close() using { at(iteration, separate(memory(dst[i]), memory(dst[k]))); };
                    }
                    have at(statement(2).statement(0).exit, dst[k]) == at(iteration, dst[k]) by {
                        preserve(memory(dst[k]), statement(2).statement(0));
                    }
                    have separate(statement(2).statement(1).footprint, memory(dst[k])) by { close() using { }; }
                    have dst[k] == at(statement(2).statement(1).entry, dst[k]) by {
                        preserve(memory(dst[k]), statement(2).statement(1));
                    }
                    close();
                } else {
                    have k == at(iteration, i) by { close() using { k < i; not k < at(iteration, i); 0 <= at(iteration, i); at(iteration, i) < 3; }; }
                    have k < 3 by { close() using { k == at(iteration, i); at(iteration, i) < 3; }; }
                    instantiate(at(iteration, forall (k: int32) { 0 <= k and k < 3 implies src[k] == old(src[k]) }), k);
                    rewrite(k, at(iteration, i));
                    close();
                }
            }
        }
    }
    have dst[0] == old(src[0]) by {
        have at(loop(0).exit, 0) <= at(loop(0).exit, 0) and at(loop(0).exit, 0) < at(loop(0).exit, i);
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 0);
        close();
    }
    have dst[1] == old(src[1]) by {
        have at(loop(0).exit, 0) <= at(loop(0).exit, 1) and at(loop(0).exit, 1) < at(loop(0).exit, i);
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 1);
        close();
    }
    have dst[2] == old(src[2]) by {
        have at(loop(0).exit, 0) <= at(loop(0).exit, 2) and at(loop(0).exit, 2) < at(loop(0).exit, i);
        instantiate(forall (k: int32) { at(loop(0).exit, 0) <= at(loop(0).exit, k) and at(loop(0).exit, k) < at(loop(0).exit, i) implies at(loop(0).exit, dst[k]) == old(src[k]) }, 2);
        close();
    }
    step();
    have dst[0] == old(src[0]) by {
        close();
    }
    have dst[1] == old(src[1]) by {
        close();
    }
    have dst[2] == old(src[2]) by {
        close();
    }
    have result == old(src[2]) by {
        close();
    }
    close();
    close();
    close();
    close();
}
```

```expect
pass
```
