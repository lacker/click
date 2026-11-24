# copy_n proves a symbolic copied segment

This checks that a symbolic pointer-copy loop can prove a quantified copied
segment. The destination prefix invariant says what has been copied so far; the
source invariant explicitly retains its function-entry contents. Containment
restricts source/destination separation to each selected cell; preservation
crosses the store and the index increment separately.

```c filename=copy_n_segment_invariant.c
int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        dst[i] = src[i];
        i = i + 1;
    }
    return i;
}
```

```click
verifying "copy_n_segment_invariant.c";

theorem int32_le_antisymmetric(left: int32, right: int32) {
    requires left <= right;
    requires right <= left;
    ensures left == right;
}

int32 copy_n_segment_invariant(int32 dst[], int32 src[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    consumes dst[0..n];
    views src[0..n];
    requires separate(memory(dst[0..n]), memory(src[0..n]));
    ensures returns_n: result == n;
    ensures source_unchanged: forall (k: int32) {
        0 <= k and k < n implies src[k] == old(src[k])
    };
    ensures copied_segment: forall (k: int32) {
        0 <= k and k < n implies dst[k] == old(src[k])
    };
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant forall (k: int32) {
            0 <= k and k < i implies dst[k] == old(src[k])
        };
        owns dst[0..n];
        invariant forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) };
        maintain by {
            mark iteration;
            have contains(memory(dst[0..n]), memory(dst[i])) by {
                apply(click::separation::contains_element(dst, 0, n, i));
            }
            have contains(memory(src[0..n]), memory(src[0..n])) by {
                apply(click::separation::contains_refl(memory(src[0..n])));
            }
            have separate(memory(dst[i]), memory(src[0..n])) by {
                apply(click::separation::separate_restrict(memory(dst[0..n]), memory(src[0..n]), memory(dst[i]), memory(src[0..n])));
            }
            step();
            have forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) } by {
                intro(); intro();
                instantiate(at(iteration, forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) }), k);
                have contains(memory(src[0..n]), memory(src[k])) by {
                    apply(click::separation::contains_element(src, 0, n, k));
                }
                have contains(memory(dst[i]), memory(dst[i])) by {
                    apply(click::separation::contains_refl(memory(dst[i])));
                }
                have separate(memory(dst[i]), memory(src[k])) by {
                    apply(click::separation::separate_restrict(memory(dst[i]), memory(src[0..n]), memory(dst[i]), memory(src[k])));
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
                    have k == at(iteration, i) by { close() using { k < i; not k < at(iteration, i); 0 <= at(iteration, i); at(iteration, i) < n; }; }
                    have k < n by { close() using { k == at(iteration, i); at(iteration, i) < n; }; }
                    instantiate(at(iteration, forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) }), k);
                    rewrite(k, at(iteration, i));
                    close();
                }
            }
        }

    }
    step();
    apply(int32_le_antisymmetric(
        at(loop(0).exit, i),
        at(loop(0).exit, n)
    ));
    have result == n by {
        close() using {
            at(loop(0).exit, i) == at(loop(0).exit, n);
        };
    }
    have forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) } by {
        close();
    }
    have forall (k: int32) { 0 <= k and k < n implies dst[k] == old(src[k]) } by {
        have forall (k: int32) {
            at(loop(0).exit, 0) <= at(loop(0).exit, k) and
                at(loop(0).exit, k) < at(loop(0).exit, n) implies
                at(loop(0).exit, dst[k]) == old(src[k])
        } by {
            rewrite(at(loop(0).exit, n), at(loop(0).exit, i));
            close();
        }
        have forall (k: int32) { 0 <= k and k < n implies dst[k] == old(src[k]) } by {
            close();
        }
        close();
    }
    close();
    close();
    close();
}
```

```expect
pass
```
