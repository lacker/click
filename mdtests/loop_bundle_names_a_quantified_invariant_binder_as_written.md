# A quantified bundle member names its binder as the invariant wrote it

The back edge of
[`loop_initialize_narrows_a_held_range_under_a_universal.md`](loop_initialize_narrows_a_held_range_under_a_universal.md)
owes the extent bound of `viewable(a[0..k])` for every `k` the quantified
invariant covers, as its own bundle member
`forall (k: int32) { 0 <= k and k <= n implies (-2147483648 ^ k) <= -1073741825 }`.
The kernel builds that member, so nothing written spells it; the closer
synthesizes its source form. The synthesized binder used to be a generated
`__click_q0`, so a proof that focused the member with `both` and introduced
it could not write `extract(0 <= k)`: `k` was unbound. The binder now takes
the name the invariant gave it, and the explicit proof below names `k` the
way the invariant does.

```c filename=loop_bundle_names_a_quantified_invariant_binder_as_written.c
int32 count_up(int32 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_bundle_names_a_quantified_invariant_binder_as_written.c";

int32 count_up(int32 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k <= n);
                simp();
            }
            simp();
        }
        preserve by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k <= n);
                simp();
            }
            close_invariants by {
                both { simp(); } and {
                    both { simp(); } and {
                        both {
                            intro();
                            intro();
                            extract(0 <= k);
                            extract(k <= n);
                            arithmetic() using { 0 <= k; k <= n; n <= 1073741823; }
                        } and {
                            both {
                                intro();
                                intro();
                                intro();
                                assumption();
                            } and {
                                both {
                                    arithmetic() using {
                                        at(statement(5).entry, 0) <= at(statement(5).entry, i);
                                        at(statement(5).entry, i) < at(statement(5).entry, n);
                                    }
                                } and {
                                    arithmetic() using {
                                        at(statement(5).entry, 0) <= at(statement(5).entry, i);
                                        at(statement(5).entry, i) < at(statement(5).entry, n);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
