# Deleting a loop-entry guard introduction is rejected

This is `loop_entry_guard_intro.md` with the `intro()` deleted from the second
invariant's initialization certificate. The lowering guard in front of that
entry obligation is derivable but not exactly available, so it is part of the
goal that validation checks; without the introduction the certificate no longer
discharges the obligation it was retained for.

```c filename=loop_entry_guard_intro_required.c
int32 loop_entry_guard_intro_required(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return p[2];
}
```

```click
verifying "loop_entry_guard_intro_required.c";

int32 loop_entry_guard_intro_required(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures returns_third: result == 2;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == k
        };

        initialize by {
            have i >= 0 and i <= 3 by {
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have forall (k: int32) { 0 <= k and k < i implies p[k] == k } by {
                normalize();
            }
        }
        preserve by simp;
    }
    step();
    simp();
}
```

```expect
fail: certificate failed round-trip validation
```
