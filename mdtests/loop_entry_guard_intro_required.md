# Deleting a loop-entry guard introduction is rejected

A quantified entry claim still requires a proof of the written quantifier;
`normalize()` alone cannot discharge it. There is no implicit read guard.

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
fail: `normalize` goal did not normalize to true
```
