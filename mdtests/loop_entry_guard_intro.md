# A loop-entry guard is introduced explicitly

The quantified loop entry claim can be enumerated directly. Logical reads
do not insert an extra viewability guard before the universal.

```c filename=loop_entry_guard_intro.c
int32 loop_entry_guard_intro(int32 p[3]) {
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
verifying "loop_entry_guard_intro.c";

int32 loop_entry_guard_intro(int32 p[3]) {
    consumes p[0..3];
    ensures returns_third: result == 2;
} by {
    step();
    step();
    loop {
        decreases 3 - i;
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
                enumerate();
            }
        }
        preserve by simp;
    }
    step();
    simp();
}
```

```expect
pass
```
