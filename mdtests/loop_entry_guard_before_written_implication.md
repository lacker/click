# A loop-entry guard in front of a written implication

The loop entry claim has exactly the written universal and implication.
Logical reads add no hidden viewability introduction. The negative companion
omits the introduction of the written antecedent.

```c filename=loop_entry_guard_before_written_implication.c
int32 loop_entry_guard_before_written_implication(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_entry_guard_before_written_implication.c";

int32 loop_entry_guard_before_written_implication(int32 p[3]) {
    consumes p[0..3];
    ensures returns_three: result == 3;
} by {
    step();
    step();
    loop {
        decreases 3 - i;
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == p[k]
        };

        initialize by {
            have i >= 0 and i <= 3 by {
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have forall (k: int32) { 0 <= k and k < i implies p[k] == p[k] } by {
                intro();
                intro();
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
pass
```
