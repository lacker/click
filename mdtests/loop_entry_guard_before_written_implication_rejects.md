# Dropping one recorded loop-entry introduction is rejected

This is `loop_entry_guard_before_written_implication.md` with one `intro()`
removed from the second invariant's initialization certificate. The entry
obligation's recorded chain has three introducible nodes — the hidden
loadability guard, the written universal, and the written implication — so two
introductions leave the written implication as the goal, and `normalize` does
not close it.

```c filename=loop_entry_guard_before_written_implication_rejects.c
int32 loop_entry_guard_before_written_implication_rejects(int32 p[3]) {
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
verifying "loop_entry_guard_before_written_implication_rejects.c";

int32 loop_entry_guard_before_written_implication_rejects(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures returns_three: result == 3;
} by {
    step();
    step();
    loop {
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
fail: certificate failed round-trip validation
```
