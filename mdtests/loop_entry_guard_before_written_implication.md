# A loop-entry guard in front of a written implication

The kernel builds this loop's entry obligations itself, and each one now
carries the head chain the lowering recorded for it. The second invariant's
chain is a hidden loadability guard, then the written universal, then the
written implication in its body, so the initialization certificate spells one
`intro()` per node in exactly that order: the first keeps the written Surface
goal focused while the hidden guard is introduced, the second binds `k`, and
only the third consumes the written antecedent. Pairing those nodes by
constructor shape cannot distinguish the first from the third.

Planning and independent validation read the same obligation and the same
record, so the certificate below checks identically at both. See
`loop_entry_guard_before_written_implication_rejects.md` for the same
certificate with one introduction removed.

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
