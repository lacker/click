# A loop-entry guard is introduced explicitly

Lowering wraps this loop's quantified entry obligation in a loadability guard
that has no Surface connective. The guard is derivable at entry but is not
exactly among the available facts, so it stays part of the checked goal and the
initialization certificate discharges it with an explicit `intro()`.

Planning and independent validation compute that goal the same way, so the
certificate written below is checked against the goal it was built for. See
`loop_entry_guard_intro_required.md` for the same certificate with the
introduction deleted.

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
