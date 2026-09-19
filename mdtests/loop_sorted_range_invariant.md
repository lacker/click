# loop_sorted_range_invariant unfolds a predicate invariant

This checks that loop invariants can explicitly unfold a named predicate before
the loop verification condition is generated. The loop does not write through
`p`; it carries a sorted-range fact across iterations. Initialization explicitly
introduces the two lowering-generated viewability guards, the two indices, and
their range constraint, then instantiates the existing sortedness fact.

```c filename=loop_sorted_range_invariant.c
int32 loop_sorted_range_invariant(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_sorted_range_invariant.c";

predicate sorted(p: int32[], n: int32) {
    sorted_range(p, 0, n)
}

predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 loop_sorted_range_invariant(int32 p[3]) {
    requires viewable(p[0..3]);
    requires sorted(p, 3);
    ensures still_sorted: sorted(p, 3);
} by {
    unfold(sorted);
    unfold(sorted_range);
    step();
    step();
    loop as carry_sorted {
        decreases 3 - i;
        invariant i >= 0 and i <= 3;
        invariant sorted(old(p), 3);

        initialize by {
            unfold(sorted);
            unfold(sorted_range);
            have i >= 0 and i <= 3 by {
                both { normalize(); } and { normalize(); }
            }
            have sorted(old(p), 3) by {
                intro();
                intro();
                intro();
                intro();
                intro();
                instantiate(forall (i: int32) {
                    forall (j: int32) {
                        0 <= i and 0 <= j and 0 <= i and i < j and j < 3 implies p[i] <= p[j]
                    }
                }, i) using {}
                instantiate(forall (j: int32) {
                    0 <= i and 0 <= j and 0 <= i and i < j and j < 3 implies p[i] <= p[j]
                }, j) using {
                    0 <= i and 0 <= j and 0 <= i and i < j and j < 3;
                }
                assumption();
            }
        }
        preserve by {
            unfold(sorted);
            unfold(sorted_range);
        }
    }
    step();
    unfold(sorted);
    unfold(sorted_range);
    simp();
}
```

```expect
pass
```
