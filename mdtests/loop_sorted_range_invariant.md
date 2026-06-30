# loop_sorted_range_invariant unfolds a predicate invariant

This checks that loop invariants can explicitly unfold a named predicate before
the loop verification condition is generated. The loop does not write through
`p`; it carries a sorted-range fact across iterations.

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

predicate sorted(int32 p[], int32 n) {
    sorted_range(p, 0, n)
}

predicate sorted_range(int32 p[], int32 lo, int32 hi) {
    forall (int32 i) {
        forall (int32 j) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

predicate all_le_range(int32 p[], int32 lo, int32 hi, int32 x) {
    forall (int32 k) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 loop_sorted_range_invariant(int32 p[3]) {
    requires valid_range(p[0..3]);
    requires sorted(p, 3);
    for loop(0) as carry_sorted {
        invariant i >= 0 and i <= 3 by auto;
        invariant sorted(p, 3) by {
            unfold(sorted);
            unfold(sorted_range);
        }
        immutable by frame;
    }
    ensures still_sorted: sorted(p, 3) by {
        symbolic_execute();
        loop_vc(carry_sorted);
        frame(carry_sorted);
        unfold(sorted);
        unfold(sorted_range);
        simp();
        close();
    }
}
```

```expect
pass
```
