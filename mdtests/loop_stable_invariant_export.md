# Stable loop invariants retain their declared export position

A loop invariant that is already available before the loop still occupies its
declared position in the verified loop rule's exported invariant vector. A
duplicate declaration keeps its own position as well. An
unrelated sibling fact is also present in the ambient context but is not
mistaken for an invariant export.

```c filename=loop_stable_invariant_export.c
int32 fill_tail(int32 p[], int32 n, int32 untouched[]) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_stable_invariant_export.c";

int32 fill_tail(int32 p[], int32 n, int32 untouched[]) {
    requires n >= 1;
    requires n <= 10;
    requires loadable(untouched[0..1]);
    consumes p[0..n];
    consumes untouched[0..1];
    ensures result == n;
} by {
    step();
    step();
    loop {
        invariant n <= 10;
        invariant n <= 10;
        invariant i >= 1 and i <= n;
        invariant i >= 1 and i <= n;

        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants by { simp(); }
        }
    }
    have at(loop(0).exit, n) <= at(loop(0).exit, 10) by { assumption(); }
    have at(loop(0).exit, i) >= at(loop(0).exit, 1) and
        at(loop(0).exit, i) <= at(loop(0).exit, n) by { assumption(); }
    have i == n by { simp(); }
    step();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
