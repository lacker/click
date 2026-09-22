# A checked store remains available after a ranked-loop return arm

The continuing arm of a proof-level `if` remains at the post-store state after
the sibling arm returns from the function. The checked store therefore makes
its written value available immediately, before the rest of the iteration.

```c filename=post_store_fact_after_ranked_loop_return.c
int32 scan(int32 *b, int32 n, int32 to) {
    for (int32 i = 0; i < n; i++) {
        if (i == to) return 1;
        b[i] = 1;
    }
    return 0;
}
```

```click
verifying "post_store_fact_after_ranked_loop_return.c";

int32 scan(int32 *b, int32 n, int32 to) {
    owns b[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        owns b[0..n];
        initialize by { simp(); }
        preserve by {
            if i == to {
                step();
                step();
            } else {
                step();
                step();
                step();
                have b[i] == 1 by { simp(); }
                have b[i] != 0 by { simp(); }
                step();
                close_invariants();
            }
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
