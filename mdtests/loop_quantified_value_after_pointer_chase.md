# A pointer-chasing loop retains its quantified value invariant

The loop changes `visited` and advances `cur` from `next[cur]`, but never
changes `next`. The quantified bounds on every `next` element must therefore
remain available at the back edge, while their instance at the old `cur`
establishes the scalar bounds on the new `cur`.

```c filename=loop_quantified_value_after_pointer_chase.c
void walk(int32 *next, int32 *visited, int32 n) {
    int32 cur = 0;
    int32 i = 0;
    while (i < n) {
        visited[cur] = 1;
        cur = next[cur];
        i = i + 1;
    }
}
```

```click
verifying "loop_quantified_value_after_pointer_chase.c";

void walk(int32 *next, int32 *visited, int32 n) {
    requires 1 <= n;
    requires n <= 1073741823;
    views next[0..n];
    owns visited[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant 0 <= cur;
        invariant cur < n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k] and next[k] < n
        };
        views next[0..n];
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
            have 0 <= next[cur] and next[cur] < n by {
                instantiate(forall (k: int32) {
                    0 <= k and k < n implies 0 <= next[k] and next[k] < n
                }, cur) using { 0 <= cur; cur < n; }
                assumption();
            }
            step();
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
