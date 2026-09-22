# A quantified invariant keeps viewability across a disjoint store

The loop writes only `visited`, while `next` remains held as a view.  The
quantified invariant over `next` therefore remains meaningful at the back
edge, including the viewability obligation generated for each guarded load.

```c filename=loop_quantified_viewability_across_disjoint_store.c
void walk(int32 *next, int32 *visited, int32 n) {
    int32 i = 0;
    while (i < n) {
        visited[i] = 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_quantified_viewability_across_disjoint_store.c";

void walk(int32 *next, int32 *visited, int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    views next[0..n];
    owns visited[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k]
    };
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) {
            0 <= k and k < n implies 0 <= next[k]
        };
        views next[0..n];
        owns visited[0..n];
        initialize by { simp(); }
        preserve by {
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
