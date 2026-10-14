# recursive calls inside loops descend in a lexicographic function measure

Each call's descent is an ordinary obligation at the call, so the loop
invariants that bound the counter are what discharge it. The first loop calls
`grid(i, 1000)` with `i < m`, lowering the first component while the second
grows. The second loop calls `grid(m, i)` with `i < n`, tying the first
component and lowering the second. Both calls are ranked by the one function
measure `(m, n)` read at `grid`'s entry, while each loop is ranked by its own
measure.

```c filename=c_decreases_lexicographic_recursion_under_loops.c
int32 grid(int32 m, int32 n) {
    int32 i;
    int32 result;
    i = 0;
    result = 0;
    while (i < m) {
        result = grid(i, 1000);
        i = i + 1;
    }
    i = 0;
    while (i < n) {
        result = grid(m, i);
        i = i + 1;
    }
    return result;
}
```

```click
verifying "c_decreases_lexicographic_recursion_under_loops.c";

int32 grid(int32 m, int32 n) {
    decreases (m, n);
    requires m >= 0;
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases m - i;
        invariant i >= 0;
        invariant i <= m;
        invariant result == 0;
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        invariant result == 0;
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
