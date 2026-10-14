# a tied lexicographic call inside a loop must still descend

The second loop now calls `grid(m, i + 1)`. On the last iteration `i + 1`
equals `n`, so the call ties both components, and the descent the call owes
is not established by the loop's invariants.

```c filename=c_decreases_lexicographic_recursion_under_loops_must_descend.c
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
        result = grid(m, i + 1);
        i = i + 1;
    }
    return result;
}
```

```click
verifying "c_decreases_lexicographic_recursion_under_loops_must_descend.c";

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
fail: `(m, n)` decreases at the recursive call
```
