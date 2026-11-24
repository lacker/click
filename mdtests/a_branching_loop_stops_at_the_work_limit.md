# A branching loop stops at the deterministic work limit

With no written `maintain` proof, successive C branches multiply the paths the
loop closer checks. This fixture reaches the deterministic work limit while
checking the loop. The unit test
`implicit_tail_budget_errors_check_boundaries_without_exploring_paths`
checks the exact step and split boundaries directly.

```c filename=a_branching_loop_stops_at_the_work_limit.c
int32 f(int32 n, int32 a0, int32 a1, int32 a2, int32 a3, int32 a4, int32 a5, int32 a6, int32 a7, int32 a8, int32 a9, int32 a10) {
    int32 i;
    int32 x;
    i = 0;
    x = 0;
    while (i < n) {
        if (a0 > 0) { x = 1; }
        if (a1 > 0) { x = 1; }
        if (a2 > 0) { x = 1; }
        if (a3 > 0) { x = 1; }
        if (a4 > 0) { x = 1; }
        if (a5 > 0) { x = 1; }
        if (a6 > 0) { x = 1; }
        if (a7 > 0) { x = 1; }
        if (a8 > 0) { x = 1; }
        if (a9 > 0) { x = 1; }
        if (a10 > 0) { x = 1; }
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "a_branching_loop_stops_at_the_work_limit.c";

int32 f(int32 n, int32 a0, int32 a1, int32 a2, int32 a3, int32 a4, int32 a5, int32 a6, int32 a7, int32 a8, int32 a9, int32 a10) {
    requires 0 <= n;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    close();
}
```

```expect
fail: verification budget exhausted inside tactic `loop` in `f.contract` exhausted its deterministic smart work budget
```
