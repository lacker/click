# A ranked loop body may return from one branch

A return completes that execution path rather than reaching the loop back
edge. The continuing arm still executes one complete iteration and closes the
invariants and ranking obligation normally.

```c filename=return_inside_ranked_loop_body.c
int32 scan(int32 *b, int32 n, int32 to) {
    for (int32 i = 0; i < n; i++) {
        if (i == to) return 1;
        b[i] = 1;
    }
    return 0;
}

int32 scan_auto(int32 *b, int32 n, int32 to) {
    for (int32 i = 0; i < n; i++) {
        if (i == to) return 1;
        b[i] = 1;
    }
    return 0;
}
```

```click
verifying "return_inside_ranked_loop_body.c";

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
                step();
                close_invariants();
            }
        }
    }
    execute();
    simp();
}

int32 scan_auto(int32 *b, int32 n, int32 to) {
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
    }
    execute();
    simp();
}
```

```expect
pass
```
