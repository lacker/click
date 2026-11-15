# frontier facts, statement states, and marks act at the current frontier

This checks the frontier proof shapes from the proof-workflow concept page:
`have` before a loop sees the facts the preceding steps established,
`step_until` pauses at a statement whose entry state a later `have`
reads, and `mark` names the reached state for a later comparison.

```c filename=fill_zero.c
int32 fill_zero(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = 0;
        i = i + 1;
    }
    return i;
}
```

```c filename=state_y.c
int32 state_y(int32 x) {
    int32 y;
    y = 1;
    x = 2;
    x = 3;
    y = y + 1;
    return y;
}
```

```c filename=bump_first.c
int32 bump_first(int32 p[]) {
    p[0] = p[0] + 1;
    return 0;
}
```

```click
verifying "fill_zero.c";
verifying "state_y.c";
verifying "bump_first.c";

int32 fill_zero(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns p[0..n];
    ensures result == n;
} by {
    step();
    step();
    have i == 0 by {
        solve();
    }
    loop as fill {
        decreases n - i;
        owns p[0..n];
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    solve();
}

int32 state_y(int32 x) {
    ensures result >= 0;
} by {
    step_until(region(4));
    have y >= 0 by {
        solve();
    }
    step();
    have at(region(4).entry, y) >= 0 by {
        known();
    }
}

int32 bump_first(int32 p[]) {
    requires p[0] < 100;
    owns p[0..1];
    ensures p[0] == old(p[0]) + 1;
} by {
    mark before_write;
    step();
    have p[0] == at(before_write, p[0]) + 1 by solve();
}
```

```expect
pass
```
