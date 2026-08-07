# fill3 verifies an array-parameter pointer loop

This checks C-style array parameter syntax, pointer-loop stores, loop
invariants, and post-state memory claims in one small example.

```c filename=fill3_array_loop.c
int32 fill3_array_loop(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return p[2];
}
```

```click
verifying "fill3_array_loop.c";

int32 fill3_array_loop(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures writes_first: p[0] == 0;
    ensures writes_second: p[1] == 1;
    ensures writes_third: p[2] == 2;
    ensures returns_third: result == 2;
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == k
        };

        initialize by simp;
        preserve by {
            step();
            step();
            have i == at(statement(3).entry, i) + 1 by simp;
            simp();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
