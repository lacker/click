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
    requires valid_range(p, 12);

    for loop(0) {
        invariant i >= 0 by auto;
        invariant i <= 3 by auto;
    }

    ensures writes_first: p[0] == 0 by auto;
    ensures writes_second: p[1] == 1 by auto;
    ensures writes_third: p[2] == 2 by auto;
    ensures returns_third: result == 2 by auto;
}
```

```expect
pass
```
