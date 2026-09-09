# A loop rejects a stale function-local static value

Function-local static storage is shared across calls and is not a stack local.
The loop writes `g`, so a weak loop invariant must not preserve its pre-loop
value at the loop head.

```c filename=loop_static_not_havoced_rejected.c
int32 loop_static_not_havoced_rejected(int32 n) {
    static int32 g = 0;
    int32 i = 0;
    g = 0;
    while (i < n) {
        if (g < 100) {
            g = g + 1;
        }
        i = i + 1;
    }
    return g;
}
```

```click
verifying "loop_static_not_havoced_rejected.c";

int32 loop_static_not_havoced_rejected(int32 n) {
    requires n >= 0 and n <= 100;
    mutable &g[0..1];
    ensures stale: result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    frame();
    simp();
}
```

```expect
fail: loop_static_not_havoced_rejected.stale
```
