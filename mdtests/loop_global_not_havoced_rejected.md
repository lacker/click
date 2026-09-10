# A loop rejects a stale global value

The loop writes the file-scope global `g`, so a weak loop invariant must not
let the postcondition retain its pre-loop value. This exercises both the
modified-name and memory-write sides of loop havoc for a by-name global
assignment.

```c filename=loop_global_not_havoced_rejected.c
int32 g = 0;

int32 loop_global_not_havoced_rejected(int32 n) {
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
verifying "loop_global_not_havoced_rejected.c";

int32 loop_global_not_havoced_rejected(int32 n) {
    requires n >= 0 and n <= 100;
    owns &g[0..1];
    ensures stale: result == 0;
} by {
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}
```

```expect
fail: loop_global_not_havoced_rejected.stale
```
