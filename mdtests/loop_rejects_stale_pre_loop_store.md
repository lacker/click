# A loop that overwrites memory rejects a stale pre-loop value

The loop sets `p[0] = 100`, so a post-loop read of `p[0]` must not still
observe the pre-loop value `7`. The bound is symbolic, so this exercises the
loop verification-condition / havoc path: loop memory havoc drops concrete
cells the loop body may clobber, so this false postcondition is rejected.

```c filename=loop_rejects_stale_pre_loop_store.c
int32 loop_rejects_stale_pre_loop_store(int32 p[], int32 n) {
    int32 i;
    p[0] = 7;
    i = 0;
    while (i < n) {
        p[0] = 100;
        i = i + 1;
    }
    return p[0];
}
```

```click
verifying "loop_rejects_stale_pre_loop_store.c";

int32 loop_rejects_stale_pre_loop_store(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires valid_range(p, 4);
    loop 0 {
        invariant i >= 0 and i <= n by auto;
    }
    ensures stale: result == 7 by auto;
}
```

```expect
fail: loop_rejects_stale_pre_loop_store.stale
```
