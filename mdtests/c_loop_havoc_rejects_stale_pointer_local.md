# a pointer local advanced by the loop does not keep its entry value

`p` is reassigned on every iteration, so after the loop it points at
`arr[n]`, not `arr[0]`. Without an invariant relating `p` to the loop index,
the loop head havocs `p`, so the post-loop load through `p` has no
view and the stale-value postcondition cannot be proved.

```c filename=c_loop_havoc_rejects_stale_pointer_local.c
int32 stale_ptr(int32 arr[], int32 n, int32 cap) {
    int32* p;
    int32 i;
    p = arr;
    i = 0;
    while (i < n) {
        i = i + 1;
        p = p + 1;
    }
    return *p;
}
```

```click
verifying "c_loop_havoc_rejects_stale_pointer_local.c";

int32 stale_ptr(int32 arr[], int32 n, int32 cap) {
    requires 0 <= n;
    requires n < cap;
    requires 1 <= cap;
    views arr[0..cap];
    ensures stale: result == arr[0];
} by {
    step();
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
fail: missing resource fact `views symbolic-pointer:
```
