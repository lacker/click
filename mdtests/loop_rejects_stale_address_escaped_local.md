# A loop rejects a stale local written through an escaped address

`x`'s address escapes into `p` before the loop, and the loop writes `*p = 100`.
So `x` is overwritten by the loop, even though it is never assigned by name.
The bound is symbolic (forces the havoc path), and loop havoc must not preserve
its stale pre-loop value `7` for an address-escaped local.

```c filename=loop_rejects_stale_address_escaped_local.c
int32 loop_rejects_stale_address_escaped_local(int32 n) {
    int32 x;
    int32* p;
    int32 i;
    x = 7;
    p = &x;
    i = 0;
    while (i < n) {
        *p = 100;
        i = i + 1;
    }
    return x;
}
```

```click
verifying "loop_rejects_stale_address_escaped_local.c";

int32 loop_rejects_stale_address_escaped_local(int32 n) {
    requires n >= 1 and n <= 2147483647;
    loop 0 {
        invariant i >= 0 and i <= n by auto;
    }
    ensures stale: result == 7 by auto;
}
```

```expect
fail: loop_rejects_stale_address_escaped_local.stale
```
