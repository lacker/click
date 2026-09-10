# static scalar writes require authorized ownership

Static storage is an external memory object for ownership certification. A
function that mutates it must declare the corresponding owned footprint.

```c filename=static_scalar_local_effect.c
int32 increment() {
    static int32 calls;
    calls = calls + 1;
    return calls;
}
```

```click
verifying "static_scalar_local_effect.c";

int32 increment() {
    requires calls < 1000;
    ensures result == old(calls) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
