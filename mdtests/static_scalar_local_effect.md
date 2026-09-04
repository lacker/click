# static scalar writes require an authorized effect

Static storage is an external memory object for effect certification. A
function that mutates it must declare the corresponding mutable footprint.

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
    immutable;
    ensures result == old(calls) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
