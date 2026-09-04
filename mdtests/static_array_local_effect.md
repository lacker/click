# static array writes require an authorized effect

Static array storage is an external memory object for effect certification. A
function that mutates it must declare the corresponding mutable footprint.

```c filename=static_array_local_effect.c
int32 increment() {
    static int32 values[2];
    values[0] = values[0] + 1;
    return values[0];
}
```

```click
verifying "static_array_local_effect.c";

int32 increment() {
    immutable;
    ensures result == old(values[0]) + 1 by auto;
}
```

```expect
fail: outside the mutable footprint
```
