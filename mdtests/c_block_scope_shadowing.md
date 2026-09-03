# block-scoped declarations keep distinct identities

Declarations in nested C blocks may shadow an outer object. Click resolves
each source spelling to the object that is live at that point, while the
kernel receives distinct local block identities. Taking the inner object's
address must not change the value returned from the outer scope.

```c filename=c_block_scope_shadowing.c
int32 shadow_with_address(int32 c) {
    int32 value = 10;
    int32 *outer = &value;
    if (c < 0) {
        int32 value = 5;
        int32 *inner = &value;
        *inner = 6;
    }
    return value;
}
```

```click
verifying "c_block_scope_shadowing.c";

int32 shadow_with_address(int32 c) {
    ensures result == 10 by auto;
}
```

```expect
pass
```
