# a block-scoped declaration may not shadow an enclosing local

```c filename=c_block_scope_rejects_shadowing_local.c
int32 shadow(int32 c) {
    int32 y = 10;
    if (c < 0) { int32 y = 5; } else { int32 y = 5; }
    return y;
}
```

```click
verifying "c_block_scope_rejects_shadowing_local.c";

int32 shadow(int32 c) {
    ensures result == 10 by auto;
}
```

```expect
fail: `y` is already declared in an enclosing scope
```
