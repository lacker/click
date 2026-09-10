# nested automatic block re-entry has fresh lifetimes

Nested scopes retain their distinct lexical names, while each re-entry still
creates a fresh lifetime for the declaration.

```c filename=automatic_block_reentry_lifetime_nested.c
int32 automatic_block_reentry_lifetime_nested() {
    int32 i;
    for (i = 0; i < 2; i++) {
        if (i < 2) {
            int32 a[1];
            if (i == 1) {
                return a[0];
            }
            a[0] = 5;
        }
    }
    return 0;
}
```

```click
verifying "automatic_block_reentry_lifetime_nested.c";

int32 automatic_block_reentry_lifetime_nested() {
    ensures result == 5;
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
