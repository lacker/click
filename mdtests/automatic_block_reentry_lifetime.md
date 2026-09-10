# automatic block re-entry starts a fresh lifetime

An automatic object declared in a loop body is a new object on every block
entry. A value written during an earlier iteration must not initialize the
later lifetime.

```c filename=automatic_block_reentry_lifetime.c
int32 automatic_block_reentry_lifetime() {
    int32 i;
    for (i = 0; i < 2; i++) {
        int32 a[2];
        if (i == 1) {
            return a[0];
        }
        a[0] = 5;
    }
    return 0;
}
```

```click
verifying "automatic_block_reentry_lifetime.c";

int32 automatic_block_reentry_lifetime() {
    ensures result == 5;
}
```

```expect
fail: undefined behavior: read of uninitialized storage
```
