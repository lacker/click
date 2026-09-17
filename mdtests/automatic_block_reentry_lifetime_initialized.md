# automatic block re-entry accepts per-entry initialization

An automatic object declared in a loop body may be used after re-entry when
the current lifetime is initialized on that entry.

```c filename=automatic_block_reentry_lifetime_initialized.c
int32 automatic_block_reentry_lifetime_initialized() {
    int32 i;
    for (i = 0; i < 2; i++) {
        int32 a[1];
        a[0] = i;
        if (i == 1) {
            return a[0];
        }
    }
    return 0;
}
```

```click
verifying "automatic_block_reentry_lifetime_initialized.c";

int32 automatic_block_reentry_lifetime_initialized() {
    ensures result == 1;
}
```

```expect
pass
```
