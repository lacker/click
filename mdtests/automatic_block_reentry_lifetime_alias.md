# aliases cannot cross automatic block re-entry lifetimes

An alias retained from an earlier loop-body declaration points to an ended
automatic object after the body is re-entered.

```c filename=automatic_block_reentry_lifetime_alias.c
int32 automatic_block_reentry_lifetime_alias() {
    int32 i;
    int32* p;
    for (i = 0; i < 2; i++) {
        int32 a[1];
        if (i == 0) {
            p = &a[0];
        } else {
            return *p;
        }
        a[0] = 5;
    }
    return 0;
}
```

```click
verifying "automatic_block_reentry_lifetime_alias.c";

int32 automatic_block_reentry_lifetime_alias() {
    ensures result == 5;
}
```

```expect
fail: undefined behavior: invalid memory access
```
