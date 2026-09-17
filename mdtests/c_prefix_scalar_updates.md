# Prefix scalar updates

Prefix increment and decrement are accepted as statement-only scalar update
sugar, including in a `for` step.

```c filename=prefix_scalar_updates.c
int32 prefix_scalar_updates() {
    int32 i = 0;
    ++i;
    --i;
    for (; i < 3; ++i) {
    }
    return i;
}
```

```click
verifying "prefix_scalar_updates.c";

int32 prefix_scalar_updates() {
    ensures result == 3 by auto;
}
```

```expect
pass
```
