# Unary plus and comma-separated `for` initializers

Unary `+` is a no-op scalar operator, and scalar assignments in a `for`
initializer execute left to right. Multiple declaration declarators remain
outside this C0 slice.

```c filename=unary_plus_for_init.c
int32 unary_plus_for_init() {
    int32 i;
    int32 j;
    for (i = +0, j = +3; i < 3; i++) {
        j = j + 1;
    }
    return j;
}
```

```click
verifying "unary_plus_for_init.c";

int32 unary_plus_for_init() {
    ensures result == 6 by auto;
}
```

```expect
pass
```
