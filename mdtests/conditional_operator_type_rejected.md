# conditional arithmetic operands use their common C type

```c filename=t.c
int32 cond_type_cmp() {
    return (1 ? -1 : 1u) < 0;
}
```

```click
verifying "t.c";

int32 cond_type_cmp() {
    ensures result == 1;
}
```

```expect
fail: unclosed goal
```
