# decimal negative literals retain their C type before unary minus

```c filename=t.c
int32 t() {
    return -2147483648 < 0u;
}
```

```click
verifying "t.c";

int32 t() {
    ensures result == 0;
}
```

```expect
fail: unclosed goal
```
