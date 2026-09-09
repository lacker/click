# sizeof uses the modeled LP64 size_t type

```c filename=t.c
int32 sizeof_cmp() {
    return sizeof(int32) - 5 < 0;
}
```

```click
verifying "t.c";

int32 sizeof_cmp() {
    ensures result == 1;
}
```

```expect
fail: unclosed goal
```
