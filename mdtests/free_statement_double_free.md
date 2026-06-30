# double free fails

This checks that `free(p);` consumes the free permission, so a second free of
the same range is rejected.

```c filename=double_free.c
int32 double_free(int32 p[]) {
    free(p);
    free(p);
    return 0;
}
```

```click
verifying "double_free.c";

int32 double_free(int32 p[]) {
    requires free(p[0..1]);

    ensures returns_zero: result == 0 by auto;
}
```

```expect
fail: missing resource `free(p[0..1])`
```
