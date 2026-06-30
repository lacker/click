# write after free fails

This checks that `free(p);` removes overlapping access permissions, so a later
store to the same range is rejected.

```c filename=write_after_free.c
int32 write_after_free(int32 p[]) {
    free(p);
    p[0] = 1;
    return p[0];
}
```

```click
verifying "write_after_free.c";

int32 write_after_free(int32 p[]) {
    requires write(p[0..1]);
    requires free(p[0..1]);

    ensures returns_written: result == 1 by auto;
}
```

```expect
fail: missing resource `write(p[0..1])`
```
