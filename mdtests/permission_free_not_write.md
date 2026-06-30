# free permission does not grant write access

This checks that `free(...)` is separate from `write(...)`. Permission to free a
range does not by itself permit stores to that range.

```c filename=write_with_free_only.c
int32 write_with_free_only(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```click
verifying "write_with_free_only.c";

int32 write_with_free_only(int32 p[]) {
    requires free(p[0..1]);

    ensures free(p[0..1]) by auto;
}
```

```expect
fail: MissingResource
```
