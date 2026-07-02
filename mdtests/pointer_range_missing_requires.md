# pointer range verification rejects missing requirements

This checks that an indexed pointer load without a `read(...)` requirement
reports a missing resource.

```c filename=pointer_range_missing_requires.c
int32 read_second(int32* p) {
    return p[1];
}
```

```click
verifying "pointer_range_missing_requires.c";

int32 read_second(int32* p) {
    ensures reads_second_cell: result == p[1] by auto;
}
```

```expect
fail: missing resource `read(p[1..2])`
```
