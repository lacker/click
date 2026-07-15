# pointer range verification

This checks a one-cell write permission plus `loadable(p, 8)` for one
indexed `int32` store and a matching indexed load.

```c filename=pointer_range.c
int32 write_second(int32* p) {
    p[1] = 9;
    return p[1];
}
```

```click
verifying "pointer_range.c";

int32 write_second(int32* p) {
    requires loadable(p, 8);
    consumes p[1..2];
    ensures writes_and_reads_second_cell: result == 9 by auto;
}
```

```expect
pass
```
