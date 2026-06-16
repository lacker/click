# pointer range verification

This checks that `valid_range(p, 8)` is enough to prove one indexed `int32`
store and a matching indexed load.

```c filename=pointer_range.c
int32 write_second(int32* p) {
    p[1] = 9;
    return p[1];
}
```

```click
verifying "pointer_range.c";

int32 write_second(int32* p) {
    requires valid_range(p, 8);
    ensures writes_and_reads_second_cell: result == 9 by auto;
}
```

```expect
pass
```
